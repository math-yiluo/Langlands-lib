/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceSheaf

/-!
# The projection formula for the trace of a locally split cover

Let `g : Y ⟶ X` be weakly étale and pro-étale locally split into `d` sheets, and let
`F = j_g^* ⋙ g_*` be the endofunctor `G ↦ (V ↦ G(V ×_X Y))` of abelian sheaves on `X_proét`,
with unit `η : 𝟭 ⟶ F` and trace `T : F ⟶ 𝟭` (`AlgebraicGeometry.ProEtale.splitTrace`). The
functor `F` is lax monoidal, as a composite of pushforwards along continuous functors. This file
proves:

* `AlgebraicGeometry.ProEtale.splitTrace_projection`: the **projection formula** for the
  trace, `(η_P ▷ F Q) ≫ μ_F(P, Q) ≫ T_{P ⊗ Q} = P ◁ T_Q`. On sections, it says that
  `T(p|_{V ×_X Y} ⊗ q) = p ⊗ T(q)`; it is checked locally, where `T` is a sum of restrictions
  along sections of `V ×_X Y ⟶ V`;
* `AlgebraicGeometry.ProEtale.isMonoidal_upperStarIsoLocalizationRestriction`: the
  identification `g^* ≅ j_g^*` of the pullback along a weakly étale `g` with the restriction is
  a monoidal natural isomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

section Restriction

variable (h : WeaklyEtale g)

/-- The restriction along the localization functor is lax monoidal, being a pushforward along a
continuous functor. -/
noncomputable instance localizationRestriction_laxMonoidal :
    (localizationRestriction Ab.{u + 1} g h).LaxMonoidal :=
  inferInstanceAs ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).LaxMonoidal

/-- The tensor map of the restriction along the localization functor, on sections. -/
@[reassoc]
lemma μ_sheafToPresheaf_app_comp_μ_localizationRestriction_app
    (P Q : Sheaf (ProEt.topology X) Ab.{u + 1}) (U : Y.ProEtᵒᵖ) :
    (μ (sheafToPresheaf _ Ab.{u + 1}) ((localizationRestriction Ab.{u + 1} g h).obj P)
        ((localizationRestriction Ab.{u + 1} g h).obj Q)).app U ≫
      (μ (localizationRestriction Ab.{u + 1} g h) P Q).hom.app U =
    (μ (sheafToPresheaf _ Ab.{u + 1}) P Q).app ((MorphismProperty.Over.map ⊤ h).op.obj U) :=
  Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.map ⊤ h) Ab.{u + 1} _ _ P Q U

/-- The tensor map of the pushforward, on sections. -/
@[reassoc]
lemma μ_sheafToPresheaf_app_comp_μ_lowerStar_app_ab
    (P Q : Sheaf (ProEt.topology Y) Ab.{u + 1}) (U : X.ProEtᵒᵖ) :
    (μ (sheafToPresheaf _ Ab.{u + 1}) ((g)_*[Ab.{u + 1}].obj P)
        ((g)_*[Ab.{u + 1}].obj Q)).app U ≫
      (μ (g)_*[Ab.{u + 1}] P Q).hom.app U =
    (μ (sheafToPresheaf _ Ab.{u + 1}) P Q).app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.obj U) :=
  Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) Ab.{u + 1} _ _ P Q U

end Restriction

variable [WeaklyEtale g]

/-- The tensor map of `F = j_g^* ⋙ g_*`, on sections over `V`: the tensor map of the underlying
presheaves over `V ×_X Y`. -/
@[reassoc]
lemma μ_sheafToPresheaf_app_comp_μ_localizationRestriction_comp_lowerStar_app
    (P Q : Sheaf (ProEt.topology X) Ab.{u + 1}) (V : X.ProEt) :
    (μ (sheafToPresheaf _ Ab.{u + 1})
        ((localizationRestriction Ab.{u + 1} g inferInstance ⋙ (g)_*[Ab.{u + 1}]).obj P)
        ((localizationRestriction Ab.{u + 1} g inferInstance ⋙ (g)_*[Ab.{u + 1}]).obj Q)).app
          (op V) ≫
      (μ (localizationRestriction Ab.{u + 1} g inferInstance ⋙ (g)_*[Ab.{u + 1}]) P Q).hom.app
        (op V) =
    (μ (sheafToPresheaf _ Ab.{u + 1}) P Q).app (op ((traceBaseChange g).obj V)) := by
  rw [comp_μ]
  change _ ≫ (μ (g)_*[Ab.{u + 1}] _ _).hom.app _ ≫
    (μ (localizationRestriction Ab.{u + 1} g inferInstance) P Q).hom.app _ = _
  erw [μ_sheafToPresheaf_app_comp_μ_lowerStar_app_ab_assoc]
  exact μ_sheafToPresheaf_app_comp_μ_localizationRestriction_app g _ P Q _

/-- The tensor maps of the underlying presheaves of a tensor product of sheaves are natural. -/
@[reassoc]
lemma μ_sheafToPresheaf_app_comp_map {P Q : Sheaf (ProEt.topology X) Ab.{u + 1}}
    {W W' : X.ProEt} (k : W' ⟶ W) :
    (μ (sheafToPresheaf _ Ab.{u + 1}) P Q).app (op W) ≫ (P ⊗ Q).obj.map k.op =
      (P.obj.map k.op ⊗ₘ Q.obj.map k.op) ≫ (μ (sheafToPresheaf _ Ab.{u + 1}) P Q).app (op W') :=
  ((μ (sheafToPresheaf _ Ab.{u + 1}) P Q).naturality k.op).symm

variable {g} {d : ℕ} (hg : IsLocallySplit g d)

/-- The section-level projection formula: for `V : X.ProEt`, restricting `p ∈ P(V)` along the
projection `V ×_X Y ⟶ V`, tensoring with `q ∈ Q(V ×_X Y)` and taking the trace is `p ⊗ T(q)`. -/
lemma splitTraceApp_projection (P Q : Sheaf (ProEt.topology X) Ab.{u + 1}) (V : X.ProEt) :
    (P.obj.map (traceProj g V).op ▷ _) ≫
        (μ (sheafToPresheaf _ Ab.{u + 1}) P Q).app (op ((traceBaseChange g).obj V)) ≫
        splitTraceApp hg (P ⊗ Q) V =
      (_ ◁ splitTraceApp hg Q V) ≫ (μ (sheafToPresheaf _ Ab.{u + 1}) P Q).app (op V) := by
  refine (P ⊗ Q).property.hom_ext ⟨splitSieve g d V, hg V⟩ _ _ fun I ↦ ?_
  obtain ⟨D, -⟩ := I.hf
  have hs (j : D.J) : (D.s j ≫ (traceBaseChange g).map I.f) ≫ traceProj g V = I.f := by
    rw [Category.assoc, traceBaseChange_map_comp_traceProj, reassoc_of% (D.s_proj j)]
  simp only [Category.assoc]
  rw [splitTraceApp_comp hg (P ⊗ Q) I.f D, μ_sheafToPresheaf_app_comp_map_assoc,
    μ_sheafToPresheaf_app_comp_map, ← Category.assoc (_ ◁ _), whiskerLeft_comp_tensorHom,
    splitTraceApp_comp hg Q I.f D]
  simp only [TraceSplitting.trace, Preadditive.comp_sum, tensor_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    μ_sheafToPresheaf_app_comp_map, tensorHom_comp_tensorHom_assoc]
  congr 2
  conv_rhs => rw [← hs j]
  simp only [op_comp, Functor.map_comp, Category.assoc]

/-- **The projection formula for the trace** of a locally split cover: for abelian sheaves `P`
and `Q` on `X_proét`, `(η_P ▷ F Q) ≫ μ_F(P, Q) ≫ T_{P ⊗ Q} = P ◁ T_Q`, where `F = j_g^* ⋙ g_*`,
`η` is the unit of `j_g^* ⊣ g_*` and `T` the trace. -/
theorem splitTrace_projection (P Q : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).unit.app P ▷ _ ≫
        μ (localizationRestriction Ab.{u + 1} g inferInstance ⋙ (g)_*[Ab.{u + 1}]) P Q ≫
        (splitTrace hg Ab.{u + 1}).app (P ⊗ Q) =
      P ◁ (splitTrace hg Ab.{u + 1}).app Q := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← μ_natural_left_assoc]
  erw [← μ_natural_right]
  refine NatTrans.ext (funext fun V ↦ ?_)
  induction V using Opposite.rec with | op V => ?_
  simp only [NatTrans.comp_app, Monoidal.whiskerRight_app, Monoidal.whiskerLeft_app]
  have h₁ : ((sheafToPresheaf _ Ab.{u + 1}).map
      ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).unit.app P)).app
        (op V) = P.obj.map (traceProj g V).op :=
    localizationRestrictionLowerStarAdjunction_unit_app_hom_app_traceProj (g := g) Ab.{u + 1} P V
  have h₂ (G : Sheaf (ProEt.topology X) Ab.{u + 1}) :
      ((sheafToPresheaf _ Ab.{u + 1}).map ((splitTrace hg Ab.{u + 1}).app G)).app (op V) =
        splitTraceApp hg G V := rfl
  have h₃ : (μ (sheafToPresheaf _ Ab.{u + 1})
        ((localizationRestriction Ab.{u + 1} g inferInstance ⋙ (g)_*[Ab.{u + 1}]).obj P)
        ((localizationRestriction Ab.{u + 1} g inferInstance ⋙ (g)_*[Ab.{u + 1}]).obj Q)).app
          (op V) ≫ ((sheafToPresheaf _ Ab.{u + 1}).map
        (μ (localizationRestriction Ab.{u + 1} g inferInstance ⋙ (g)_*[Ab.{u + 1}]) P Q)).app
          (op V) =
      (μ (sheafToPresheaf _ Ab.{u + 1}) P Q).app (op ((traceBaseChange g).obj V)) :=
    μ_sheafToPresheaf_app_comp_μ_localizationRestriction_comp_lowerStar_app g P Q V
  rw [h₁, h₂, h₂]
  refine Eq.trans ?_ (splitTraceApp_projection hg P Q V)
  rw [← h₃, Category.assoc]
  rfl

section Monoidal

variable (g)

/-- The unit of `j_g^* ⊣ g_*` restricts sections along the projection `V ×_X Y ⟶ V`. -/
lemma localizationRestrictionLowerStarAdjunction_unit_app_app
    (P : Sheaf (ProEt.topology X) Ab.{u + 1}) (U : X.ProEtᵒᵖ) :
    ((sheafToPresheaf _ Ab.{u + 1}).map
      ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).unit.app P)).app
        U = P.obj.map
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial).counit.app
        U.unop).op := by
  simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
    Adjunction.whiskerLeft]

/-- The unit of `j_g^* ⊣ g_*` is compatible with the tensor maps of `j_g^*` and `g_*`. -/
lemma localizationRestrictionLowerStarAdjunction_unit_tensor
    (P Q : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).unit.app (P ⊗ Q) =
      ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).unit.app P ⊗ₘ
        (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).unit.app Q) ≫
      μ (g)_*[Ab.{u + 1}] _ _ ≫
      (g)_*[Ab.{u + 1}].map (μ (localizationRestriction Ab.{u + 1} g inferInstance) P Q) := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, ← μ_natural_assoc]
  ext U : 2
  simp only [NatTrans.comp_app, Functor.map_comp, Monoidal.tensorHom_app,
    localizationRestrictionLowerStarAdjunction_unit_app_app]
  erw [← (μ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}) P Q).naturality]
  erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc]
  erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g))]
  rfl

/-- The unit of `j_g^* ⊣ g_*` at the tensor unit is given by the unit maps of `j_g^*` and
`g_*`. -/
lemma localizationRestrictionLowerStarAdjunction_unit_unit :
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).unit.app (𝟙_ _) =
      ε (g)_*[Ab.{u + 1}] ≫
      (g)_*[Ab.{u + 1}].map (ε (localizationRestriction Ab.{u + 1} g inferInstance)) := by
  apply Sheaf.hom_ext_of_ε_comp
  ext U : 2
  simp only [NatTrans.comp_app, Functor.map_comp,
    localizationRestrictionLowerStarAdjunction_unit_app_app]
  erw [← (ε (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})).naturality]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g))]
  erw [Monoidal.tensorUnit_map, Category.id_comp]
  rfl

/-- The identification `g^* ≅ j_g^*` of the pullback along a weakly étale `g` with the
restriction along the localization functor is monoidal. -/
instance isMonoidal_upperStarIsoLocalizationRestriction :
    NatTrans.IsMonoidal (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).hom where
  unit := by
    rw [← cancel_epi (Functor.OplaxMonoidal.η (g)^*[Ab.{u + 1}])]
    simp only [Functor.Monoidal.η_ε_assoc]
    apply ((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).injective
    dsimp only [upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_app_unit_comp_map_η]
    exact localizationRestrictionLowerStarAdjunction_unit_unit g
  tensor P Q := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (g)^*[Ab.{u + 1}] P Q)]
    simp only [Functor.Monoidal.δ_μ_assoc]
    apply ((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).injective
    dsimp only [upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_app_tensor_comp_map_δ, Category.assoc,
      ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc, Adjunction.unit_leftAdjointUniq_hom_app,
      Adjunction.unit_leftAdjointUniq_hom_app]
    exact localizationRestrictionLowerStarAdjunction_unit_tensor g P Q

end Monoidal

end AlgebraicGeometry.ProEtale
