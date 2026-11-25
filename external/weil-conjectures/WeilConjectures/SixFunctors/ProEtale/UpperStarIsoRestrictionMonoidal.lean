/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.PushforwardNatTransMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# The pullback along a weakly étale morphism is restriction, monoidally

For a weakly étale `g : Y ⟶ X`, the pullback `g^*` of pro-étale sheaves is computed by restriction
along the localization functor (`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`).
Both functors are monoidal: `g^*` is strong monoidal
(`AlgebraicGeometry.ProEtale.monoidal_upperStar`),
and the restriction is the pushforward along a continuous functor of sites, hence lax monoidal.
This file proves that the comparison isomorphism is monoidal
(`AlgebraicGeometry.ProEtale.isMonoidal_upperStarIsoLocalizationRestriction_hom`).

The proof transposes along the monoidal adjunction `g^* ⊣ g_*`: the claim becomes the
monoidality of the unit `𝟭 ⟶ g_* ∘ j_g^*` of the restriction adjunction
(`AlgebraicGeometry.ProEtale.isMonoidal_localizationRestrictionLowerStarAdjunction_unit`), which is
the restriction along the projections `V ×_X Y ⟶ V`, monoidal by
`CategoryTheory.Functor.isMonoidal_sheafPushforwardContinuousNatTrans`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]
  {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]
  [((Scheme.ProEt.topology X).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology Y).W (A := A)).IsMonoidal]


/-- The restriction along the localization functor is lax monoidal, being a pushforward along a
continuous functor of sites. -/
noncomputable instance laxMonoidal_localizationRestriction :
    (localizationRestriction A g inferInstance).LaxMonoidal := by
  unfold localizationRestriction
  infer_instance

instance isContinuous_overPullback' :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) :=
  Scheme.ProEt.isContinuous_overPullback g

instance isContinuous_overMap' :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).IsContinuous
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overMap _

instance isContinuous_overPullback_comp_overMap :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙
      MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) :=
  Functor.isContinuous_comp (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g)
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)) (Scheme.ProEt.topology X)
    (Scheme.ProEt.topology Y)
    (Scheme.ProEt.topology X)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [BraidedCategory A]
  [((Scheme.ProEt.topology X).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology Y).W (A := A)).IsMonoidal] in
/-- The unit of the adjunction `j_g^* ⊣ g_*` is the identification `𝟭 ≅ 𝟭_*`, followed by
restriction along the projections `V ×_X Y ⟶ V` and the composition isomorphism of
pushforwards. -/
lemma localizationRestrictionLowerStarAdjunction_unit_eq :
    (localizationRestrictionLowerStarAdjunction A g inferInstance).unit =
      (Functor.sheafPushforwardContinuousId' (Iso.refl (𝟭 X.ProEt)) A
          (Scheme.ProEt.topology X)).inv ≫
        Functor.sheafPushforwardContinuousNatTrans
          (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial).counit
          A (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) ≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙
            MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g))) A
          (Scheme.ProEt.topology X)
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).inv := by
  refine NatTrans.ext (funext fun H ↦ Sheaf.hom_ext ?_)
  ext U : 2
  simp only [localizationRestrictionLowerStarAdjunction,
    Adjunction.sheafPushforwardContinuous_unit_app_hom_app, Functor.id_obj, Functor.comp_obj,
    NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, Functor.sheafPushforwardContinuousNatTrans_app_hom,
    ObjectProperty.ι_obj, Functor.sheafPushforwardContinuousId'_inv_app_hom_app,
    Opposite.op_unop, Iso.refl_hom, NatTrans.id_app, op_id, CategoryTheory.Functor.map_id,
    Functor.whiskerRight_app, Functor.op_obj, NatTrans.op_app,
    MorphismProperty.Over.mapPullbackAdj_counit_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, id_comp]
  erw [Category.comp_id]

/-- The unit of the adjunction `j_g^* ⊣ g_*` is monoidal. -/
instance isMonoidal_localizationRestrictionLowerStarAdjunction_unit :
    NatTrans.IsMonoidal (localizationRestrictionLowerStarAdjunction A g inferInstance).unit := by
  rw [localizationRestrictionLowerStarAdjunction_unit_eq]
  infer_instance


omit [MonoidalCategory A] [BraidedCategory A] [((Scheme.ProEt.topology X).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology Y).W (A := A)).IsMonoidal] in
/-- The unit of `g^* ⊣ g_*` followed by the comparison `g^* ≅ j_g^*` is the unit of
`j_g^* ⊣ g_*`. -/
@[reassoc]
lemma unit_app_comp_map_upperStarIsoLocalizationRestriction_hom_app
    (H : Sheaf (Scheme.ProEt.topology X) A) :
    (upperStarLowerStarAdjunction A g).unit.app H ≫
      (g)_*[A].map ((upperStarIsoLocalizationRestriction A g inferInstance).hom.app H) =
      (localizationRestrictionLowerStarAdjunction A g inferInstance).unit.app H :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ H

variable [∀ M : A, Limits.PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

/-- **The comparison `g^* ≅ j_g^*` is monoidal**, for the strong monoidal structure of the
pullback and the lax monoidal structure of the restriction along the localization functor. -/
instance isMonoidal_upperStarIsoLocalizationRestriction_hom :
    NatTrans.IsMonoidal (upperStarIsoLocalizationRestriction A g inferInstance).hom where
  unit := by
    rw [← cancel_epi (η (g)^*[A]), Functor.Monoidal.η_ε_assoc]
    apply ((upperStarLowerStarAdjunction A g).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [unit_app_comp_map_upperStarIsoLocalizationRestriction_hom_app,
      Adjunction.unit_app_unit_comp_map_η_assoc,
      ← Functor.LaxMonoidal.comp_ε, ← NatTrans.IsMonoidal.unit
        (τ := (localizationRestrictionLowerStarAdjunction A g inferInstance).unit)]
    exact (id_comp _).symm
  tensor P Q := by
    rw [← cancel_epi (δ (g)^*[A] P Q), Functor.Monoidal.δ_μ_assoc]
    apply ((upperStarLowerStarAdjunction A g).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [unit_app_comp_map_upperStarIsoLocalizationRestriction_hom_app,
      Adjunction.unit_app_tensor_comp_map_δ_assoc, ← Functor.LaxMonoidal.μ_natural_assoc,
      tensorHom_comp_tensorHom_assoc, unit_app_comp_map_upperStarIsoLocalizationRestriction_hom_app,
      unit_app_comp_map_upperStarIsoLocalizationRestriction_hom_app,
      ← Functor.LaxMonoidal.comp_μ, ← NatTrans.IsMonoidal.tensor
        (τ := (localizationRestrictionLowerStarAdjunction A g inferInstance).unit)]
    exact (id_comp _).symm

end AlgebraicGeometry.ProEtale
