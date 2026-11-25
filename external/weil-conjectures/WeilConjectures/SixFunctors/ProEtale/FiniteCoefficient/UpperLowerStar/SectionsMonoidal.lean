/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso

/-!
# Global sections of pro-étale sheaves are lax monoidal

The sections functor `G ↦ G(U)` on sheaves of `ℚ̄_ℓ`-modules on a small pro-étale site is lax
monoidal, as the composite of the lax monoidal inclusion of sheaves into presheaves and the
evaluation at `U`, which is strictly monoidal for the pointwise tensor product of presheaves.
The global sections functor `Γ` gets the transported structure along
`Γ ≅ (G ↦ G(X))`. With these structures, the identifications `Γ(W, g_* G) ≅ Γ(Z, G)` and
`Γ(Z, e^* G) ≅ Γ(W, G)` of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections` are monoidal
natural isomorphisms.

## Main results

- `AlgebraicGeometry.ProEtale.laxMonoidal_Γ`: the global sections functor is lax monoidal.
- `AlgebraicGeometry.ProEtale.isMonoidal_globalSectionsLowerStarIso_hom` and
  `AlgebraicGeometry.ProEtale.isMonoidal_globalSectionsUpperStarIso_hom`: the global sections of
  pushforwards and of pullbacks along isomorphisms are identified monoidally.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Opposite Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation at an object is a strictly monoidal functor on the pointwise monoidal functor
category. -/
@[simps!]
instance Functor.Monoidal.evaluation {C : Type*} [Category* C]
    (E : Type*) [Category* E] [MonoidalCategory E] (X : C) :
    ((evaluation C E).obj X).Monoidal :=
  CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

end CategoryTheory

namespace AlgebraicGeometry.ProEtale
variable {l : ℕ} [Fact l.Prime]

/-- The sections functor over an object of the pro-étale site is lax monoidal. -/
noncomputable instance laxMonoidal_sheafSections (X : Scheme.{u}) (U : X.ProEtᵒᵖ) :
    ((sheafSections (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).obj U).LaxMonoidal :=
  inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj U).LaxMonoidal

/-- The global sections functor is lax monoidal, through the identification of global sections
with the sections over the terminal object. -/
noncomputable instance laxMonoidal_Γ (X : Scheme.{u}) :
    (Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).LaxMonoidal :=
  Functor.LaxMonoidal.transport
    (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).symm

instance isMonoidal_ΓNatIsoSheafSections_inv (X : Scheme.{u}) :
    NatTrans.IsMonoidal (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId X)).inv :=
  Functor.LaxMonoidal.natTransIsMonoidal_of_transport
    (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).symm

instance isMonoidal_ΓNatIsoSheafSections_hom (X : Scheme.{u}) :
    NatTrans.IsMonoidal (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId X)).hom :=
  have : NatTrans.IsMonoidal (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId X)).symm.hom :=
    isMonoidal_ΓNatIsoSheafSections_inv X
  inferInstanceAs (NatTrans.IsMonoidal (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId X)).symm.inv)

lemma ε_sheafSections (X : Scheme.{u}) (U : X.ProEtᵒᵖ) :
    ε ((sheafSections (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).obj U) =
      (ε (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))).app U := by
  change ε (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj U) = _
  rw [Functor.LaxMonoidal.comp_ε]
  exact Category.id_comp _

lemma μ_sheafSections (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (F G : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    μ ((sheafSections (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).obj U) F G =
      (μ (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) F G).app U := by
  change μ (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj U) F G = _
  rw [Functor.LaxMonoidal.comp_μ]
  exact Category.id_comp _

/-- Restriction of sections along a morphism of the pro-étale site is monoidal. -/
instance isMonoidal_sheafSections_map {X : Scheme.{u}} {U V : X.ProEtᵒᵖ} (f : U ⟶ V) :
    NatTrans.IsMonoidal ((sheafSections (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).map
      f) where
  unit := by
    rw [ε_sheafSections, ε_sheafSections]
    simpa using ((ε (sheafToPresheaf (Scheme.ProEt.topology X)
      (WeilCoefficients.{u} l))).naturality f).symm
  tensor F G := by
    rw [μ_sheafSections, μ_sheafSections]
    simpa using ((μ (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) F
      G).naturality f).symm

lemma ε_Γ (X : Scheme.{u}) :
    ε (Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) =
      (ε (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))).app
          (op (Scheme.ProEt.mk (𝟙 X))) ≫
        (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).inv.app (𝟙_ _) := by
  rw [← ε_sheafSections]
  rfl

lemma μ_Γ (X : Scheme.{u}) (F G : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    μ (Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) F G =
      ((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).hom.app F ⊗ₘ
          (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).hom.app G) ≫
        (μ (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) F G).app
          (op (Scheme.ProEt.mk (𝟙 X))) ≫
        (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).inv.app (F ⊗ G) := by
  rw [← μ_sheafSections]
  rfl

variable {Z W : Scheme.{u}} (g : Z ⟶ W)

/-- The unit of the lax monoidal pushforward `g_*`, on sections over `V`, is the unit of the
sheaves on the base change of `V`. -/
@[reassoc]
lemma ε_sheafToPresheaf_app_comp_ε_lowerStar_app (V : W.ProEtᵒᵖ) :
    (ε (sheafToPresheaf (Scheme.ProEt.topology W) (WeilCoefficients.{u} l))).app V ≫
        (ε (g)_*[WeilCoefficients.{u} l]).hom.app V =
      (ε (sheafToPresheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l))).app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) :=
  Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (WeilCoefficients.{u} l)
    (Scheme.ProEt.topology W) (Scheme.ProEt.topology Z) V

/-- The tensor comparison of the lax monoidal pushforward `g_*`, on sections over `V`, is that
of the sheaves on the base change of `V`. -/
@[reassoc]
lemma μ_sheafToPresheaf_app_comp_μ_lowerStar_app (V : W.ProEtᵒᵖ)
    (F G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    (μ (sheafToPresheaf (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)) ((g)_*[_].obj F)
        ((g)_*[_].obj G)).app V ≫ (μ (g)_*[WeilCoefficients.{u} l] F G).hom.app V =
      (μ (sheafToPresheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) F G).app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) := by
  have h := NatTrans.IsMonoidal.tensor
    (τ := (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (WeilCoefficients.{u} l)
      (Scheme.ProEt.topology W) (Scheme.ProEt.topology Z)).hom) F G
  simp only [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    Functor.LaxMonoidal.comp_μ, tensorHom_id, id_whiskerRight, Category.id_comp,
    Category.comp_id] at h
  exact (congr_app h V).symm

lemma μ_sheafToPresheaf_comp_map_μ_lowerStar_app (V : W.ProEtᵒᵖ)
    (F G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    (μ (sheafToPresheaf (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)) ((g)_*[_].obj F)
        ((g)_*[_].obj G) ≫ (sheafToPresheaf _ _).map (μ (g)_*[WeilCoefficients.{u} l] F G)).app V =
      (μ (sheafToPresheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) F G).app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) :=
  μ_sheafToPresheaf_app_comp_μ_lowerStar_app g V F G

lemma globalSectionsLowerStarIso_hom_app
    (G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g).hom.app G =
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId W)).hom.app ((g)_*[_].obj G) ≫
        G.obj.map (overPullbackObjMkIdIso g).inv.op ≫
          (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId Z)).inv.app G := by
  simp [globalSectionsLowerStarIso]

/-- The identification `Γ(W, g_* G) ≅ Γ(Z, G)` is monoidal. -/
instance isMonoidal_globalSectionsLowerStarIso_hom :
    NatTrans.IsMonoidal (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g).hom where
  unit := by
    rw [globalSectionsLowerStarIso_hom_app, Functor.LaxMonoidal.comp_ε, ε_Γ, ε_Γ]
    simp only [Category.assoc]
    rw [NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc, Functor.flip_obj_map]
    erw [ε_sheafToPresheaf_app_comp_ε_lowerStar_app_assoc]
    erw [← (ε (sheafToPresheaf (Scheme.ProEt.topology Z)
      (WeilCoefficients.{u} l))).naturality_assoc]
    exact Category.id_comp _
  tensor F G := by
    rw [globalSectionsLowerStarIso_hom_app, globalSectionsLowerStarIso_hom_app,
      globalSectionsLowerStarIso_hom_app, Functor.LaxMonoidal.comp_μ, μ_Γ, μ_Γ]
    simp only [Category.assoc]
    rw [NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc, Functor.flip_obj_map,
      ← NatTrans.comp_app_assoc, μ_sheafToPresheaf_comp_map_μ_lowerStar_app]
    erw [← (μ (sheafToPresheaf (Scheme.ProEt.topology Z)
      (WeilCoefficients.{u} l)) F G).naturality_assoc]
    simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.inv_hom_id_app,
      Monoidal.tensorObj_map]
    erw [Category.comp_id, Category.comp_id, ← tensorHom_comp_tensorHom_assoc]

/-- The identification `Γ(Z, e^* G) ≅ Γ(W, G)` for an isomorphism `e : Z ≅ W` is monoidal. -/
instance isMonoidal_globalSectionsUpperStarIso_hom (e : Z ≅ W) :
    NatTrans.IsMonoidal (globalSectionsUpperStarIso (WeilCoefficients.{u} l) e).hom := by
  dsimp only [globalSectionsUpperStarIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance

end AlgebraicGeometry.ProEtale
