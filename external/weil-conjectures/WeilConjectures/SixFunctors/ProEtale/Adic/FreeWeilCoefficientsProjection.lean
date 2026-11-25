/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.Sites.SheafAdjunctionUnitProjection
public import WeilConjectures.SixFunctors.ProEtale.Adic.FreeWeilCoefficients

/-!
# The projection formula for sheafified free modules

Let `R` be a commutative ring, `F` the sheafified free `R`-module functor from abelian sheaves to
sheaves of `R`-modules (`CategoryTheory.Sheaf.extendScalarsAb`) and `U` the lax monoidal
forgetful functor. For a sheaf of `R`-modules `P` and an abelian sheaf `Z`, the map
```
U P ⊗ Z ⟶ U P ⊗ U (F Z) ⟶ U (P ⊗ F Z)
```
is an isomorphism (`CategoryTheory.Sheaf.isIso_extendScalarsAbProjection`): on presheaves this
is the isomorphism `M ⊗[ℤ] Z ≅ M ⊗[R] (R ⊗[ℤ] Z)`, and the general case follows by
sheafification.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal TensorProduct

namespace ModuleCat

universe v

variable (R : Type v) [CommRing R]

/-- The projection formula for modules: `m ⊗ z ↦ m ⊗ (1 ⊗ z)` is an isomorphism
`M ⊗[ℤ] Z ≅ M ⊗[R] (R ⊗[ℤ] Z)`. -/
instance isIso_whiskerLeft_unit_comp_μ (M : ModuleCat.{v} R) (Z : Ab.{v}) :
    IsIso ((forget₂ (ModuleCat.{v} R) Ab.{v}).obj M ◁ (extendScalarsAbAdj R).unit.app Z ≫
      μ (forget₂ (ModuleCat.{v} R) Ab.{v}) M ((extendScalarsAb R).obj Z)) := by
  have : (forget₂ (ModuleCat.{v} R) Ab.{v}).obj M ◁ (extendScalarsAbAdj R).unit.app Z ≫
      μ (forget₂ (ModuleCat.{v} R) Ab.{v}) M ((extendScalarsAb R).obj Z) =
      (AlgebraTensorModule.cancelBaseChange ℤ R R M Z).symm.toAddEquiv.toAddCommGrpIso.hom :=
    AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)
  rw [this]
  infer_instance

/-- The forgetful functor from `R`-modules to abelian groups is a left adjoint: it is the
restriction of scalars along `ℤ ⟶ R`, followed by the equivalence between `ℤ`-modules and
abelian groups. -/
lemma isLeftAdjoint_forget₂Ab : (forget₂ (ModuleCat.{v} R) Ab.{v}).IsLeftAdjoint := by
  have : (ModuleCat.restrictScalars.{v} (algebraMap ℤ R)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, v} (algebraMap ℤ R)).isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso (F := ModuleCat.restrictScalars.{v} (algebraMap ℤ R) ⋙
    forget₂ (ModuleCat.{v} ℤ) Ab.{v}) (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl)

end ModuleCat

namespace CategoryTheory

namespace Sheaf

universe v

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (R : Type v) [CommRing R]
  [HasWeakSheafify J Ab.{v}] [(J.W (A := Ab.{v})).IsMonoidal]
  [HasWeakSheafify J (ModuleCat.{v} R)] [(J.W (A := ModuleCat.{v} R)).IsMonoidal]
  [J.HasSheafCompose (forget₂ (ModuleCat.{v} R) Ab.{v})]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The projection formula map `U P ⊗ Z ⟶ U P ⊗ U (F Z) ⟶ U (P ⊗ F Z)`, for the sheafified free
`R`-module functor `F` and the forgetful functor `U`. -/
noncomputable def extendScalarsAbProjection (P : Sheaf J (ModuleCat.{v} R))
    (Z : Sheaf J Ab.{v}) :
    (sheafCompose J (forget₂ (ModuleCat.{v} R) Ab.{v})).obj P ⊗ Z ⟶
      (sheafCompose J (forget₂ (ModuleCat.{v} R) Ab.{v})).obj
        (P ⊗ (extendScalarsAb J R).obj Z) :=
  _ ◁ (extendScalarsAbAdjunction J R).unit.app Z ≫ μ _ _ _

/-- The projection formula map, on underlying presheaves. -/
lemma μ_comp_sheafToPresheaf_map_extendScalarsAbProjection (P : Sheaf J (ModuleCat.{v} R))
    (Z : Sheaf J Ab.{v}) :
    μ (sheafToPresheaf J Ab.{v}) ((sheafCompose J (forget₂ (ModuleCat.{v} R) Ab.{v})).obj P) Z ≫
      (sheafToPresheaf J Ab.{v}).map (extendScalarsAbProjection J R P Z) =
      (P.obj ⋙ forget₂ _ _) ◁ ((ModuleCat.extendScalarsAbAdj R).whiskerRight Cᵒᵖ).unit.app Z.obj ≫
        μ ((Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) Ab.{v})) P.obj
          (Z.obj ⋙ ModuleCat.extendScalarsAb R) ≫
        Functor.whiskerRight (P.obj ◁ toSheafify J (Z.obj ⋙ ModuleCat.extendScalarsAb R))
          (forget₂ _ _) ≫
        Functor.whiskerRight (μ (sheafToPresheaf J _) P ((extendScalarsAb J R).obj Z))
          (forget₂ _ _) := by
  rw [extendScalarsAbProjection, Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_right_assoc]
  have h := μ_sheafToPresheaf_comp_map_μ_sheafCompose J (forget₂ (ModuleCat.{v} R) Ab.{v}) P
    ((extendScalarsAb J R).obj Z)
  simp only [Functor.comp_obj] at h ⊢
  rw [h, ObjectProperty.ι_map, Sheaf.adjunction_unit_app_hom]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  congr 1
  exact Functor.LaxMonoidal.μ_natural_right_assoc
    ((Functor.whiskeringRight Cᵒᵖ _ _).obj (forget₂ (ModuleCat.{v} R) Ab.{v})) P.obj
    (toSheafify J (Z.obj ⋙ ModuleCat.extendScalarsAb R)) _

/-- **The projection formula** for the sheafified free `R`-module functor `F`: the map
`U P ⊗ Z ⟶ U (P ⊗ F Z)` is an isomorphism. On presheaves this is the isomorphism
`M ⊗[ℤ] Z ≅ M ⊗[R] (R ⊗[ℤ] Z)`, the remaining maps becoming isomorphisms after
sheafification. -/
instance isIso_extendScalarsAbProjection (P : Sheaf J (ModuleCat.{v} R)) (Z : Sheaf J Ab.{v}) :
    IsIso (extendScalarsAbProjection J R P Z) := by
  have := ModuleCat.isLeftAdjoint_forget₂Ab R
  have : J.PreservesSheafification (forget₂ (ModuleCat.{v} R) Ab.{v}) :=
    Sheaf.preservesSheafification_of_adjunction J (Adjunction.ofIsLeftAdjoint _)
  rw [← J.W_sheafToPresheaf_map_iff_isIso]
  refine J.W.of_precomp _ _ (J.W_μ_sheafToPresheaf _ Z) ?_
  rw [μ_comp_sheafToPresheaf_map_extendScalarsAbProjection, ← Category.assoc]
  refine J.W.comp_mem _ _ (@MorphismProperty.of_isIso _ _ _ _ _ _ _ _ ?_) (J.W.comp_mem _ _ ?_ ?_)
  · rw [NatTrans.isIso_iff_isIso_app]
    intro U
    simp only [NatTrans.comp_app, Functor.LaxMonoidal.whiskeringRight_μ_app]
    exact ModuleCat.isIso_whiskerLeft_unit_comp_μ R (P.obj.obj U) (Z.obj.obj U)
  · exact J.W_of_preservesSheafification _ _
      (MorphismProperty.IsMonoidal.whiskerLeft _ _ (J.W_toSheafify _))
  · exact J.W_of_preservesSheafification _ _ (J.W_μ_sheafToPresheaf _ _)

end Sheaf

end CategoryTheory
