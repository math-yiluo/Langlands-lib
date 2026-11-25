/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # The ordinary pullback/tensor comparison on representatives

Let `F : C ⥤ D` be an exact strong monoidal functor between monoidal Grothendieck abelian
categories with functorial flat resolutions, which preserves flat objects and is a left adjoint.
On objects `Q P`, `Q T` of the derived category, the tensor comparison
`D(F)(K ⊗ᴸ M) ⟶ D(F) K ⊗ᴸ D(F) M` of `CategoryTheory.Functor.mapDerivedCategoryTensorComparison`
is induced by the inverse tensorator `F(P ⊗ T) ≅ F P ⊗ F T` of complexes
(`CategoryTheory.Functor.projection_mapDerivedCategoryTensorComparison_app_app_Q_comp`).

This is the normalization used to compare the native tensor square after localization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

namespace CategoryTheory.Functor

/-- The uncurried tensor and the tensor bifunctor have the same components. -/
def projection_uncurryTensorIso (E : Type*) [Category* E] [MonoidalCategory E] :
    uncurry.obj (curriedTensor E) ≅ MonoidalCategory.tensor E :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun fg ↦ by
    dsimp
    rw [Category.comp_id, Category.id_comp, tensorHom_def])

@[simp]
lemma projection_uncurryTensorIso_hom_app (E : Type*) [Category* E] [MonoidalCategory E]
    (MN : E × E) : (projection_uncurryTensorIso E).hom.app MN = 𝟙 _ := rfl

section Abstract

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

omit [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] in
/-- The tensorator of the localization functor `Q` is the one of `Qh`. -/
private lemma projection_μ_Q_eq_μ_Qh (P T : CochainComplex C ℤ) : LaxMonoidal.μ Q P T =
    LaxMonoidal.μ Qh ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj T) := by
  have : LaxMonoidal.μ Q P T =
      ((quotientCompQhIso C).inv.app P ⊗ₘ (quotientCompQhIso C).inv.app T) ≫
        LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ) ⋙ Qh) P T ≫
          (quotientCompQhIso C).hom.app (P ⊗ T) := rfl
  rw [this, LaxMonoidal.comp_μ]
  erw [Functor.map_id, Category.comp_id, Category.comp_id, id_tensorHom_id, Category.id_comp]

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [HasFunctorialFlatResolution D]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] in
/-- On complexes, the factorization isomorphism of `D(F)` through the homotopy category is
the one through cochain complexes. -/
private lemma projection_mapDerivedCategoryFactorsh_hom_app_quotient_obj (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [mapDerivedCategoryFactorsh_hom_app]
  erw [Functor.map_id, Category.id_comp, Category.id_comp, Functor.map_id, Category.comp_id]

/-- On objects `Q P`, `Q T`, the tensor comparison of `D(F)` is induced by the inverse
tensorator `F(P ⊗ T) ≅ F P ⊗ F T` of complexes:
```
  D(F)(Q P ⊗ᴸ Q T) ──comparison──▶ D(F)(Q P) ⊗ᴸ D(F)(Q T)
          │                                    │
          ▼                                    ▼
   Q(F(P ⊗ T)) ──────────Q(μ⁻¹)───────▶ Q(F P ⊗ F T)
``` -/
lemma projection_mapDerivedCategoryTensorComparison_app_app_Q_comp (P T : CochainComplex C ℤ) :
    (F.mapDerivedCategoryTensorComparison.app (Q.obj P)).app (Q.obj T) ≫
      (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
        LaxMonoidal.μ Q ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj T) =
      F.mapDerivedCategory.map (LaxMonoidal.μ Q P T) ≫
        F.mapDerivedCategoryFactors.hom.app (P ⊗ T) ≫
          Q.map (F.mapCochainComplexμIso P T).inv := by
  have h := F.mapDerivedCategoryTensorComparison_app_app_comp
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj T)
  rw [projection_mapDerivedCategoryFactorsh_hom_app_quotient_obj,
    projection_mapDerivedCategoryFactorsh_hom_app_quotient_obj] at h
  erw [projection_mapDerivedCategoryFactorsh_hom_app_quotient_obj] at h
  rw [projection_μ_Q_eq_μ_Qh, projection_μ_Q_eq_μ_Qh]
  exact h

/-- Naturality of the tensor comparison of `D(F)` in both variables. -/
@[reassoc]
lemma projection_mapDerivedCategoryTensorComparison_naturality {X X' Y Y' : DerivedCategory C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    F.mapDerivedCategory.map (f ⊗ₘ g) ≫ (F.mapDerivedCategoryTensorComparison.app X').app Y' =
      (F.mapDerivedCategoryTensorComparison.app X).app Y ≫
        (F.mapDerivedCategory.map f ⊗ₘ F.mapDerivedCategory.map g) := by
  let := F.mapDerivedCategoryOplaxMonoidal
  exact (OplaxMonoidal.δ_natural F.mapDerivedCategory f g).symm

/-- The tensor comparison of `D(F)` on arbitrary objects with chosen maps to localized
complexes: it is the localization of the inverse tensorator of complexes. -/
lemma projection_mapDerivedCategoryTensorComparison_total_model (X Y : DerivedCategory C)
    (P T : CochainComplex C ℤ) (f : X ⟶ Q.obj P) (g : Y ⟶ Q.obj T) :
    (F.mapDerivedCategoryTensorComparison.app X).app Y ≫
      ((F.mapDerivedCategory.map f ≫ F.mapDerivedCategoryFactors.hom.app P) ⊗ₘ
        (F.mapDerivedCategory.map g ≫ F.mapDerivedCategoryFactors.hom.app T)) ≫
        LaxMonoidal.μ Q ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj T) =
      F.mapDerivedCategory.map ((f ⊗ₘ g) ≫ LaxMonoidal.μ Q P T) ≫
        F.mapDerivedCategoryFactors.hom.app (P ⊗ T) ≫
          Q.map (F.mapCochainComplexμIso P T).inv := by
  rw [← tensorHom_comp_tensorHom, Category.assoc,
    ← projection_mapDerivedCategoryTensorComparison_naturality_assoc,
    projection_mapDerivedCategoryTensorComparison_app_app_Q_comp, Functor.map_comp, Category.assoc]

end Abstract

end CategoryTheory.Functor
