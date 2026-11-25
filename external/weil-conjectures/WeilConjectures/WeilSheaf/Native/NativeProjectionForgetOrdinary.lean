/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.WeilSheaf.Native.NativePullDerivedTensorKFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Braided
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # The ordinary pullback/tensor comparison on representatives

Let `F : C ⥤ D` be an exact strong monoidal functor between monoidal Grothendieck abelian
categories with functorial flat resolutions, which preserves flat objects and is a left adjoint.
On objects `Q P`, `Q T` of the derived category, the tensor comparison
`D(F)(K ⊗ᴸ M) ⟶ D(F) K ⊗ᴸ D(F) M` of `CategoryTheory.Functor.mapDerivedCategoryTensorComparison`
is induced by the inverse tensorator `F(P ⊗ T) ≅ F P ⊗ F T` of complexes
(`CategoryTheory.Functor.mapDerivedCategoryTensorComparison_app_app_Q_comp`).

We apply this to the pullback `f^*ᵃ[l]` of `ℓ`-adic sheaves along an arbitrary morphism of
schemes: it preserves flat objects (`AlgebraicGeometry.ProEtale.adicUpperStar_preservesFlat`),
since it preserves K-flat complexes. This is the ordinary side of the comparison of the native
and the ordinary pullback/tensor comparisons (blueprint: fix-prop-projection-formula).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

namespace CategoryTheory.Functor

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
private lemma μ_Q_eq_μ_Qh (P T : CochainComplex C ℤ) : LaxMonoidal.μ Q P T =
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
private lemma mapDerivedCategoryFactorsh_hom_app_quotient_obj (P : CochainComplex C ℤ) :
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
lemma mapDerivedCategoryTensorComparison_app_app_Q_comp (P T : CochainComplex C ℤ) :
    (F.mapDerivedCategoryTensorComparison.app (Q.obj P)).app (Q.obj T) ≫
      (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
        LaxMonoidal.μ Q ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj T) =
      F.mapDerivedCategory.map (LaxMonoidal.μ Q P T) ≫
        F.mapDerivedCategoryFactors.hom.app (P ⊗ T) ≫
          Q.map (F.mapCochainComplexμIso P T).inv := by
  have h := F.mapDerivedCategoryTensorComparison_app_app_comp
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj T)
  rw [mapDerivedCategoryFactorsh_hom_app_quotient_obj,
    mapDerivedCategoryFactorsh_hom_app_quotient_obj] at h
  erw [mapDerivedCategoryFactorsh_hom_app_quotient_obj] at h
  rw [μ_Q_eq_μ_Qh, μ_Q_eq_μ_Qh]
  exact h

/-- Naturality of the tensor comparison of `D(F)` in both variables. -/
@[reassoc]
lemma mapDerivedCategoryTensorComparison_naturality {X X' Y Y' : DerivedCategory C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    F.mapDerivedCategory.map (f ⊗ₘ g) ≫ (F.mapDerivedCategoryTensorComparison.app X').app Y' =
      (F.mapDerivedCategoryTensorComparison.app X).app Y ≫
        (F.mapDerivedCategory.map f ⊗ₘ F.mapDerivedCategory.map g) := by
  let := F.mapDerivedCategoryOplaxMonoidal
  exact (OplaxMonoidal.δ_natural F.mapDerivedCategory f g).symm

/-- The tensor comparison of `D(F)` on arbitrary objects with chosen maps to localized
complexes: it is the localization of the inverse tensorator of complexes. -/
lemma mapDerivedCategoryTensorComparison_total_model (X Y : DerivedCategory C)
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
    ← mapDerivedCategoryTensorComparison_naturality_assoc,
    mapDerivedCategoryTensorComparison_app_app_Q_comp, Functor.map_comp, Category.assoc]

end Abstract

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of `ℓ`-adic sheaves preserves flat objects: a flat object placed in degree `0`
is a K-flat complex, and pullback preserves K-flat complexes
(`AlgebraicGeometry.ProEtale.nativeOrdinaryKFlat_adicUpperStar`). -/
theorem adicUpperStar_preservesFlat : (adicUpperStar l f).PreservesFlat where
  flat_obj {M} hM := by
    rw [← CochainComplex.kFlat_single_obj_iff_flat _ 0, ← nativeOrdinaryKFlat_iff_kFlat] at hM ⊢
    exact ProEtaleWeilSheaf.nativeOrdinaryKFlat_of_iso
      ((HomologicalComplex.singleMapHomologicalComplex (adicUpperStar l f) (.up ℤ) 0).app M)
      (nativeOrdinaryKFlat_adicUpperStar l f _ hM)

/-- The strong monoidal structure of the pullback of `ℓ`-adic sheaves, induced on module
objects by the braided monoidal pullback of pro-étale sheaves. -/
@[instance_reducible]
def adicUpperStarMonoidal : (adicUpperStar l f).Monoidal := by
  let G := upperStar (WeilCoefficients.{u} l) f
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  dsimp only [adicUpperStar, Adjunction.modLeft]
  infer_instance

/-- The ordinary pullback/tensor comparison `D(f^*)(K ⊗ᴸ M) ⟶ D(f^*) K ⊗ᴸ D(f^*) M` of `ℓ`-adic
sheaves, `CategoryTheory.Functor.mapDerivedCategoryTensorComparison` for the strong monoidal
structure `AlgebraicGeometry.ProEtale.adicUpperStarMonoidal`. -/
def adicPullTensorComparison :
    (Functor.postcompose₂.obj (adicUpperStar l f).mapDerivedCategory).obj
        (curriedTensor (DerivedCategory (AdicSheaf l Y))) ⟶
      (((Functor.whiskeringLeft₂ _).obj (adicUpperStar l f).mapDerivedCategory).obj
        (adicUpperStar l f).mapDerivedCategory).obj
          (curriedTensor (DerivedCategory (AdicSheaf l X))) :=
  letI := adicUpperStarMonoidal l f
  letI := adicUpperStar_preservesFlat l f
  letI : (adicUpperStar l f).IsLeftAdjoint := (adicUpperStarLowerStarAdjunction l f).isLeftAdjoint
  (adicUpperStar l f).mapDerivedCategoryTensorComparison

/-- The inverse tensorator `f^*(P ⊗ T) ≅ f^* P ⊗ f^* T` of complexes of `ℓ`-adic sheaves, for
the strong monoidal structure `AlgebraicGeometry.ProEtale.adicUpperStarMonoidal`. -/
def adicPullTotal (P T : CochainComplex (AdicSheaf l Y) ℤ) :
    ((adicUpperStar l f).mapHomologicalComplex (.up ℤ)).obj (P ⊗ T) ≅
      ((adicUpperStar l f).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((adicUpperStar l f).mapHomologicalComplex (.up ℤ)).obj T :=
  letI := adicUpperStarMonoidal l f
  letI : (adicUpperStar l f).IsLeftAdjoint := (adicUpperStarLowerStarAdjunction l f).isLeftAdjoint
  ((adicUpperStar l f).mapCochainComplexμIso P T).symm

/-- The ordinary pullback/tensor comparison on objects with chosen maps to localized complexes
is the localization of the inverse tensorator of complexes. -/
theorem adicPullTensorComparison_total_model (M N : DerivedCategory (AdicSheaf l Y))
    (P T : CochainComplex (AdicSheaf l Y) ℤ) (a : M ⟶ Q.obj P) (b : N ⟶ Q.obj T) :
    ((adicPullTensorComparison l f).app M).app N ≫
      (((adicUpperStar l f).mapDerivedCategory.map a ≫
          (adicUpperStar l f).mapDerivedCategoryFactors.hom.app P) ⊗ₘ
        ((adicUpperStar l f).mapDerivedCategory.map b ≫
          (adicUpperStar l f).mapDerivedCategoryFactors.hom.app T)) ≫
        Functor.LaxMonoidal.μ Q (((adicUpperStar l f).mapHomologicalComplex (.up ℤ)).obj P)
          (((adicUpperStar l f).mapHomologicalComplex (.up ℤ)).obj T) =
      (adicUpperStar l f).mapDerivedCategory.map ((a ⊗ₘ b) ≫ Functor.LaxMonoidal.μ Q P T) ≫
        (adicUpperStar l f).mapDerivedCategoryFactors.hom.app (P ⊗ T) ≫
          Q.map (adicPullTotal l f P T).hom := by
  let := adicUpperStarMonoidal l f
  let := adicUpperStar_preservesFlat l f
  let : (adicUpperStar l f).IsLeftAdjoint := (adicUpperStarLowerStarAdjunction l f).isLeftAdjoint
  exact (adicUpperStar l f).mapDerivedCategoryTensorComparison_total_model M N P T a b

end AlgebraicGeometry.ProEtale
