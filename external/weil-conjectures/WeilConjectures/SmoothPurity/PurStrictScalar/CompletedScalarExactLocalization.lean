/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitReduction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Exact localization of completed scalar extension

Source: Stacks Tags 03EK and 06YY. The constant/completed balancing detects
exactness after forgetting to abelian sheaves.
(blueprint: lem-pur-completed-scalar-extension-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})

/-- Completed scalar extension is exact, detected on underlying abelian sheaves.
Source: Stacks 03EK, 06YY
(blueprint: lem-pur-completed-scalar-extension-exact).
Proof: constant scalar extension and constant restriction are exact. The fixed
ordinary balancing identifies their composite with completed scalar extension
followed by restriction. The latter restriction leaves underlying abelian sheaves
unchanged, and the functor to abelian sheaves reflects finite limits and colimits.
Thus completed scalar extension preserves both. -/
theorem completedTensor_exact :
    PreservesFiniteLimits (pbcExtend (completedCoefficientMap l E F i W)) ∧
      PreservesFiniteColimits (pbcExtend (completedCoefficientMap l E F i W)) := by
  have := (baseTensor_exact l E F i W).1
  have := (baseTensor_exact l E F i W).2
  have := scalarConstantRestriction_limits l E W
  have := scalarConstantRestriction_colimits l E W
  let A := integralConstantRingOfUniverses l F W
  let R := completedIntegralCoefficientSheafUnrestricted l F W
  let U := SheafOfModules.toSheaf.{u + 1} A
  let e : pbcExtend (completedCoefficientMap l E F i W) ⋙
      SheafOfModules.toSheaf.{u + 1} R ≅
      (constantRestriction l E W ⋙ pbcExtend (constantMap l E F i W)) ⋙ U :=
    isoWhiskerRight (scalarCompletionOrdinary l E F i W).symm U
  have : PreservesFiniteLimits
      (pbcExtend (completedCoefficientMap l E F i W) ⋙ SheafOfModules.toSheaf R) :=
    preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits
      (pbcExtend (completedCoefficientMap l E F i W) ⋙ SheafOfModules.toSheaf R) :=
    preservesFiniteColimits_of_natIso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R)⟩

/-- The exact termwise model, fixed by the universal derived counit.
Source: Stacks 06YY (blueprint: def-pur-completed-scalar-exact-model). -/
def completedTensorModel :
    pbcDerivedExtend (completedCoefficientMap l E F i W) ≅
      (letI := (completedTensor_exact l E F i W).1
       have := (completedTensor_exact l E F i W).2
       (pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategory) := by
  have := (completedTensor_exact l E F i W).1
  have := (completedTensor_exact l E F i W).2
  have := pbcDerivedExtension_universal (completedCoefficientMap l E F i W)
  have : (pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategory.IsLeftDerivedFunctor
      (pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (scalarReductionSource l E W) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ _
  exact Functor.leftDerivedUnique _ _
    (pbcExtensionCounit (completedCoefficientMap l E F i W))
    (pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (scalarReductionSource l E W) (.up ℤ))

/-- The exact localization comparison preserves the computation counit on complexes.
Source: Stacks 06YY (blueprint: lem-pur-completed-scalar-model-counit). -/
theorem completedTensorModel_counit (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (letI := (completedTensor_exact l E F i W).1
     have := (completedTensor_exact l E F i W).2
     (completedTensorModel l E F i W).hom.app (DerivedCategory.Q.obj P) ≫
       (pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategoryFactors.hom.app P) =
      pbcComplexCounit (completedCoefficientMap l E F i W) P := by
  have := (completedTensor_exact l E F i W).1
  have := (completedTensor_exact l E F i W).2
  have := pbcDerivedExtension_universal (completedCoefficientMap l E F i W)
  have h := Functor.leftDerivedNatTrans_app
    (pbcDerivedExtend (completedCoefficientMap l E F i W))
    (pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategory
    (pbcExtensionCounit (completedCoefficientMap l E F i W))
    (pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (scalarReductionSource l E W) (.up ℤ))
    (𝟙 _) ((HomotopyCategory.quotient _ _).obj P)
  simp only [NatTrans.id_app, Category.comp_id] at h
  change (completedTensorModel l E F i W).hom.app
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫ _ = _ at h
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  dsimp only [pbcComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at h ⊢
  erw [(pbcDerivedExtend (completedCoefficientMap l E F i W)).map_id,
    DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  erw [(pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategory.map_id,
    DerivedCategory.Qh.map_id, Category.comp_id] at h
  erw [Category.id_comp] at h
  exact h

end WeilConjectures.PurStrictScalar
