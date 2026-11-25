/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # K-flatness of a strict coefficient-system presentation

Source: Stacks Project, Tags 06YY and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard

/-- A simultaneous strict quotient presentation of a good complex is K-flat.

Source: Stacks Project, Tags 06YY and 0941, applied to the evaluation functors
of the coefficient-system site.
(blueprint: lem-trf-scalar-presentation-kflat).

Proof in words: quotient extension preserves K-flatness because P is K-flat
with flat terms. Transport this property through each evaluation isomorphism.
Tensor products commute with evaluation. An acyclic test complex remains
acyclic after evaluation, so its tensor with C is acyclic at every level.
Componentwise detection of acyclicity on the system site gives the result. -/
theorem scalarPresentationKFlat
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E X) C := by
  have hflat : ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory
          (completedIntegralCommRingSheafUnrestricted l E X)) (P.obj.X i)) := fun i ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ (P.obj.X i)) (P.property.2 i)
  have hCn (n : ℕ) : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C) := by
    let : (unrestrictedIntegralReductionFunctor l E X n).Additive :=
      (unrestrictedIntegralReductionExistence l E X n).choose_spec.choose_spec.choose_spec.choose
    have hK := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (completedIntegralCommRingProjectionUnrestricted l E X n) P.obj
      (unrestrictedIntegralReductionFunctor l E X n)
      (unrestrictedIntegralReductionExistence l E X n).choose_spec.choose
      (unrestrictedIntegralReductionExistence l E X n).choose_spec.choose_spec.choose
      P.property.1 hflat
    let Rn := integralCoefficientCommRingSheaf l E X n
    let := SheafOfModules.isMonoidal_W_independentCoefficients Rn
    let := SheafOfModules.monoidalCategory Rn
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients Rn
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients Rn
    intro Z hZ i
    let ei := ((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj Z).mapIso (κ n).symm
    exact (hK.1 Z hZ i).of_iso ei
  let R := coefficientSequenceCommRingSheaf l E X
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro Z hZ i
  let D := (SemilinearSections.semilinearDerivedSections.{u + 1, u, u}
    (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X)
    (coefficientSequenceCommRingTransition l E X)).some.systems
  apply (D.componentwise _).2
  intro n
  have hZn : (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex
      (.up ℤ)).obj Z).Acyclic := fun j ↦ (hZ j).map (coefficientSequenceEvaluation l E X n)
  exact ((hCn n _ hZn) i).of_iso (coefficientEvaluationTensorIso l E X n Z C).symm

end WeilConjectures
