/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientModel
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # The ordinary quotient system preserves K-flat complexes

Source: Stacks 06YN, 07A4 and 0941.

K-flatness on the ringed sequence site is tested on finite evaluations: evaluation is
exact, commutes with the total tensor product, and exactness on the sequence site is
detected by the finite evaluations. The finite evaluations of the ordinary quotient
system of a K-flat complex are its finite scalar extensions, which are K-flat.
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

noncomputable section
set_option synthInstance.maxSize 4096
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension coefficientEvaluationTensorIso
  coefficientScalarTensorIso

/-- Exactness of a short complex on the ringed sequence site is detected by the finite
evaluations. Source: Stacks 0941. -/
theorem coefficientSequence_exact_iff_evaluations
    (s : ShortComplex (coefficientSequenceModules l E W)) :
    s.Exact ↔ ∀ n : ℕ, (s.map (coefficientSequenceEvaluation l E W n)).Exact := by
  let D := (SemilinearSections.semilinearDerivedSections.{t + 1, t, u}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)).some.systems
  exact D.componentwise s

/-- A complex on the ringed sequence site is K-flat once all its finite evaluations are.
Source: Stacks 06YN, 0941. -/
theorem coefficientSequence_isKFlat_of_evaluations
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hC : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) C := by
  let R := coefficientSequenceCommRingSheaf l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro Z hZ i
  apply (coefficientSequence_exact_iff_evaluations l E W _).2
  intro n
  have hZn : (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
      (.up ℤ)).obj Z).Acyclic := by
    intro j
    exact (hZ j).map (coefficientSequenceEvaluation l E W n)
  exact ((hC n _ hZn) i).of_iso (coefficientEvaluationTensorIso l E W n Z C).symm

/-- K-flatness is invariant under isomorphism of complexes.
Source: Stacks 06YN. -/
theorem coefficientIsKFlat_of_iso {n : ℕ}
    {C D : CochainComplex (normalizedDVRModules l E W n) ℤ} (e : C ≅ D)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) D) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) C := by
  intro Z hZ i
  exact ((hD Z hZ) i).of_iso ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).mapIso ((Iso.refl Z).prod e)).symm

namespace OrdinaryQuotient

/-- The ordinary quotient system of a flat-term K-flat complex is K-flat.
Source: Stacks 06YN, 07A4 and 0941. -/
theorem OrdinaryModel.quotient_isKFlat (M : OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (_hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) ((M.quotient l E W).obj P) := by
  apply coefficientSequence_isKFlat_of_evaluations
  intro n
  exact coefficientIsKFlat_of_iso l E W
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P)
    ((coefficientTensorModelPreservation l E W).1 P hP n)

end OrdinaryQuotient

end
end WeilConjectures
