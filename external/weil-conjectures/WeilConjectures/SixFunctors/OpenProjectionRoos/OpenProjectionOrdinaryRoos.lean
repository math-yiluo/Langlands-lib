/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletionData
import WeilConjectures.SixFunctors.SfOpenRoos.SfOpenRoosExtensionComparison
import WeilConjectures.SixFunctors.SfOpenRoos.SfOpenRoosRestrictionUnit

/-! # Transport of the ordinary open tensor and signed Roos comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

variable
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
  (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
  (c : IntegralOpenReduction.Comparison l E j o SX SU st)
  (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)

attribute [local irreducible] integralOperationsTensorTowerFunctor
  coefficientTotalTensor integralOperationsTensorLevel
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralComplexFunctor scalarReductionExistence unrestrictedIntegralReductionExistence

/-- Ordinary descent and signed Roos comparison in the global coefficient presentation.
Source: Stacks 09BP, 03DI, 0GL1; the open-factor blueprint argument
(blueprint: lem-sf-open-projection-ordinary-roos).

Proof: identify the open pro-etale site with the slice at the open object, using the
coefficient equivalence in o. Finite type over the field makes both schemes
Noetherian, so j is quasi-compact. Apply the normalized extension and restriction
Roos comparisons, then transport along o.integral. The product projection identities
and both signed coordinates are preserved by this exact equivalence. The strict
augmentation has coordinates (lift a,0); transport gives the augmentation clauses.
The slice unit is invertible, and its localization gives the derived unit. Good
complexes are flat-term K-flat complexes; the flatness and extension-preservation
maps are supplied separately, and restriction preserves them by exact monoidal
restriction.
Descend m.totalComparison.chain through the two resolving localizations, using
q.tensorX.ordinary and q.tensorU.ordinary. The descent comparison on representatives
is exactly the displayed chain identity. All these constructions precede completion. -/
theorem openProjectionOrdinaryRoos
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [U.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))]
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
    integralOperationsGoodComplex l E W P →
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P)
    (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
    :
    ∃ (extension : RoosComparison (IntegralOpenReduction.extension l E j o)),
    ∃ (restriction : RoosComparison (IntegralOpenReduction.restriction l E j o)),
    ∃ (moduleUnit : 𝟭 (scalarReductionSource l E U) ≅
    IntegralOpenReduction.extension l E j o ⋙ IntegralOpenReduction.restriction l E j o),
    ∃ (_moduleUnit_hom : moduleUnit.hom = (IntegralOpenReduction.ordinaryAdjunction l E j o).unit),
    ∃ (unit : 𝟭 (DerivedCategory (scalarReductionSource l E U)) ≅
    IntegralOpenReduction.shriek l E j o ⋙ IntegralOpenReduction.star l E j o),
    ∃ (_unit_hom : unit.hom = (IntegralOpenReduction.openAdjunction l E j o).unit),
    ∃ (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P)),
    ∃ (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
    rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o),
    OrdinaryRepresentative l E j o SX SU AX AU st m c q flat extendGood restrictGood ordinary := by
  sorry

end WeilConjectures.OpenProjectionRoos
