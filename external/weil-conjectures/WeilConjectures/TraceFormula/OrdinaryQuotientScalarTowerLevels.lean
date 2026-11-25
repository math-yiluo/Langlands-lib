/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionAssociationSuccessor
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationScalarUnits

/-! # Finite levels of the ordinary scalar tower

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
(blueprint: def-trf-ordinary-quotient-scalar-tower-levels).
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralCoefficientCommRingSheaf

private def direct (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W) :
    CochainComplex (scalarReductionSource l E W) ℤ ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ :=
  M.quotient l E W ⋙ A.scalar.model.E.mapHomologicalComplex (.up ℤ)

attribute [local irreducible] SemilinearSections.systemMap
  CategoryTheory.Functor.leftAdjoint HasDerivedCategory.standard
attribute [local implicit_reducible] SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

end OrdinaryScalarTowerProof
end WeilConjectures
