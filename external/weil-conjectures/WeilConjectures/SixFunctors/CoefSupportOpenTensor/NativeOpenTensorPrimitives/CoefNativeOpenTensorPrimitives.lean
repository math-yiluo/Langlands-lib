/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefOpenTensorEvaluationData
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorCochainData

/-! # Primitive native open tensor cochain types

These are the explicit specializations previously written in
`CoefNativeOpenTensorCochains`, shared with the two existence lemmas.
Source: Stacks 0E8I and 0GL1
(blueprint: def-coef-native-open-tensor-primitives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor.NativeOpenTensorPrimitives

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Sequence-site specialization of ordinary open tensor data.
Source: Stacks 0E8I (blueprint: def-coef-native-open-tensor-primitives). -/
abbrev SystemOpenCochainsData {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  letI := ProEtale.VaryingRing.extensionAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  @OpenTensorCochainData.{u + 1, u, u} (ℕ × Z.ProEt) _
    (ProEtale.VaryingRing.sequenceSiteSmall Z)
    (coefficientSequenceTopology (ProEt.topology Z)) (coefficientSequenceCommRingSheaf.{u, u} l E Z)
    (ℕ × X.ProEt) _ (ProEtale.VaryingRing.sequenceSiteSmall X)
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf.{u, u} l E X)
    (ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.extensionAdditive (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.pullAdditive (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.baseChange j) (pullSection l E j)

/-- Finite-coefficient specialization of ordinary open tensor data.
Source: Stacks 0E8I (blueprint: def-coef-native-open-tensor-primitives). -/
abbrev FiniteOpenCochainsData {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (n : ℕ) :=
  letI := ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteLimits (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteColimits (compactSupportSystemLevel l E n) j
  letI := proEtaleRingModulePullback_additive j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteLimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteColimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  @OpenTensorCochainData.{u + 1, u, u} Z.ProEt _
    (WeilConjectures.instEssentiallySmallProEt_weilConjectures Z) (ProEt.topology Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    X.ProEt _ (WeilConjectures.instEssentiallySmallProEt_weilConjectures X) (ProEt.topology X)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j)
    (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j)
    _ _
    (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)
    (proEtaleBaseChange j) (finitePullSection l E j n)

end WeilConjectures.CoefSupportOpenTensor.NativeOpenTensorPrimitives
