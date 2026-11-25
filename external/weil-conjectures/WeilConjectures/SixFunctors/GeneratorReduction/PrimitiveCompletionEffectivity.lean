/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData
import WeilConjectures.SixFunctors.GeneratorReduction.FiniteTorOrdinaryTensorComplete
import WeilConjectures.SixFunctors.GeneratorReduction.FiniteTorOrdinaryPullComplete
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible

set_option linter.privateModule false

/-! # Primitive completion effectivity

Source: current blueprint fix-prop-coherence, primitive realization step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem completion_unit_isIso (X : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : IntegralOnSlice.IsComplete l E X none K) :
    IsIso ((IntegralOnSlice.completionUnit l E X none).app K) := by
  classical
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  let := IntegralOnSlice.goodLocalization l E X none
  let L := IntegralOnSlice.qGood l E X none
  let W := (HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E X none) (.up ℤ)).inverseImage
    (IntegralOnSlice.Good l E X none).ι
  let : L.EssSurj := Localization.essSurj L W
  let P := L.objPreimage K
  let e := L.objObjPreimageIso K
  exact ((roosIntrinsicCompletenessEquivalence p l (by omega) E X d hd K P e).out 1 5).mp hK

end WeilConjectures.GeneratorReduction
