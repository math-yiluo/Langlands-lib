/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData
public import WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity

set_option linter.privateModule false

/-! # Integral intermediate domains

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def reduction_iso (X : Scheme.{u})
    (M : coefficientSequenceDerived l E X) (hM : IsNormalizedCoefficientSequence l E X M)
    (A : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (e : A ≅ (coefficientSequenceLimit l E X).obj M) :
    (IntegralSystemRealization.calculus l E X).reduction.obj A ≅ M := by
  have := ((purNormalizedReconstructionOfScheme l E X
    (IntegralSystemRealization.calculus l E X)).1 M hM).2
  exact (IntegralSystemRealization.calculus l E X).reduction.mapIso e ≪≫
    asIso ((IntegralSystemRealization.calculus l E X).adjunction.counit.app M)

private theorem domain_of_realization (X : Scheme.{u})
    (M : coefficientSequenceDerived l E X) (lo hi torLo torHi : ℤ)
    (hM : SystemAdmissible l E X M lo hi torLo torHi)
    (A : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (e : A ≅ (coefficientSequenceLimit l E X).obj M) :
    finiteTorConstructibleIntegral l E X A := by
  have hcomplete := ((purNormalizedReconstructionOfScheme l E X
    (IntegralSystemRealization.calculus l E X)).1 M hM.1).1
  obtain ⟨D, hl, hA⟩ := complete_of_iso l E X e.symm hcomplete
  have hc : IsSfDerivedComplete l E X A :=
    (sfDerivedComplete_iff_legacy l E X D hl A).2 hA
  have r := reduction_iso l E X M hM.1 A e
  have d (n : ℕ) : (scalarReductionDerivedExtension.{u, u} l E X n).obj A ≅
      (coefficientSequenceDerivedEvaluation l E X n).obj M :=
    ((IntegralSystemRealization.calculus l E X).reductionEvaluation n).symm.app A ≪≫
      (coefficientSequenceDerivedEvaluation l E X n).mapIso r
  have hlevels := hM.2.2.2.2
  refine ⟨⟨hc, lo, hi, hM.2.2.1, fun n ↦ ?_⟩,
    torLo, torHi, hM.2.2.2.1, fun n ↦ ?_⟩
  · let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X) :=
      (proEtale_bounded_constructible_isTriangulated X
        (Padic.coefficientExtensionRing l E (n + 1))).1
    refine ⟨(intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).prop_of_iso
      (d n).symm (hlevels n).1, ?_⟩
    intro q hq
    apply (hlevels n).2.1
    intro hz
    exact hq (hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso (d n)))
  · refine ⟨(hlevels n).2.2.1, ?_⟩
    rintro L P ⟨q⟩ f hf hP N i hi
    exact (hlevels n).2.2.2 L P ⟨q ≪≫ d n⟩ f hf hP N i hi

end WeilConjectures.GeneratorReduction
