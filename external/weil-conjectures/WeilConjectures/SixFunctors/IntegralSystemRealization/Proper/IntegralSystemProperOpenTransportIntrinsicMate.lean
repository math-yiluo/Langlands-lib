/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenTransportCanonicalMate

/-! Intrinsic mate identity for the semilinear proper/open calculus. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The intrinsic semilinear gamma is the mate of the intrinsic alpha.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0F7B.
(blueprint: lem-sf-integral-system-proper-open-transport-core-intrinsic-mate).
Proof: unfold the intrinsic proper/open gamma and apply the defining mate
bijection to the intrinsic alpha. -/
theorem integralSystemIntrinsicMate
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (mateEquiv (ProEtale.SemilinearProperOpen.adj (scalarRings l E)
      (scalarTransitions l E) r) (ProEtale.SemilinearProperOpen.adj
        (scalarRings l E) (scalarTransitions l E) p)
      (TwoSquare.mk _ _ _ _ (ProEtale.SemilinearProperOpen.alpha
        (scalarRings l E) (scalarTransitions l E) k r p i h))).app M =
      (ProEtale.SemilinearProperOpen.gamma (scalarRings l E)
        (scalarTransitions l E) k r p i h).app M := by
  rfl

end WeilConjectures.IntegralSystemRealization
