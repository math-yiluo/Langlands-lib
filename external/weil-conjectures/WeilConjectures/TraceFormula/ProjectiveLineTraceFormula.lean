/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv
public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.ZetaFunction.Examples

/-!

# The trace formula for the constant Weil object on the projective line

For `X = ℙ¹` over `k = 𝔽_q`, the constant Weil object `ℚ̲̄_ℓ` and `m ≥ 1`, both sides of the
Grothendieck–Lefschetz trace formula for the `m`-th power of Frobenius are `qᵐ + 1` (blueprint
`example-frobenius-projective-line`): the points of degree `m` are the `qᵐ + 1` points of
`ℙ¹(𝔽_{qᵐ})`, each has local term `1`, and the alternating trace of the `m`-th Frobenius on
`RΓ_c(ℙ¹ ⊗ k̄, ℚ̄_ℓ)` is `qᵐ + 1`.

## Main statements

- `ProEtale.CondensedRing.projectiveLine_weilTraceFormula`: blueprint
  `example-frobenius-projective-line`, both sides of the trace formula.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

open Scheme

attribute [local instance] fintypeFrobeniusFixedPoints

/-- Blueprint `example-frobenius-projective-line`: for `X = ℙ¹` over `k = 𝔽_q`, the constant
Weil object `ℚ̲̄_ℓ` and `m ≥ 1`,

* (local side) each point of degree `m`, that is each fixed point of the `m`-th power of
  Frobenius, has local term `tₘ(ℚ̲̄_ℓ; x̄) = 1`, and there are `qᵐ + 1` of them, the points of
  `ℙ¹(𝔽_{qᵐ})`;
* (global side) the alternating trace of the `m`-th Frobenius on `RΓ_c(ℙ¹ ⊗ k̄, ℚ̄_ℓ)` is
  `qᵐ + 1`.

The cohomology `ℚ̄_ℓ ⊕ ℚ̄_ℓ(-1)[-2]` of the global side, degree by degree, is
`AlgebraicGeometry.projectiveLine_frobenius_trace_formula`. -/
theorem projectiveLine_weilTraceFormula (m : ℕ) [NeZero m] :
    (∀ x : frobeniusFixedPoints (Iso.refl (overProjectiveLine (point k))) m,
      weilStalkTraceAlternatingSum ℓ m x.1 x.2.2
        (weilUnit ℓ (Iso.refl (overProjectiveLine (point k)))) = 1) ∧
    Nat.card (frobeniusFixedPoints (Iso.refl (overProjectiveLine (point k))) m) =
      Nat.card k ^ m + 1 ∧
    weilStalkTraceAlternatingSum ℓ m (specAlgebraicClosure k) (specAlgebraicClosure_comp_pow m)
        ((weilCompactSupportCohomology ℓ (Iso.refl (overProjectiveLine (point k)))).obj
          (weilUnit ℓ (Iso.refl (overProjectiveLine (point k))))) =
      Nat.card k ^ m + 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
  have hcard : Nat.card (frobeniusFixedPoints (Iso.refl (overProjectiveLine (point k))) (n + 1)) =
      Nat.card k ^ (n + 1) + 1 := by
    have h := AlgebraicGeometry.pointCount_projectiveLine k (n := n + 1) (Nat.succ_ne_zero n)
    rw [Hom.pointCount] at h
    rw [← Nat.card_congr (fieldPointsEquivFrobeniusFixedPointsRefl n)]
    simp only [overProjectiveLine, Over.mk_hom]
    rw [Nat.add_comm (Nat.card k ^ (n + 1)) 1, ← h]
    congr 2
  refine ⟨fun x ↦ weilStalkTraceAlternatingSum_weilUnit ℓ _ (n + 1) x.1 x.2.2, hcard, ?_⟩
  rw [weilPointCount ℓ (Iso.refl _) ⟨1, Nat.one_pos, Iso.pow_refl 1⟩, hcard]
  push_cast
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
