/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.ZetaFunction.Examples
public import WeilConjectures.ZetaFunction.TraceFormula
public import WeilConjectures.ZetaFunction.TraceFormulaExamples

/-!

# Frobenius on the projective line

For `X₀ = ℙ¹` over `k₀ = 𝔽_q`, constant coefficients `ℚ̄_ℓ` and `m ≥ 1`, both sides of the trace
formula for the `m`-th power of Frobenius are `1 + qᵐ` (blueprint
`example-frobenius-projective-line`): `Φ_m` has the `qᵐ + 1` fixed points of `ℙ¹(𝔽_{qᵐ})`,
geometric Frobenius `F` acts on the line `H⁰(ℙ¹ ⊗ k̄, ℚ̄_ℓ)` by `1` and on the line `H²` by
`q`, `H¹ = 0`, and `∑ᵢ (-1)ⁱ Tr(Fᵐ | Hⁱ) = 1 + qᵐ`.

## Main statements

- `AlgebraicGeometry.projectiveLine_frobenius_trace_formula`: blueprint
  `example-frobenius-projective-line`.

## Implementation notes

The local side is stated as the point count `#ℙ¹(𝔽_{qᵐ})`, the number of fixed points of `Φ_m`,
each of local term `1` for the constant sheaf; the global side is the alternating trace of `Fᵐ`
on the cohomology `Hⁱ(ℙ¹ ⊗ k̄, ℚ̄_ℓ)` of the Weil sheaf `ℚ̄_ℓ`. The local terms `1` at the
fixed points, and the equality of both sides of the trace formula for the constant Weil object,
are `ProEtale.CondensedRing.projectiveLine_weilTraceFormula`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (k : Type u) [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]

/-- Blueprint `example-frobenius-projective-line`: let `X₀ = ℙ¹` over `k = 𝔽_q` and `m ≥ 1`.

* (local side) the fixed points of the `m`-th power of Frobenius are the points of
  `ℙ¹(𝔽_{qᵐ})`, and there are `qᵐ + 1` of them;
* (global side) `RΓ(ℙ¹ ⊗ k̄, ℚ̄_ℓ) = ℚ̄_ℓ ⊕ ℚ̄_ℓ(-1)[-2]`: `H⁰` is a line on which Frobenius acts
  by `1`, `H¹ = 0`, and `H²` is a line on which Frobenius acts by `q`, so that `Fᵐ` acts on it
  by `qᵐ`; hence `∑ᵢ (-1)ⁱ Tr(Fᵐ | Hⁱ(ℙ¹ ⊗ k̄, ℚ̄_ℓ)) = 1 + qᵐ`, with no signs. -/
theorem projectiveLine_frobenius_trace_formula {m : ℕ} (hm : 1 ≤ m) :
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).pointCount m = Nat.card k ^ m + 1 ∧
    Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology 0).carrier = 1 ∧
    ((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology 0).frobeniusEnd =
      1 ∧
    Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology 1).carrier = 0 ∧
    Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology 2).carrier = 1 ∧
    ((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology 2).frobeniusEnd ^ m =
      (Nat.card k : PadicAlgCl l) ^ m • 1 ∧
    ∑ i ∈ Finset.range 3, (-1) ^ i * LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology
          (i : ℤ)).frobeniusEnd ^ m) = 1 + (Nat.card k : PadicAlgCl l) ^ m := by
  set Y := ProjectiveLine (Spec (.of k))
  have hN := pointCount_projectiveLine k (n := m) (by omega)
  have hsum := WeilSheaf.pointCount_eq_sum_trace_cohomology k l Y 1 hm
  obtain ⟨-, hb⟩ := isIntegralFrobeniusFactor_projectiveLine k
  obtain ⟨hb0, hb1, -⟩ := hb l
  obtain ⟨hH2, hF2⟩ := Scheme.finrank_cohomology_two_and_frobeniusEnd_of_curve k l Y
  have hF0 : ((WeilSheaf.adicConstant k l Y).cohomology 0).frobeniusEnd = 1 := by
    rw [FrobeniusModule.frobeniusEnd, WeilSheaf.frobenius_cohomology_zero_adicConstant]
    rfl
  rw [hN] at hsum
  push_cast at hsum
  exact ⟨hN.trans (add_comm _ _), hb0, hF0, hb1, hH2, by rw [hF2, smul_pow, one_pow],
    hsum.symm⟩

end AlgebraicGeometry
