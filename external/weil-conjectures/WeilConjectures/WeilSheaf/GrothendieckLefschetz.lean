/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Stalk
import WeilConjectures.PointCount
import WeilConjectures.ZetaFunction.WeilObjectComparison
import WeilConjectures.WeilSheaf.StalkCharpoly
import WeilConjectures.WeilSheaf.TraceFunctionCongr

/-!
# The Grothendieck–Lefschetz trace formula for Weil sheaves

For a separated `k₀`-scheme `X` of finite type and a Weil sheaf `F` on `X`, the alternating sum of
the traces of the `m`-th power of the geometric Frobenius on the compactly supported cohomology
`H_c^i(X ⊗ k̄, F)` is the sum, over the `𝔽_{qᵐ}`-points `y` of `X`, of the traces of the local
Frobenius `F_{y, m}` on the geometric stalks: grouping the `𝔽_{qᵐ}`-points by the closed point
`x` of `X` they lie over, a closed point of degree `e ∣ m` carries `e` such points, each with
local Frobenius `F_x^{m / e}`. This is blueprint `theorem-grothendieck-lefschetz-trace-formula--8`
of the trace formula chapter, in the case of a Weil sheaf in degree zero; it is deduced from the
trace formula for Weil complexes,
`WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The Grothendieck–Lefschetz trace formula** (blueprint:
`theorem-grothendieck-lefschetz-trace-formula--8`, for a Weil sheaf placed in degree zero): for
every `m ≥ 1`,

`∑ᵢ (-1)ⁱ tr (Fᵐ ∣ H_c^i(X ⊗ k̄, F)) = ∑_{y ∈ X(𝔽_{qᵐ})} tr (F_{y, m} ∣ F_ȳ)
  = ∑_{x closed, deg x ∣ m} deg x · tr (F_x^{m / deg x} ∣ F_x̄)`. -/
theorem sum_trace_compactlySupportedCohomology (F : WeilSheaf k₀ l X) {m : ℕ} (hm : m ≠ 0) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l)
        (F.compactlySupportedCohomology i).carrier
        ((F.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ x : X.finitePoints, if (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ m then
        ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 : PadicAlgCl l) *
          LinearMap.trace (PadicAlgCl l) (F.stalk x).carrier ((F.stalk x).frobeniusEnd ^
            (m / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))
      else 0 := by
  classical
  let f := X ↘ Spec (CommRingCat.of k₀)
  let T := (f.finite_setOf_degreeOver_le m).toFinset
  have hT (x : X.finitePoints) (hx : f.degreeOver x.1 ∣ m) : x ∈ T :=
    (f.finite_setOf_degreeOver_le m).mem_toFinset.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hx)
  have htrace :=
    WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction (toComplex.obj F) hm
  change (∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
      ((F.compactlySupportedCohomology i).frobeniusEnd ^ m)) = _ at htrace
  simp_rw [WeilComplex.traceFunction_toComplex] at htrace
  rw [htrace, f.finsum_fieldPoints_eq_sum hm (F.traceFunction m)
    (fun x ↦ LinearMap.trace (PadicAlgCl l) _
      ((F.stalk x).frobeniusEnd ^ (m / f.degreeOver x.1)))
    (fun y x hx ↦ F.traceFunction_eq_trace_frobeniusEnd_stalk_pow m y x hx) hT]
  rw [Finset.sum_filter]
  symm
  refine (finsum_eq_sum_of_support_subset _ (s := T) ?_).trans ?_
  · intro x hx
    by_cases hd : f.degreeOver x.1 ∣ m
    · exact hT x hd
    · exact False.elim (hx (by simp [f, hd]))
  · exact Finset.sum_congr rfl fun x _ ↦ by simp [f, nsmul_eq_mul]

end AlgebraicGeometry.WeilSheaf
