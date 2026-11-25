/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.BlowupChartExpansion

/-!
# Regular systems of parameters of a regular local surface

Let `R` be a regular local ring of dimension `2` and `(u, v)` a regular system of parameters,
i.e. `𝔪 = (u, v)`. Then `R/(u)` is a domain on which `v` is a non-zero-divisor, and for
`h ∈ 𝔪 ∖ 𝔪²` the quotient `R/(h)` is a regular ring. We deduce the two facts about tangent
directions used to construct the separating chart of the blow-up:

* a generic line `x₀ + c y₀ = 0` is not tangent to a curve `V(r)`
  (`BlowupChart.not_mem_span_sup_pow_of_eval_ne_zero`);
* if the tangent cones of `V(f)` and `V(g)` meet only at the origin, the dehomogenized initial
  forms of `f` and `g` have no common root (`BlowupChart.not_eval_mem_and_eval_mem`).
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

namespace BlowupChart

variable {R : Type u} [CommRing R]

/-- `(a + c b, b) = (a, b)`. -/
theorem span_pair_add_mul (a b c : R) :
    Ideal.span {a + c * b, b} = Ideal.span {a, b} := by
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_) <;>
    rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, Ideal.mem_span_pair]
  · exact ⟨1, c, by ring⟩
  · exact ⟨0, 1, by ring⟩
  · exact ⟨1, -c, by ring⟩
  · exact ⟨0, 1, by ring⟩

variable [IsRegularLocalRing R]

/-- In a regular local ring of dimension `2`, the maximal ideal is not principal. -/
theorem maximalIdeal_ne_span_singleton (hdim : ringKrullDim R = 2) (z : R) :
    maximalIdeal R ≠ Ideal.span {z} := by
  intro h
  have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hdim, h] at h1
  have h2 : (Ideal.span {z}).spanFinrank ≤ 1 := by
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_singleton z)
  have h3 : ((Ideal.span {z}).spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h2
  rw [h1] at h3
  exact absurd h3 (by decide)

/-- For a regular system of parameters `(u, v)` of a regular local ring of dimension `2`, the
quotient `R/(u)` is a domain and `v` is a non-zero-divisor on it. -/
theorem isDomain_quotient_and_mul_eq_zero (hdim : ringKrullDim R = 2) {u v : R}
    (hm : maximalIdeal R = Ideal.span {u, v}) :
    IsDomain (R ⧸ Ideal.span {u}) ∧
      ∀ a : R ⧸ Ideal.span {u}, Ideal.Quotient.mk _ v * a = 0 → a = 0 := by
  have hsys : IsRegularSystemOfParameters [u, v] := by
    refine ⟨?_, ?_⟩
    · rw [hm]
      congr 1
      ext w
      simp
    · rw [hdim]
      rfl
  have := ((IsRegularLocalRing.isRegular_and_quotients_of_generators R 2 (by rw [hdim]; rfl)
    [u, v] hsys).2.1 1 (by norm_num)).1
  have hq : Ideal.ofList ([u, v].take 1) = Ideal.span {u} := by
    simp
  rw [hq] at this
  have hdom : IsDomain (R ⧸ Ideal.span {u}) := inferInstance
  refine ⟨hdom, fun a ha => ?_⟩
  have hv : Ideal.Quotient.mk (Ideal.span {u}) v ≠ 0 := by
    intro hv
    rw [Ideal.Quotient.eq_zero_iff_mem] at hv
    apply maximalIdeal_ne_span_singleton hdim u
    rw [hm]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_mono (by simp))
    rintro _ (rfl | rfl)
    · exact Ideal.mem_span_singleton_self _
    · exact hv
  exact (mul_eq_zero.mp ha).resolve_left hv

/-- For `h ∈ 𝔪 ∖ 𝔪²` in a regular local ring of dimension `2`, the quotient `R/(h)` is a regular
ring (a discrete valuation ring). -/
theorem isRegularRing_quotient (hdim : ringKrullDim R = 2) {h : R} (hh : h ∈ maximalIdeal R)
    (hh2 : h ∉ maximalIdeal R ^ 2) : IsRegularRing (R ⧸ Ideal.span {h}) := by
  obtain ⟨_, hreg, hrank⟩ := IsRegularLocalRing.quotient_span_singleton hh hh2
  have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ Ideal.span {h})
  rw [hdim, ← hrank] at h1
  have h3 : (maximalIdeal (R ⧸ Ideal.span {h})).spanFinrank = 1 := by
    have : (((maximalIdeal (R ⧸ Ideal.span {h})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) =
        ((2 : ℕ) : WithBot ℕ∞) := h1
    have : (maximalIdeal (R ⧸ Ideal.span {h})).spanFinrank + 1 = 2 := by exact_mod_cast this
    omega
  have hdim' : ringKrullDim (R ⧸ Ideal.span {h}) ≤ 1 := by
    rw [← h2, h3]
    rfl
  have : IsIntegrallyClosed (R ⧸ Ideal.span {h}) :=
    IsRegularLocalRing.isIntegrallyClosed _ hdim'
  have : Ring.KrullDimLE 1 (R ⧸ Ideal.span {h}) := Ring.krullDimLE_iff.mpr (by exact_mod_cast hdim')
  have : Ring.DimensionLEOne (R ⧸ Ideal.span {h}) :=
    ⟨fun {p} hp hp' ↦ Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this p hp hp'⟩
  have : IsDedekindDomain (R ⧸ Ideal.span {h}) := { }
  infer_instance

end BlowupChart
