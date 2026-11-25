/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Finitely many maximal ideals over a nonzero element

Source: Stacks Project, Algebra, Lemma Tag 00PF (blueprint:
lem-sc-finite-maximals-over-element).
-/

@[expose] public section

universe u

namespace Ring

/-- For a one-dimensional Noetherian domain, only finitely many maximal ideals contain
any fixed nonzero element (Stacks, Tag 00PF).
(blueprint: lem-sc-finite-maximals-over-element)

Proof: For `I = xR`, the minimal primes over `I` form a finite set by
`lem-sc-finite-minimal-primes-over-ideal`. Any maximal ideal containing `x` contains one
of these minimal primes by `lem-weil-pbc-prime-contains-minimal-prime`. Since `R` is a domain,
that prime is nonzero; the dimension-one hypothesis forces it to equal the maximal ideal.
Thus the maximal ideals in question form a subset of a finite set. -/
theorem finite_maximalIdeals_containing_nonzero
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h_dim : ringKrullDim R = 1) (x : R) (hx : x ≠ 0) :
    Set.Finite {m : Ideal R | m.IsMaximal ∧ x ∈ m} := by
  let : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [h_dim])
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {x})).subset ?_
  rintro m ⟨hm, hxm⟩
  let : m.IsPrime := hm.isPrime
  obtain ⟨p, hp, hpm⟩ := Ideal.exists_minimalPrimes_le
    (m.span_singleton_le_iff_mem.mpr hxm)
  have hxp : x ∈ p := hp.le (Ideal.subset_span (Set.mem_singleton x))
  have hp0 : p ≠ ⊥ := by
    intro h
    exact hx (by simpa [h] using hxp)
  have h_eq : p = m := (hp.isPrime.isMaximal_of_ne_bot hp0).eq_of_le hm.ne_top hpm
  exact h_eq ▸ hp

end Ring
