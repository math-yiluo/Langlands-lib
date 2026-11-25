/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SerreConditions
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.SerreS2RegularQuotientAssociatedHeight

/-!
# Membership in a reduced S2 ring detected in codimension one

Source: Stacks Project, Algebra, Tag 031T, proof of (1) and (2), using only S2;
the argument applies to nonzerodivisor denominators in a reduced ring.
(blueprint: lem-weil-pbc-serre-s2-total-fraction-membership).
-/

@[expose] public section

universe u

/-- A total fraction of a reduced Noetherian S2 ring lies in the ring if it does so
at every prime of height at most one, expressed by clearing a local denominator.
Source: Stacks Project, Algebra, Tag 031T, proof of (1) and (2), using only S2
(blueprint: lem-weil-pbc-serre-s2-total-fraction-membership).

Proof: Write x = a/b with b a nonzerodivisor. If x is not in R, the class of a in
M = R/bR is nonzero. Choose an associated prime p of the cyclic submodule generated
by this class; it is also an associated prime of M, and it contains the annihilator
J = (bR : a). Localizing at p gives depth(M_p) = 0. Since b is regular in R_p,
the regular-element depth formula (Tag 090R) gives depth(R_p) = 1. Condition S2
forces min(2,height(p)) ≤ 1, hence height(p) ≤ 1. The local denominator hypothesis
supplies s outside p and c with sx = c. Multiplication by b and injectivity of
R → Q(R) gives sa = bc, so s lies in J and hence in p, a contradiction.
Thus x comes from R. If b is a unit the conclusion is immediate; if R is the zero
ring every fraction already comes from R. No domain or normality assumption is used. -/
theorem Ring.exists_algebraMap_eq_of_serreS_two
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (hS : Ring.IsSerreS R 2) (x : FractionRing R)
    (hlocal : ∀ (p : Ideal R) [p.IsPrime], p.height ≤ (1 : ℕ∞) →
      ∃ s : R, s ∉ p ∧ ∃ a : R,
        algebraMap R (FractionRing R) s * x = algebraMap R (FractionRing R) a) :
    ∃ a : R, algebraMap R (FractionRing R) a = x  := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) x
  by_cases ha : a ∈ Ideal.span {(b : R)}
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨c, ?_⟩
    apply (IsLocalization.map_units (FractionRing R) b).mul_left_cancel
    calc
      algebraMap R (FractionRing R) b * algebraMap R (FractionRing R) c =
          algebraMap R (FractionRing R) a := by rw [← map_mul, mul_comm, hc]
      _ = algebraMap R (FractionRing R) b * x := by rw [← hab, mul_comm]
  · have hclass : Ideal.Quotient.mk (Ideal.span {(b : R)}) a ≠ 0 := by
      simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using ha
    obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hclass
    let := hp.isPrime
    have hheight := Ideal.height_le_one_of_mem_associatedPrimes_regular_quotient hS
      b b.prop p hp
    obtain ⟨s, hs, c, hsc⟩ := hlocal p hheight
    have hsa : s * a = c * b := by
      apply IsFractionRing.injective R (FractionRing R)
      simp only [map_mul]
      calc
        algebraMap R (FractionRing R) s * algebraMap R (FractionRing R) a =
            algebraMap R (FractionRing R) s *
              (x * algebraMap R (FractionRing R) b) := by rw [hab]
        _ = (algebraMap R (FractionRing R) s * x) *
            algebraMap R (FractionRing R) b := by ring
        _ = algebraMap R (FractionRing R) c * algebraMap R (FractionRing R) b := by
          rw [hsc]
    apply False.elim (hs (hle ?_))
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk (Ideal.span {(b : R)}) (s * a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hsa]
    exact Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩

