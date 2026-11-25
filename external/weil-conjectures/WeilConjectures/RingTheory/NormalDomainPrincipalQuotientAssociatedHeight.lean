/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
import WeilConjectures.RingTheory.SerreCriterionNormal
import WeilConjectures.RingTheory.SerreS2RegularQuotientAssociatedHeight

/-!
# Associated primes of principal quotients of normal domains

Source: Stacks Project, Algebra, Tag 031T, Lemma 10.157.6 (1)
(blueprint: lem-weil-pbc-normal-domain-principal-quotient-associated-height).
-/

@[expose] public section

universe u

namespace Ideal

/-- Every associated prime of a nonzero principal quotient of a Noetherian normal domain
has height one. Source: Stacks Project, Algebra, Tag 031T, Lemma 10.157.6 (1)
(blueprint: lem-weil-pbc-normal-domain-principal-quotient-associated-height).

Since `A` is Noetherian, `isAssociatedPrime_iff` identifies association with being the
annihilator of an element; primality forces that element to be nonzero. For a prime,
`Ideal.height` is the supremum of lengths of strict prime chains ending at that prime.

Proof following the six steps of the node:
1. The element `a` annihilates every element of `A/aA`, hence belongs to `p`. Since `a`
   is nonzero and `A` is a domain, the prime chain `(0) < p` gives height at least one.
2. By `lem-weil-pbc-localization-normal-domain`, all prime localizations are normal domains.
   Serre's criterion `lem-weil-pbc-serre-criterion-normal` gives condition `(S₂)`
   (`def-weil-pbc-serre-conditions-rk-sk`), so depth at `p` is at least `min(2, dim A_p)`.
3. Multiplication by `a` is injective. Localize the exact sequence
   `0 → A → A → A/aA → 0` using `lem-weil-pbc-localization-module-exact` and
   `def-weil-pbc-module-localization`. The ring `A_p` is Noetherian by
   `lem-weil-pbc-localization-noetherian`, and local by
   `def-weil-pbc-localization-at-prime`. The quotient is finite and nonzero since `a ∈ p`.
4. The depth inequality `lem-weil-pbc-depth-in-ses` (2), with `def-weil-pbc-depth`,
   implies depth of `(A/aA)_p` is at least one if `dim A_p ≥ 2`.
5. By `lem-weil-pbc-associated-prime-localize-at-prime`, the localized annihilator
   is the maximal ideal. The bound `lem-weil-pbc-depth-le-dim-associated-prime` gives
   depth at most the dimension of the residue field, which is zero
   (`def-weil-pbc-krull-dimension-ring`). Thus the localized quotient has depth zero.
6. Consequently `dim A_p ≤ 1`. By
   `lem-weil-pbc-localization-dimension-chains-below-prime`, no strict prime chain
   ending at `p` has length at least two. Together with step 1 this gives height one.
-/
theorem height_eq_one_of_mem_associatedPrimes_quotient_span
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {a : A} (ha : a ≠ 0) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {a})) :
    p.height = 1 := by
  let : p.IsPrime := hp.isPrime
  have hS : Ring.IsSerreS A 2 :=
    (Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS A).mp (by
    intro q hq
    exact ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization (Localization.AtPrime q) q.primeCompl
        q.primeCompl_le_nonZeroDivisors⟩) |>.2
  have hupper : p.height ≤ 1 :=
    height_le_one_of_mem_associatedPrimes_regular_quotient hS a
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha) p hp
  have hamem : a ∈ p := by
    apply hp.annihilator_le
    rw [Submodule.mem_annihilator]
    intro y hy
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk (Ideal.span {a}) (a * b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right b _ (Ideal.mem_span_singleton_self a)
  have hpbot : p ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hamem
    exact ha hamem
  exact le_antisymm hupper
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpbot))

end Ideal
