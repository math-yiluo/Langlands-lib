/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# A normal ring is integrally closed in its total ring of fractions

Source: Stacks Project, Algebra, Lemma Tag 034M
(blueprint: lem-weil-pbc-normal-ring-integrally-closed-total).

`FractionRing R` is `Localization (nonZeroDivisors R)`, also for rings with zero divisors.
This is the ring specialization of the module localization in
`def-weil-pbc-module-localization`: `Localization S` and `LocalizedModule S R` are
reducibly the same fraction construction. No domain assumption on `R` is made.
-/

@[expose] public section

universe u

/-- Every integral total fraction of a normal commutative ring comes from the ring.
Source: Stacks Project, Algebra, Lemma Tag 034M
(blueprint: lem-weil-pbc-normal-ring-integrally-closed-total).

Proof (the three steps of the node):
1. Write `x = a/s` with `s` a nonzerodivisor, using
   `def-weil-pbc-module-localization`. The map into the total fraction ring is injective.
   For any prime `p`, `s/1` is nonzero in `R_p`: otherwise some `t` outside `p` has
   `ts = 0`, contradicting regularity of `s`. Map the integral equation for `x`
   (`def-weil-pbc-integral-closure`) into the fraction field of `R_p`
   (`def-weil-pbc-localization-at-prime`).
2. Normality (`def-weil-pbc-normal-ring`) puts this fraction in `R_p`, say `b/f`
   with `f` outside `p`. Clear denominators: some `t` outside `p` satisfies
   `t(fa - bs) = 0`. Thus `(tf)x = tb` in the total fraction ring, and `tf` is
   outside `p`. The ideal `I = {r | rx lies in the image of R}` therefore has an
   element outside each prime ideal.
3. If `I` were proper, `lem-weil-pbc-proper-ideal-contained-in-maximal` would put
   it in a maximal, hence prime, ideal, a contradiction. Thus `1` belongs to `I`,
   so `x` belongs to the image of `R`.
-/
theorem integral_totalFraction_mem_range_of_normal
    (R : Type u) [CommRing R]
    (hnormal : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (x : FractionRing R) (hx : IsIntegral R x) :
    ∃ r : R, algebraMap R (FractionRing R) r = x := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have ha : a ∈ Ideal.span ({(s : R)} : Set R) := by
    apply Ideal.mem_of_localization_maximal
    intro p hp
    let : p.IsMaximal := hp
    let A := Localization.AtPrime p
    let K := FractionRing A
    let : IsDomain A := (hnormal p).1
    let : IsIntegrallyClosed A := (hnormal p).2
    let g : R →ₐ[R] K := Algebra.ofId R K
    have hu : ∀ t : nonZeroDivisors R, IsUnit (g t) := by
      intro t
      have ht : algebraMap R A t ∈ nonZeroDivisors A :=
        IsLocalization.nonZeroDivisors_le_comap p.primeCompl A t.2
      simpa only [g, Algebra.ofId_apply, IsScalarTower.algebraMap_apply R A K] using
        IsLocalization.map_units K (⟨algebraMap R A t, ht⟩ : nonZeroDivisors A)
    let f : FractionRing R →ₐ[R] K := IsLocalization.liftAlgHom hu
    have hi : IsIntegral A (f (IsLocalization.mk' (FractionRing R) a s)) :=
      (hx.map f).tower_top
    obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff K).mp inferInstance hi
    have he : algebraMap R A a = b * algebraMap R A s := by
      apply IsFractionRing.injective A K
      have hs := congrArg f (IsLocalization.mk'_spec (FractionRing R) a s)
      simpa only [map_mul, AlgHom.commutes, ← hb, g,
        IsScalarTower.algebraMap_apply R A K, map_mul] using hs.symm
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨b, he.trans (mul_comm _ _)⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨r, IsLocalization.eq_mk'_of_mul_eq ?_⟩
  exact (mul_comm _ _).trans hr.symm
