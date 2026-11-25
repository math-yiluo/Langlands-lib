/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.Prime

import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Unique primes in a finite purely inseparable integral extension

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07PR
(blueprint: lem-weil-pbc-purely-inseparable-integral-prime-unique).
-/

@[expose] public section

universe u v w x

/-- Source: Stacks Project, More on Algebra, Lemma Tag 07PR, proof, and Algebra,
Tag 0BR8 (blueprint: lem-weil-pbc-purely-inseparable-integral-prime-unique).
A finite extension of domains with normal base and finite purely inseparable fraction fields
has exactly one prime above each base prime.

Proof: First, for every `b` in `B`, pure inseparability gives a power `b^(e^n)` in `K`,
where `e` is the exponential characteristic. This power remains in `B`, hence is integral
 over `A` by finite generation (lem-weil-pbc-finite-algebra-is-integral). Its monic equation
holds in `K` because `K → L` is injective. Normality of `A`
(def-weil-pbc-normal-ring and def-weil-pbc-integral-closure) puts the power in `A`.
Second, the map `A → B` is injective and integral, so lying over
(lem-weil-pbc-integral-injective-lying-over) supplies a prime over `p`.
Third, if two primes lie over `p`, a power of any element in the first lies in `A`,
hence in `p` and the second prime. Primality puts the element itself in the second.
Exchanging the primes gives equality. In characteristic zero `e = 1`, so the same
argument applies without imposing positive characteristic. -/
theorem purelyInseparable_integral_prime_unique
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] (hA : IsIntegrallyClosed A)
    [Module.Finite A B]
    (K : Type w) (L : Type x) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra A L]
    [Algebra K L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Module.Finite K L] [IsPurelyInseparable K L]
    (p : Ideal A) [p.IsPrime] :
    ∃! q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = p := by
  have hAB : Function.Injective (algebraMap A B) := by
    intro a a' haa
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa only [← IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply A K L] using
      congrArg (algebraMap B L) haa
  have hpowers : ∀ b : B, ∃ n > 0, b ^ n ∈ (algebraMap A B).range := by
    intro b
    obtain ⟨e, he⟩ := ExpChar.exists K
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem K e (algebraMap B L b)
    have hintL : IsIntegral A (algebraMap K L c) := by
      rw [hc, ← map_pow]
      exact (IsIntegral.of_finite A (b ^ e ^ n)).map (IsScalarTower.toAlgHom A B L)
    have hintK : IsIntegral A c :=
      (isIntegral_algebraMap_iff (R := A) (A := K) (B := L)).mp hintL
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintK
    refine ⟨e ^ n, expChar_pow_pos K e n, a, ?_⟩
    apply IsFractionRing.injective B L
    rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L,
      ha, hc, map_pow]
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := B) p
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hAB]; exact bot_le)
  change q.comap (algebraMap A B) = p at hqp
  refine ⟨q, ⟨hq, hqp⟩, ?_⟩
  intro q' hq'
  apply le_antisymm
  · intro b hb
    obtain ⟨n, hn, a, ha⟩ := hpowers b
    apply (hq.pow_mem_iff_mem n hn).mp
    rw [← ha]
    change a ∈ q.comap (algebraMap A B)
    rw [hqp, ← hq'.2]
    change algebraMap A B a ∈ q'
    rw [ha]
    exact (hq'.1.pow_mem_iff_mem n hn).mpr hb
  · intro b hb
    obtain ⟨n, hn, a, ha⟩ := hpowers b
    apply (hq'.1.pow_mem_iff_mem n hn).mp
    rw [← ha]
    change a ∈ q'.comap (algebraMap A B)
    rw [hq'.2, ← hqp]
    change algebraMap A B a ∈ q
    rw [ha]
    exact (hq.pow_mem_iff_mem n hn).mpr hb
