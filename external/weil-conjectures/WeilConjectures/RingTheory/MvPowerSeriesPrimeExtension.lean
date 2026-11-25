/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# Prime ideals extended to a power-series ring

Source: Stacks Project, Tags 0312 and 0EY9, coefficientwise quotient argument.
(blueprint: lem-sbc-power-series-prime-extension)
-/

@[expose] public section

universe u
namespace MvPowerSeries

private theorem mem_map_C_of_coeff_mem_span
    {A : Type u} [CommRing A] {σ : Type*} (t : Finset A)
    (f : MvPowerSeries σ A) (hf : ∀ n, coeff n f ∈ Ideal.span (t : Set A)) :
    f ∈ (Ideal.span (t : Set A)).map (C (σ := σ)) := by
  classical
  induction t using Finset.induction_on generalizing f with
  | empty =>
    have heq : f = 0 := by
      ext n
      simpa using hf n
    simp [heq]
  | @insert a t ha ih =>
    have hex : ∀ n, ∃ b, ∃ c ∈ Ideal.span (t : Set A), coeff n f = b * a + c := by
      intro n
      apply Ideal.mem_span_insert.mp
      simpa only [Finset.coe_insert] using hf n
    choose b c hc hfc using hex
    let g : MvPowerSeries σ A := b
    let k : MvPowerSeries σ A := c
    have heq : f = C a * g + k := by
      ext n
      rw [map_add, coeff_C_mul]
      change f n = a * b n + c n
      simpa only [coeff_apply, mul_comm] using hfc n
    rw [heq]
    apply Ideal.add_mem
    · apply Ideal.mul_mem_right
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
    · exact (Ideal.map_mono (Ideal.span_mono (by simp))) (ih k hc)

/-- Extending a prime ideal from a Noetherian coefficient ring to finitely many
power-series variables gives a prime ideal.

Source: Stacks Project, Tags 0312 and 0EY9, the coefficientwise quotient
argument in the associated-prime calculation.
(blueprint: lem-sbc-power-series-prime-extension)

Proof: Reduce coefficients modulo p. This is a surjective ring homomorphism
onto the power-series ring over A/p: choose a lift of each coefficient.
Its kernel consists of series all of whose coefficients lie in p.
Choose finitely many generators a_1,...,a_r of p, possible by Noetherianity.
For each coefficient choose its expression as a sum of a_i times scalars.
For every i the scalars form a power series f_i. The original series is
sum_i C(a_i)*f_i by coefficient extensionality. Thus the kernel is exactly
p.map C. The target is a domain, since A/p is a domain, so the kernel is prime.
For d=0 the coefficient reduction is the ordinary quotient map. The zero ring
has no prime ideal, and p=bot in a domain gives the domain power-series ring. -/
theorem isPrime_map_C (A : Type u) [CommRing A] [IsNoetherianRing A]
    (d : ℕ) (p : Ideal A) (hp : p.IsPrime) :
    (p.map (C (σ := Fin d))).IsPrime := by
  let : p.IsPrime := hp
  let : IsDomain (MvPowerSeries (Fin d) (A ⧸ p)) := NoZeroDivisors.to_isDomain _
  let f := map (σ := Fin d) (Ideal.Quotient.mk p)
  have hker : RingHom.ker f = p.map (C (σ := Fin d)) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨t, ht⟩ := p.fg_of_isNoetherianRing
      have hcoeff : ∀ n, coeff n g ∈ Ideal.span (t : Set A) := by
        intro n
        rw [ht]
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have h := congrArg (coeff n) hg
        simpa only [f, coeff_map, map_zero] using h
      rw [← ht]
      exact mem_map_C_of_coeff_mem_span t g hcoeff
    · apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change f (C a) = 0
      simp only [f, map_C, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  rw [← hker]
  exact RingHom.ker_isPrime f

end MvPowerSeries
