/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# A conductor power for a finite intermediate ring

Source: Stacks Project, Varieties, Lemma 33.37.5 (Tag 09N2), finite-conductor paragraph
(blueprint: lem-sc-finite-integral-conductor).
-/

@[expose] public section

universe u v

namespace Subalgebra

/-- A finite intermediate algebra in the fraction field of a Noetherian semilocal domain of
Krull dimension one contains the product of a positive power of the base ring's Jacobson radical
with the intermediate algebra. Membership in the base ring is expressed through its algebra map.
Source: Stacks Project, Varieties, Lemma 33.37.5 (Tag 09N2), finite-conductor paragraph
(blueprint: lem-sc-finite-integral-conductor).

Proof: (1) By `FractionalIdeal.isFractional_of_fg`, the finite submodule `A` of the fraction
field has a common denominator `d ≠ 0`: every `d * a` is in the image of `B`.
(2) Every prime containing `(d)` is nonzero, hence maximal by dimension one. Thus the
intersection of all maximal ideals is contained in the intersection of the primes containing
`(d)`, namely its radical. The Jacobson radical is finitely generated since `B` is Noetherian,
so `Ideal.exists_pow_le_of_le_radical_of_fg` gives a power contained in `(d)`. Increasing the
exponent by one makes it positive and preserves containment.
(3) Write any element `b` of this power as `r * d`. If `d * a` is the image of `c`, then
`b * a` is the image of `r * c`. -/
theorem exists_jacobson_pow_mul_mem_base
    {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    {K : Type v} [Field K] [Algebra B K] [IsFractionRing B K]
    (A : Subalgebra B K) [Module.Finite B A] [IsFractionRing A K] :
    ∃ n : ℕ, 0 < n ∧ ∀ b : B, b ∈ (Ideal.jacobson (⊥ : Ideal B)) ^ n →
      ∀ a : A, ∃ c : B, algebraMap B K c = algebraMap B K b * (a : K) := by
  have : Ring.KrullDimLE 1 B := (Ring.krullDimLE_iff).mpr (by simp [hdim])
  have hfg : A.toSubmodule.FG := Submodule.FG.of_finite
  obtain ⟨d, hd, hden⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors B) hfg
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hrad : Ideal.jacobson (⊥ : Ideal B) ≤ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP ↦ ?_
    have hP0 : P ≠ ⊥ := by
      intro heq
      have hdP := hP.1 (Ideal.mem_span_singleton_self d)
      rw [heq, Ideal.mem_bot] at hdP
      exact hd0 hdP
    exact sInf_le ⟨bot_le, hP.2.isMaximal_of_ne_bot hP0⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian _)
  refine ⟨n + 1, Nat.succ_pos _, fun b hb a ↦ ?_⟩
  have hb' : b ∈ Ideal.span {d} := hn (Ideal.pow_le_pow_right (Nat.le_succ n) hb)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb'
  obtain ⟨c, hc⟩ := hden (a : K) a.property
  refine ⟨r * c, ?_⟩
  rw [map_mul, hc, Algebra.smul_def, ← mul_assoc, ← map_mul, hr]

end Subalgebra
