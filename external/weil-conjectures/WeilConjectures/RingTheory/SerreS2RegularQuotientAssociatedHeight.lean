/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SerreConditions
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.KrullDimension.Field
import WeilConjectures.RingTheory.DepthQuotSMulTop
import WeilConjectures.RingTheory.DepthLeDimAssociatedPrime

/-!
# Associated primes of a regular principal quotient in an S2 ring

Source: Stacks Project, Algebra, Tag 031T, proof of (1), using only S2 and regularity
of the denominator (the normal-domain hypothesis is not used after obtaining S2).
(blueprint: lem-weil-pbc-serre-s2-regular-quotient-associated-height).
-/

@[expose] public section

universe u

open scoped Pointwise

open Module.associatedPrimes

/-- Associated primes of a quotient by a nonzerodivisor in an S2 Noetherian ring
have height at most one.
Source: Stacks Project, Algebra, Tag 031T, proof of (1), using only S2
(blueprint: lem-weil-pbc-serre-s2-regular-quotient-associated-height).

Proof: An associated prime p of R/bR contains b, since b annihilates the whole quotient.
Localization of associated primes (Tag 0310) makes the maximal ideal of A = R_p
associated to the localized quotient, canonically A/(b/1). Thus the associated-prime
depth bound (Tag 0BK4) bounds its depth by the dimension of A/m, which is zero.
The image of b is regular: if (b/1)(a/s) = 0, a multiplier outside p kills ba,
and regularity of b forces that multiplier to kill a. It lies in m and A is nonzero.
The regular-element depth formula (Tag 090R) therefore gives depth(A) = 1.
Condition S2 at p then gives min(2,height(p)) ≤ 1, which forces height(p) ≤ 1.
A unit b gives the zero quotient and no associated primes, so this edge case is vacuous.
No reducedness, domain property, or integral closedness is required. -/
theorem Ideal.height_le_one_of_mem_associatedPrimes_regular_quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hS : Ring.IsSerreS R 2)
    (b : R) (hb : b ∈ nonZeroDivisors R) (p : Ideal R)
    (hp : p ∈ associatedPrimes R (R ⧸ Ideal.span {b})) :
    p.height ≤ (1 : ℕ∞)  := by
  let := hp.isPrime
  let A := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal A
  let f : R →ₗ[R] A := Algebra.linearMap R A
  let I := Ideal.span {b}
  let J := I.localized' A p.primeCompl f
  let Q := A ⧸ J
  have hass : m ∈ associatedPrimes A Q := by
    apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      p.primeCompl (I.toLocalizedQuotient' A p.primeCompl f)
    simpa [m, A, Localization.AtPrime.under_maximalIdeal] using hp
  have hbmem : b ∈ p := by
    apply hp.annihilator_le
    rw [Submodule.mem_annihilator]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk I (b * a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right a _ (Ideal.subset_span (Set.mem_singleton b))
  have hbmax : algebraMap R A b ∈ m := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p b).mpr hbmem
  have hreg : IsSMulRegular A (algebraMap R A b) := by
    have hb' := IsLocalization.nonZeroDivisors_le_comap (M := p.primeCompl) (S := A) hb
    exact (isRegular_iff_mem_nonZeroDivisors.mpr hb').1.isSMulRegular
  have hJ : J = algebraMap R A b • (⊤ : Submodule A A) := by
    dsimp [J, I, f]
    rw [Submodule.localized'_span]
    simp only [Set.image_singleton, Algebra.linearMap_apply]
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  have hdepthQ : IsLocalRing.depth (R := A) Q = 0 := by
    have hbound := IsLocalRing.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes m hass
    let hfield : Field (A ⧸ m) := Ideal.Quotient.field m
    rw [ringKrullDim_eq_zero_of_field] at hbound
    exact WithBot.coe_le_coe.mp hbound |>.antisymm (zero_le)
  have hdrop := IsLocalRing.depth_quotSMulTop_of_isSMulRegular A
    (algebraMap R A b) hbmax hreg
  obtain ⟨_, d, hd, hdepth, hquot⟩ := hdrop
  have hquotzero : ((d - 1 : ℕ) : ℕ∞) = 0 := by
    rw [← hquot]
    change IsLocalRing.depth (R := A) (A ⧸ J) = 0 at hdepthQ
    rw [hJ] at hdepthQ
    exact hdepthQ
  have hd1 : d = 1 := by
    have : d - 1 = 0 := by exact_mod_cast hquotzero
    omega
  have hmin : min (2 : ℕ∞) p.height ≤ 1 := by
    have h := hS p
    rw [hdepth, hd1] at h
    exact h
  by_contra hheight
  have htwo : (2 : ℕ∞) ≤ p.height := by
    have h := (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
      (lt_of_not_ge hheight)
    norm_num at h ⊢
    exact h
  rw [min_eq_left htwo] at hmin
  norm_num at hmin

