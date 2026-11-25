/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import WeilConjectures.RingTheory.AssociatedPrimePowerQuotient
import WeilConjectures.RingTheory.DepthQuotSMulTop
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Nakayama

/-!
# Depth is bounded by the dimension at an associated prime

Source: Stacks Project, Algebra, Lemma Tag 0BK4 (lemma-depth-dim-associated-primes),
lines 17985-18020; associated primes Definition Tag 00LA (blueprint:
lem-weil-pbc-depth-le-dim-associated-prime).
-/

@[expose] public section

universe u v

namespace IsLocalRing

private theorem depth_eq_zero_of_maximal_associated
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hm : maximalIdeal R ∈ associatedPrimes R M) : depth (R := R) M = 0 := by
  have hM : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  rw [depth, Ideal.depth, ite_eq_right hM]
  apply le_antisymm _ zero_le
  apply sSup_le
  rintro n ⟨rs, hrs, hmem, rfl⟩
  cases rs with
  | nil => simp
  | cons x xs =>
    have hxreg := ((RingTheory.Sequence.isRegular_cons_iff M x xs).mp hrs).1
    have hx : x ∈ maximalIdeal R := hmem x (by simp)
    have hunion : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) :=
      Set.mem_iUnion.mpr ⟨maximalIdeal R, Set.mem_iUnion.mpr ⟨hm, hx⟩⟩
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at hunion
    exact False.elim (hunion hxreg)

/-- For a finite module over a Noetherian local ring, the depth is at most the
Krull dimension of the quotient by every associated prime. Since `R` is Noetherian,
Mathlib's `associatedPrimes R M` are exactly the primes `p = Ann_R(z)` for some `z : M`
(`isAssociatedPrime_iff`), the node's notion (Stacks 00LA). Source: Stacks Project,
Algebra, Tag 0BK4 (blueprint: lem-weil-pbc-depth-le-dim-associated-prime).

Proof, following the induction of Stacks Tag 0BK4:
1. An associated prime forces the module to be nonzero. Nakayama makes the
   maximal-ideal multiple proper, so depth is the supremum of regular-sequence lengths.
2. If the maximal ideal is associated, every element of it is a zerodivisor;
   a regular sequence in it must be empty, and depth is zero.
3. Otherwise choose a regular element in the maximal ideal. The depth-drop theorem
   gives finite positive depth. Induct on this integer, uniformly over finite modules.
4. At positive depth choose a regular element x in the maximal ideal; the
   union-of-associated-primes characterization gives x outside the associated prime p.
5. Choose any minimal prime q over p + (x), contained in the maximal ideal.
   The associated-prime power-quotient theorem makes q associated to M/x^n M
   for some positive n. The power is regular, so this quotient has depth one less.
6. Apply induction to the quotient and q. The map R/p onto R/q kills the nonzero
   image of x, a nonzerodivisor in the domain R/p. Mathlib's dimension inequality
   for such a surjection gives dim(R/q) + 1 ≤ dim(R/p), completing induction.
   This inequality suffices; no minimal prime attaining a maximal dimension is needed.
-/
theorem depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    (IsLocalRing.depth (R := R) M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  have hnt : Nontrivial M := by
    by_contra h
    let : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
    exact (not_isAssociatedPrime_of_subsingleton (I := p) (M := M)) hp
  let : Nontrivial M := hnt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, depth (R := R) M = (d : ℕ∞) := by
    by_cases hm : maximalIdeal R ∈ associatedPrimes R M
    · exact ⟨0, depth_eq_zero_of_maximal_associated M hm⟩
    · obtain ⟨x, hx, hreg⟩ := exists_mem_maximalIdeal_smul_injective R M hm
      obtain ⟨_, d, _, hd, _⟩ := depth_quotSMulTop_of_isSMulRegular M x hx hreg
      exact ⟨d, hd⟩
  have hind : ∀ (d : ℕ) (N : Type v) [AddCommGroup N] [Module R N]
      [Module.Finite R N] [Nontrivial N], depth (R := R) N = (d : ℕ∞) →
      ∀ (p : Ideal R), p ∈ associatedPrimes R N →
        (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
    intro d
    induction d with
    | zero =>
      intro N _ _ _ _ hdep p hp
      let : p.IsPrime := hp.isPrime
      exact ringKrullDim_nonneg_of_nontrivial
    | succ d ih =>
      intro N _ _ _ _ hdep p hp
      have hm : maximalIdeal R ∉ associatedPrimes R N := by
        intro hm
        have hz := depth_eq_zero_of_maximal_associated N hm
        rw [hdep] at hz
        simp at hz
      obtain ⟨x, hx, hreg⟩ := exists_mem_maximalIdeal_smul_injective R N hm
      have hxp : x ∉ p := by
        intro hxp
        have hunion : x ∈ ⋃ p ∈ associatedPrimes R N, (p : Set R) :=
          Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hxp⟩⟩
        rw [biUnion_associatedPrimes_eq_compl_regular R N] at hunion
        exact hunion hreg
      have hpm : p ≤ maximalIdeal R := le_maximalIdeal hp.isPrime.ne_top
      obtain ⟨q, hq, _⟩ := Ideal.exists_minimalPrimes_le
        (J := maximalIdeal R) (sup_le hpm ((Ideal.span_singleton_le_iff_mem _).mpr hx))
      obtain ⟨n, hn, hqa⟩ := Module.exists_mem_associatedPrimes_quotient_pow x hx p q hp hq
      have hxpow : x ^ n ∈ maximalIdeal R := Ideal.pow_mem_of_mem _ hx n (by omega)
      obtain ⟨hntq, e, he, hde, hqe⟩ :=
        depth_quotSMulTop_of_isSMulRegular N (x ^ n) hxpow (hreg.pow n)
      let : Nontrivial (QuotSMulTop (x ^ n) N) := hntq
      have hed : e = d + 1 := by
        rw [hdep] at hde
        exact_mod_cast hde.symm
      have hqd : depth (R := R) (QuotSMulTop (x ^ n) N) = (d : ℕ∞) := by
        simpa [hed] using hqe
      have hi := ih (QuotSMulTop (x ^ n) N) hqd q hqa
      have hpq : p ≤ q := le_sup_left.trans hq.1.2
      have hxq : x ∈ q :=
        hq.1.2 ((show Ideal.span {x} ≤ p ⊔ Ideal.span {x} from le_sup_right)
          (Ideal.subset_span (by simp)))
      let : p.IsPrime := hp.isPrime
      have hdimpq : ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
        apply ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq)
          (Ideal.Quotient.factor_surjective hpq)
          (r := Ideal.Quotient.mk p x)
        · exact mem_nonZeroDivisors_iff_ne_zero.mpr
            (fun heq ↦ hxp (Ideal.Quotient.eq_zero_iff_mem.mp heq))
        · simpa only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using hxq
      calc
        ((d + 1 : ℕ) : WithBot ℕ∞) = (d : WithBot ℕ∞) + 1 := by simp
        _ ≤ ringKrullDim (R ⧸ q) + 1 := by simpa only [add_comm] using add_le_add_right hi 1
        _ ≤ ringKrullDim (R ⧸ p) := hdimpq
  rw [hd]
  exact hind d M hd p hp

end IsLocalRing
