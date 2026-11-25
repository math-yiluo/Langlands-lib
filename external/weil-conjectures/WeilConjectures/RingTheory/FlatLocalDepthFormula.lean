/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.AnnihilatorElementFlatBaseChange
import WeilConjectures.RingTheory.DepthLeSupportDimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.FlatLocalDepthReduction
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Depth formula for a flat local homomorphism

Source: Stacks Project, Algebra, Lemma 10.163.2 (Tag 0337), the ring case of
Lemma 10.163.1 (Tag 0338; EGA IV, Proposition 6.3.1)
(blueprint: lem-weil-pbc-flat-local-depth-formula).
-/

@[expose] public section

universe u v

namespace IsLocalRing

private theorem depth_ne_top (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : depth (R := A) A ≠ ⊤ := by
  have h := depth_le_supportDim (R := A) A
  rw [Module.supportDim_self_eq_ringKrullDim] at h
  intro ht
  rw [ht] at h
  exact ringKrullDim_ne_top (R := A) (top_le_iff.mp h)

private theorem exists_annihilator_of_depth_zero (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hd : depth (R := A) A = 0) :
    ∃ z : A, ∀ a : A, a * z = 0 ↔ a ∈ maximalIdeal A := by
  have hm : maximalIdeal A ∈ associatedPrimes A A := by
    by_contra hm
    obtain ⟨x, hx, hreg⟩ := exists_mem_maximalIdeal_smul_injective A A hm
    have hmem : ∀ a ∈ ([x] : List A), a ∈ maximalIdeal A := by simpa using hx
    have hseq : RingTheory.Sequence.IsRegular A [x] :=
      (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
        (RingTheory.Sequence.IsWeaklyRegular.cons hreg
          (RingTheory.Sequence.IsWeaklyRegular.nil A (QuotSMulTop x A)))
    have hlen : (1 : ℕ∞) ≤ depth (R := A) A := by
      unfold depth Ideal.depth
      split_ifs with h
      · exact le_top
      · apply le_sSup
        exact ⟨[x], hseq, hmem, by simp⟩
    rw [hd] at hlen
    exact (by decide : ¬ (1 : ℕ∞) ≤ 0) hlen
  obtain ⟨_, z, hz⟩ := (isAssociatedPrime_iff.mp hm)
  refine ⟨z, fun a ↦ ?_⟩
  rw [hz]
  simp [Submodule.mem_colon_singleton, smul_eq_mul]

private theorem depth_zero_of_annihilator (A : Type*) [CommRing A] [IsLocalRing A]
    (z : A) (hz : ∀ a : A, a * z = 0 ↔ a ∈ maximalIdeal A) :
    depth (R := A) A = 0 := by
  have hzne : z ≠ 0 := by
    intro h
    have : (1 : A) ∈ maximalIdeal A := (hz 1).mp (by simp [h])
    exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  unfold depth Ideal.depth
  have hm : (maximalIdeal A • (⊤ : Submodule A A)) ≠ ⊤ := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using (maximalIdeal.isMaximal A).ne_top
  rw [ite_eq_right hm]
  apply le_antisymm _ zero_le
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  cases rs with
  | nil => simp
  | cons x xs =>
    have hinj := ((RingTheory.Sequence.isRegular_cons_iff A x xs).mp hreg).1
    have hxz : x • z = 0 := (hz x).mpr (hmem x (by simp))
    exact (hzne (hinj (hxz.trans (smul_zero x).symm))).elim

private theorem depth_zero_of_flat_local {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ] (hflat : φ.Flat)
    [IsLocalRing (B ⧸ (maximalIdeal A).map φ)]
    (hA : depth (R := A) A = 0)
    (hF : depth (R := B ⧸ (maximalIdeal A).map φ)
      (B ⧸ (maximalIdeal A).map φ) = 0) : depth (R := B) B = 0 := by
  let I := (maximalIdeal A).map φ
  obtain ⟨z, hz⟩ := exists_annihilator_of_depth_zero A hA
  obtain ⟨ybar, hy⟩ := exists_annihilator_of_depth_zero (B ⧸ I) hF
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  have hann : Module.annihilator B (Ideal.span ({φ z} : Set B)) = I := by
    rw [φ.annihilator_element_flat_base_change hflat z]
    congr 1
    ext a
    change a ∈ (Ideal.span ({z} : Set A)).annihilator ↔ a ∈ maximalIdeal A
    simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using hz a
  apply depth_zero_of_annihilator B (φ z * y)
  intro b
  calc
    b * (φ z * y) = 0 ↔ b * y ∈ I := by
      rw [← hann]
      change b * (φ z * y) = 0 ↔ b * y ∈ (Ideal.span ({φ z} : Set B)).annihilator
      rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
      rw [show b * (φ z * y) = (b * y) * φ z by ring]
    _ ↔ Ideal.Quotient.mk I b * Ideal.Quotient.mk I y = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    _ ↔ Ideal.Quotient.mk I b ∈ maximalIdeal (B ⧸ I) := hy _
    _ ↔ b ∈ maximalIdeal B := by
      have : IsLocalHom (Ideal.Quotient.mk I) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      change b ∈ (maximalIdeal (B ⧸ I)).comap (Ideal.Quotient.mk I) ↔ _
      rw [maximalIdeal_comap]

private theorem depth_eq_nat_of_flat_local (n : ℕ) :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
      (φ : A →+* B) [IsLocalHom φ] (_hflat : φ.Flat)
      [IsLocalRing (B ⧸ (maximalIdeal A).map φ)],
      depth (R := A) A + depth (R := B ⧸ (maximalIdeal A).map φ)
        (B ⧸ (maximalIdeal A).map φ) = (n : ℕ∞) → depth (R := B) B = (n : ℕ∞) := by
  induction n with
  | zero =>
    intro A B _ _ _ _ _ _ φ _ hflat _ hn
    obtain ⟨hA, hF⟩ := add_eq_zero.mp hn
    exact depth_zero_of_flat_local φ hflat hA hF
  | succ n ih =>
    intro A B _ _ _ _ _ _ φ _ hflat _ hn
    have hpos : 0 < depth (R := A) A +
        depth (R := B ⧸ (maximalIdeal A).map φ) (B ⧸ (maximalIdeal A).map φ) := by
      rw [hn]
      exact_mod_cast Nat.succ_pos n
    obtain ⟨J, K, hJ, hK, hred⟩ := exists_depth_reducing_flat_local_quotients φ hflat hpos
    let : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hJ)
    let : Nontrivial (B ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hK)
    let : IsLocalRing (A ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let : IsLocalRing (B ⧸ K) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
    obtain ⟨ψ, hψ, hflat', hF, _, hB, hsum⟩ := hred
    let := hψ
    let := hF
    have hsum' : depth (R := A ⧸ J) (A ⧸ J) +
        depth (R := (B ⧸ K) ⧸ (maximalIdeal (A ⧸ J)).map ψ)
          ((B ⧸ K) ⧸ (maximalIdeal (A ⧸ J)).map ψ) = (n : ℕ∞) := by
      apply ENat.add_left_injective_of_ne_top (show (1 : ℕ∞) ≠ ⊤ by simp)
      simpa only [Nat.cast_succ] using hsum.symm.trans hn
    rw [hB, ih ψ hflat' hsum']
    simp only [Nat.cast_succ]

/-- A flat local homomorphism of Noetherian local rings has a Noetherian local closed
fibre, with maximal ideal the image of the target's maximal ideal, and the depth of
its target is the sum of the depths of its source and closed fibre.
Source: Stacks Project, Algebra, Tags 0337 and 0338
(blueprint: lem-weil-pbc-flat-local-depth-formula).

Proof (Tag 0338, specialized to M = R and N = S, following the node's nine steps):
1. Locality puts m_R S inside m_S. The quotient-local-structure lemma makes the
   closed fibre a nonzero local ring with maximal ideal m_S / m_R S. The
   finite-algebra-noetherian lemma makes it Noetherian. The depth-le-support-dimension
   and noetherian-local-finite-krull-dimension lemmas make all three depths finite.
2. Induct on n = depth(R) + depth(S / m_R S), uniformly over flat local maps.
3. In depth zero, nonzerodivisor-if-maximal-not-associated gives an element whose
   annihilator is the maximal ideal: otherwise a nonzerodivisor in that ideal
   would be a regular sequence of length one, contradicting the definition of depth.
4. For n = 0, choose z in R annihilated exactly by m_R and a lift y in S of an
   element of the fibre annihilated exactly by its maximal ideal. By
   annihilator-element-flat-base-change, Ann_S(phi(z)) = m_R S. Thus phi(z)y
   has annihilator m_S, and no element of m_S can start a regular sequence on S.
5. If the fibre has positive depth, lift a fibre nonzerodivisor to f in m_S.
   The flat-mod-injective lemma says f is a nonzerodivisor on S and S/fS is flat
   over R. Its closed fibre is the original fibre modulo the class of f.
6. By depth-drops-by-one and depth-over-quotient-ring, the new fibre has depth
   one less. Apply induction to R -> S/fS and the same depth lemmas to S to
   recover depth(S) = n.
7. If the fibre has depth zero and n > 0, choose a nonzerodivisor f in m_R.
   Flat base change makes phi(f) a nonzerodivisor on S. The quotient-local-structure,
   finite-algebra-noetherian and flat-module-quotient-flat lemmas make
   R/fR -> S/phi(f)S a flat local map of Noetherian local rings with the same fibre.
8. By depth-drops-by-one and depth-over-quotient-ring, the source depth drops by
   one. Induction computes the target quotient depth as n - 1; the same depth
   lemmas then compute depth(S) = n.
9. These two cases complete the induction, proving the displayed depth equality.
   The addition is in the extended natural numbers, with infinity absorbing. -/
theorem depth_eq_add_of_flat_local {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat) :
    let I : Ideal S := (maximalIdeal R).map φ
    IsNoetherianRing (S ⧸ I) ∧
      ∃ hlocal : IsLocalRing (S ⧸ I),
        letI := hlocal
        (maximalIdeal S).map (Ideal.Quotient.mk I) = maximalIdeal (S ⧸ I) ∧
          depth (R := S) S = depth (R := R) R + depth (R := S ⧸ I) (S ⧸ I) := by
  let I : Ideal S := (maximalIdeal R).map φ
  let : Nontrivial (S ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top φ).ne
  let : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · exact map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  · obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (depth_ne_top R)
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (depth_ne_top (S ⧸ I))
    have hn : depth (R := R) R + depth (R := S ⧸ I) (S ⧸ I) = ((a + b : ℕ) : ℕ∞) := by
      rw [← ha, ← hb, Nat.cast_add]
    exact (depth_eq_nat_of_flat_local (a + b) φ hflat hn).trans hn.symm

end IsLocalRing
