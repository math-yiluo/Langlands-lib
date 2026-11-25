/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Colon ideals and localization

Colon ideals commute with localization when the second ideal is finitely generated
(`Ideal.map_colon_of_isLocalization`). A bound on the nilpotency index of the nilradical
passes to localizations (`nilradical_pow_eq_bot_of_isLocalization`).

A finitely generated ideal which becomes principal at a prime `p` is principal after inverting
a single element outside `p` (`Ideal.exists_notMem_mul_mem_span_singleton_of_map_eq`,
`Ideal.map_eq_span_singleton_of_mul_mem_span_singleton`).
-/

@[expose] public section

/-- **Colon ideals commute with localization** when the second ideal is finitely generated. -/
lemma Ideal.map_colon_of_isLocalization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (I J : Ideal A) (hJ : J.FG) :
    (I.colon (J : Set A)).map (algebraMap A B) =
      (I.map (algebraMap A B)).colon (J.map (algebraMap A B) : Set B) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      rw [smul_eq_mul, ← map_mul]
      exact Ideal.mem_map_of_mem _ (Submodule.mem_colon.mp ha j hj)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Ideal.mul_mem_left _ c hx
  · intro b hb
    obtain ⟨t, rfl⟩ := hJ
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M b
    have h (j : A) (hj : j ∈ t) : ∃ m ∈ M, m * (a * j) ∈ I := by
      rw [← IsLocalization.mk'_mem_map_algebraMap_iff M B I (a * j) s,
        IsLocalization.mk'_eq_mul_mk'_one,
        mul_comm a j, map_mul, mul_assoc, ← IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
      exact Submodule.mem_colon.mp hb _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hj))
    choose! m hmM hm using h
    rw [IsLocalization.mk'_mem_map_algebraMap_iff M B]
    refine ⟨∏ j ∈ t, m j, Submonoid.prod_mem M fun j hj ↦ hmM j hj, ?_⟩
    rw [Submodule.mem_colon]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      classical
      have e : (∏ j ∈ t, m j) * a * x = (∏ j ∈ t.erase x, m j) * (m x * (a * x)) := by
        rw [← Finset.mul_prod_erase t m hx]
        ring
      rw [smul_eq_mul, e]
      exact Ideal.mul_mem_left _ _ (hm x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Ideal.mul_mem_left _ c hx

/-- Spreading out from a localization at a prime: if a finitely generated ideal `I` becomes
principal in `R_p`, then there are `g ∉ p` and `b ∈ I` such that `b` generates `I R_p` and
`g • I ⊆ (b)`; in particular `b` generates `I` after inverting `g`. -/
theorem Ideal.exists_notMem_mul_mem_span_singleton_of_map_eq {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime S p] (I : Ideal R) (f : S)
    (hf : I.map (algebraMap R S) = Ideal.span {f}) :
    ∃ g ∉ p, ∃ b ∈ I, I.map (algebraMap R S) = Ideal.span {algebraMap R S b} ∧
      ∀ i ∈ I, g * i ∈ Ideal.span {b} := by
  classical
  have hfI : f ∈ I.map (algebraMap R S) := hf ▸ Ideal.mem_span_singleton_self f
  obtain ⟨⟨⟨b, hbI⟩, s⟩, hbm⟩ :=
    (IsLocalization.mem_map_algebraMap_iff p.primeCompl S).mp hfI
  have hspan : I.map (algebraMap R S) = Ideal.span {algebraMap R S b} := by
    rw [hf, ← hbm, Ideal.span_singleton_mul_right_unit (IsLocalization.map_units S s)]
  have hmem (i : R) (hi : i ∈ I) : ∃ m ∈ p.primeCompl, m * i ∈ Ideal.span {b} := by
    have : algebraMap R S i ∈ (Ideal.span {b}).map (algebraMap R S) := by
      rw [Ideal.map_span, Set.image_singleton, ← hspan]
      exact Ideal.mem_map_of_mem _ hi
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S _ _).mp this
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian I : I.FG)
  choose! m hm hmi using hmem
  refine ⟨∏ i ∈ t, m i, ?_, b, hbI, hspan, ?_⟩
  · exact p.primeCompl.prod_mem fun i hi ↦ hm i (ht ▸ Ideal.subset_span hi)
  · intro i hi
    have key : Ideal.span (t : Set R) ≤ (Ideal.span {b}).colon {∏ i ∈ t, m i} := by
      refine Ideal.span_le.mpr fun j hj ↦ ?_
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul,
        mul_comm, ← Finset.prod_erase_mul t m hj, mul_assoc]
      exact Ideal.mul_mem_left _ _ (hmi j (ht ▸ Ideal.subset_span hj))
    rw [← ht] at hi
    rw [mul_comm, ← smul_eq_mul, ← Submodule.mem_colon_singleton]
    exact key hi

/-- If `b ∈ I` and `g • I ⊆ (b)`, then `I` is generated by `b` after inverting `g`. -/
theorem Ideal.map_eq_span_singleton_of_mul_mem_span_singleton {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (g : R) [IsLocalization.Away g S] {I : Ideal R} {b : R}
    (hb : b ∈ I) (h : ∀ i ∈ I, g * i ∈ Ideal.span {b}) :
    I.map (algebraMap R S) = Ideal.span {algebraMap R S b} := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun i hi ↦ ?_)
    ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hb))
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (h i hi)
  refine ((IsLocalization.Away.algebraMap_isUnit g).dvd_mul_left).mp ⟨algebraMap R S c, ?_⟩
  rw [← map_mul, hc, map_mul]

/-- The nilradical of a localization of `A` is the extension of the nilradical of `A`, so a bound
`nilradical A ^ N = ⊥` on the nilpotency index passes to localizations. -/
theorem nilradical_pow_eq_bot_of_isLocalization {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S] {N : ℕ}
    (h : nilradical A ^ N = ⊥) : nilradical S ^ N = ⊥ := by
  have : nilradical S = (nilradical A).map (algebraMap A S) := by
    rw [nilradical, nilradical, IsLocalization.map_radical M]
    simp
  rw [this, ← Ideal.map_pow, h, Ideal.map_bot]
