/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Prime

/-!
# Graded prime avoidance

Source: Stacks Project, Algebra, Lemma 10.57.6 (Tag 00JS, `algebra-lemma-graded-silly`)
(blueprint: lem-sc-graded-prime-avoidance).
-/

@[expose] public section

universe u v

namespace HomogeneousIdeal

-- A homogeneous ideal contains every homogeneous component of each of its elements.
private theorem exists_homogeneous_mem_notMem
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (I J : HomogeneousIdeal 𝒜) (hIJ : ¬ I ≤ J) :
    ∃ n : ℕ, ∃ x : A, x ∈ 𝒜 n ∧ x ∈ I ∧ x ∉ J := by
  classical
  obtain ⟨a, ha, haj⟩ := IsConcreteLE.not_le_iff_exists.mp hIJ
  have h : ∃ n, (DirectSum.decompose 𝒜 a n : A) ∉ J := by
    by_contra! h
    exact haj (J.isHomogeneous.mem_iff.mpr h)
  obtain ⟨n, hn⟩ := h
  exact ⟨n, _, SetLike.coe_mem _, I.isHomogeneous n ha, hn⟩

-- A nonzero homogeneous element in the irrelevant ideal cannot have degree zero.
private theorem exists_positive_homogeneous_mem_notMem
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (I J : HomogeneousIdeal 𝒜)
    (hI : I ≤ irrelevant 𝒜) (hIJ : ¬ I ≤ J) :
    ∃ n : ℕ, 0 < n ∧ ∃ x : A, x ∈ 𝒜 n ∧ x ∈ I ∧ x ∉ J := by
  obtain ⟨n, x, hx, hxi, hxj⟩ := exists_homogeneous_mem_notMem 𝒜 I J hIJ
  refine ⟨n, Nat.pos_of_ne_zero ?_, x, hx, hxi, hxj⟩
  intro hn
  subst n
  have hz : (DirectSum.decompose 𝒜 x 0 : A) = 0 := hI hxi
  rw [DirectSum.decompose_of_mem_same 𝒜 hx] at hz
  exact hxj (hz ▸ zero_mem J)

-- Strong induction, choosing a minimal prime to avoid a separate antichain reduction.
private theorem exists_positive_homogeneous_mem_notMem_finset
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (s : Finset (HomogeneousIdeal 𝒜))
    (hp : ∀ p ∈ s, p.toIdeal.IsPrime) (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ irrelevant 𝒜) (hIp : ∀ p ∈ s, ¬ I ≤ p) :
    ∃ n : ℕ, 0 < n ∧ ∃ x : A, x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ p ∈ s, x ∉ p := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨1, one_pos, 0, zero_mem _, zero_mem _, by simp⟩
    obtain ⟨p, hpmin⟩ := s.exists_minimal hs
    have hps : p ∈ s := hpmin.prop
    obtain ⟨d, hd, g, hg, hgi, hgs⟩ := ih (s.erase p) (Finset.erase_ssubset hps)
      (fun q hq ↦ hp q (Finset.mem_of_mem_erase hq))
      (fun q hq ↦ hIp q (Finset.mem_of_mem_erase hq))
    by_cases hgp : g ∉ p
    · refine ⟨d, hd, g, hg, hgi, fun q hq ↦ ?_⟩
      by_cases h : q = p
      · exact h ▸ hgp
      · exact hgs q (Finset.mem_erase.mpr ⟨h, hq⟩)
    rw [not_not] at hgp
    have hx (q : s.erase p) : ∃ e, ∃ a ∈ 𝒜 e, a ∈ q.1 ∧ a ∉ p := by
      have hle : ¬ q.1 ≤ p := fun hle ↦
        (Finset.mem_erase.mp q.2).1
          (le_antisymm hle (hpmin.2 (Finset.mem_erase.mp q.2).2 hle))
      exact exists_homogeneous_mem_notMem 𝒜 q.1 p hle
    choose e a ha haq hap using hx
    obtain ⟨e₀, he₀, a₀, ha₀, ha₀i, ha₀p⟩ :=
      exists_positive_homogeneous_mem_notMem 𝒜 I p hI (hIp p hps)
    let E := e₀ + ∑ q ∈ (s.erase p).attach, e q
    let y := a₀ * ∏ q ∈ (s.erase p).attach, a q
    have hy : y ∈ 𝒜 E := SetLike.mul_mem_graded ha₀
      (SetLike.prod_mem_graded _ _ _ (fun q _ ↦ ha q))
    have hyp : y ∉ p := by
      refine (hp p hps).mul_notMem ha₀p ?_
      rw [Ideal.IsPrime.prod_mem_iff (hp := hp p hps)]
      push Not
      exact fun q _ ↦ hap q
    have hyi : y ∈ I := I.toIdeal.mul_mem_right _ ha₀i
    have hyq (q : s.erase p) : y ∈ q.1 :=
      Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _
        (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ q)) (haq q))
    have hE : 0 < E := lt_of_lt_of_le he₀ (Nat.le_add_right _ _)
    refine ⟨d * E, Nat.mul_pos hd hE, g ^ E + y ^ d, add_mem ?_ ?_,
      I.toIdeal.add_mem (I.toIdeal.pow_mem_of_mem hgi E hE)
        (I.toIdeal.pow_mem_of_mem hyi d hd), fun q hq ↦ ?_⟩
    · simpa [mul_comm] using SetLike.pow_mem_graded E hg
    · simpa using SetLike.pow_mem_graded d hy
    · by_cases hqp : q = p
      · subst hqp
        intro hmem
        exact hyp ((hp q hq).mem_of_pow_mem d ((Ideal.add_mem_iff_right _
          (Ideal.pow_mem_of_mem _ hgp E hE)).mp hmem))
      · have hqe : q ∈ s.erase p := Finset.mem_erase.mpr ⟨hqp, hq⟩
        intro hmem
        exact hgs q hqe ((hp q hq).mem_of_pow_mem E ((Ideal.add_mem_iff_left _
          (Ideal.pow_mem_of_mem _ (hyq ⟨q, hqe⟩) d hd)).mp hmem))

/-- Graded prime avoidance: a graded ideal contained in the positive-degree ideal and not
contained in any of finitely many homogeneous prime ideals contains a homogeneous element
of positive degree outside all those primes.

Source: Stacks Project, Algebra, Lemma 10.57.6 (Tag 00JS, `algebra-lemma-graded-silly`)
(blueprint: lem-sc-graded-prime-avoidance).

Proof: first discard primes contained in other primes; avoiding the remaining larger primes
avoids the discarded ones. For an empty family, take zero in degree one. Induct on the size
of the remaining family. For one prime, take a homogeneous component outside that prime of
an element of `I` outside it. Homogeneity puts the component in `I`; the containment in the
irrelevant ideal forces its degree to be positive. In the induction step choose homogeneous
`x ∈ I` of positive degree outside all but the last prime. If it also avoids the last prime,
we are done. Otherwise form the graded product ideal `I * p₁ * ... * pᵣ₋₁`. It is not contained
in the last prime: choose an element of each earlier prime outside the last prime, multiply
these together, and use primality to see that containment would force `I` into the last prime.
Choose a homogeneous component `y` in the product ideal outside the last prime. It has positive
degree since the product ideal is contained in `I`. Then `x ^ deg(y) + y ^ deg(x)` belongs to
`I` and is homogeneous of positive degree. At every earlier prime the second summand belongs
to the prime and the first does not; at the last prime the first belongs and the second does
not. Hence the sum avoids all primes. These are the five elementary steps of the blueprint proof;
no additional proof-dependency nodes are used. -/
theorem exists_homogeneous_mem_notMem_of_isPrime
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (r : ℕ) (p : Fin r → HomogeneousIdeal 𝒜)
    (hp : ∀ i : Fin r, (p i).toIdeal.IsPrime) (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ HomogeneousIdeal.irrelevant 𝒜) (hIp : ∀ i : Fin r, ¬ I ≤ p i) :
    ∃ (n : ℕ), 0 < n ∧ ∃ (x : A), x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ i : Fin r, x ∉ p i := by
  classical
  obtain ⟨n, hn, x, hx, hxi, hxp⟩ :=
    exists_positive_homogeneous_mem_notMem_finset 𝒜 (Finset.univ.image p)
      (by simpa only [Finset.mem_image, Finset.mem_univ, true_and,
        forall_exists_index, forall_apply_eq_imp_iff] using hp)
      I hI (by simpa only [Finset.mem_image, Finset.mem_univ, true_and,
        forall_exists_index, forall_apply_eq_imp_iff] using hIp)
  exact ⟨n, hn, x, hx, hxi, fun i ↦ hxp (p i) (Finset.mem_image_of_mem p (by simp))⟩

end HomogeneousIdeal
