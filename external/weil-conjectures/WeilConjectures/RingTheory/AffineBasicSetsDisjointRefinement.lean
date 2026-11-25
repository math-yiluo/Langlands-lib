/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.MeasureTheory.SetSemiring
import WeilConjectures.RingTheory.AffineBasicSetDifference

/-!
# Disjoint refinement of basic constructible subsets of an affine spectrum

Source: Stacks Project, Algebra, Lemma 10.29.3 (Tag 0G1P), and the refinement step
in Étale Cohomology, Lemma 59.72.1 (Tag 03S0) (blueprint:
lem-weil-pbc-affine-basic-sets-disjoint-refinement).
-/

@[expose] public section

universe u

open Set

namespace PrimeSpectrum

/-- (blueprint: lem-weil-pbc-affine-basic-sets-disjoint-refinement)
For a commutative ring, every finite family of basic constructible subsets of its
prime spectrum has a finite pairwise-disjoint refinement by basic constructible subsets
with the same union.  `BasicConstructibleSetData.toSet` represents
`D(f) ∩ V(g₁, ..., gₙ)` as `V(g₁, ..., gₙ) \ V(f)`.

Source: Stacks Project, Algebra, Lemma 10.29.3 (Tag 0G1P), and the refinement step
in Étale Cohomology, Lemma 59.72.1 (Tag 03S0).

Proof:
1. Induct on the number of input sets, starting with the empty output family.
   Given a disjoint basic family covering the first t input sets, start with the
   singleton family consisting of the next input set. Subtract each old piece in
   turn, replacing each current piece by the finite disjoint basic decomposition
   of its difference supplied by `lem-weil-pbc-affine-basic-set-difference`.
   Pieces arising from different current pieces stay disjoint because they are
   subsets of those pieces. The resulting family covers exactly the next input
   set minus the union of the old family.
2. Keep the entire old family and append the new pieces. Each new piece is
   disjoint from every old piece, so the combined family is finite and pairwise
   disjoint. Its union is the old union together with the next input set.
   After m steps this is the required union; for m = 0 the family is empty. -/
theorem finite_disjoint_basic_constructible_refinement {A : Type u} [CommRing A]
    (m : ℕ) (B : Fin m → BasicConstructibleSetData A) :
    ∃ (p : ℕ) (C : Fin p → BasicConstructibleSetData A),
      (Pairwise fun i j => Disjoint ((C i).toSet) ((C j).toSet)) ∧
      (⋃ i, (B i).toSet) = ⋃ j, (C j).toSet := by
  classical
  let basics : Set (Set (PrimeSpectrum A)) := Set.range BasicConstructibleSetData.toSet
  have hbasics : MeasureTheory.IsSetSemiring basics := by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨⟨0, 0, Fin.elim0⟩, ?_⟩
      simp [BasicConstructibleSetData.toSet, zeroLocus_singleton_zero]
    · rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
      refine ⟨⟨P.f * Q.f, P.n + Q.n, Fin.append P.g Q.g⟩, ?_⟩
      ext x
      simp [BasicConstructibleSetData.toSet, mem_zeroLocus, Set.range_subset_iff,
        Fin.forall_fin_add, Fin.append, x.isPrime.mul_mem_iff_mem_or_mem,
        not_or, and_assoc, and_left_comm]
    · rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
      obtain ⟨n, S, hdisj, hcover⟩ := exists_disjoint_basicConstructibleSetData_diff
        P.f Q.f P.n Q.n P.g Q.g
      let I : Finset (Set (PrimeSpectrum A)) :=
        Finset.univ.image (fun i ↦ (S i).toSet)
      refine ⟨I, ?_, ?_, ?_⟩
      · intro t ht
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
        exact ⟨S i, rfl⟩
      · intro s hs t ht hne
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
        exact hdisj (fun hij ↦ hne (hij ▸ rfl))
      · simpa [I, Set.sUnion_image, Set.sUnion_range] using hcover
  let J : Finset (Set (PrimeSpectrum A)) :=
    Finset.univ.image (fun i ↦ (B i).toSet)
  have hJ : (J : Set (Set (PrimeSpectrum A))) ⊆ basics := by
    intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨B i, rfl⟩
  obtain ⟨K, _, hK, hdisj, _, _, hcover⟩ := hbasics.disjointOfUnion_props hJ
  let Q : Finset (Set (PrimeSpectrum A)) := J.biUnion K
  have hQ : ∀ q : Q, ∃ D : BasicConstructibleSetData A, D.toSet = q.val := by
    intro q
    obtain ⟨s, hs, hqs⟩ := Finset.mem_biUnion.mp q.property
    exact hK s hs hqs
  choose D hD using hQ
  let C : Fin Q.card → BasicConstructibleSetData A := fun i ↦ D (Q.equivFin.symm i)
  have hC (i : Fin Q.card) : (C i).toSet = (Q.equivFin.symm i).val :=
    hD _
  refine ⟨Q.card, C, ?_, ?_⟩
  · intro i j hij
    rw [hC, hC]
    have hdQ : (Q : Set (Set (PrimeSpectrum A))).PairwiseDisjoint id := by
      simpa only [Q, Finset.coe_biUnion, Finset.mem_coe] using hdisj
    exact hdQ (Q.equivFin.symm i).property (Q.equivFin.symm j).property
      (fun heq ↦ hij (Q.equivFin.symm.injective (Subtype.ext heq)))
  · calc
      (⋃ i, (B i).toSet) = ⋃₀ (J : Set (Set (PrimeSpectrum A))) := by
        simp [J, Set.sUnion_range]
      _ = ⋃₀ (Q : Set (Set (PrimeSpectrum A))) := by
        simpa only [Q, Finset.coe_biUnion, Finset.mem_coe] using hcover
      _ = ⋃ j, (C j).toSet := by
        ext x
        simp only [Set.mem_sUnion, Finset.mem_coe, Set.mem_iUnion]
        constructor
        · rintro ⟨q, hq, hx⟩
          refine ⟨Q.equivFin ⟨q, hq⟩, ?_⟩
          simpa only [hC, Equiv.symm_apply_apply] using hx
        · rintro ⟨j, hj⟩
          exact ⟨(Q.equivFin.symm j).val, (Q.equivFin.symm j).property, (hC j) ▸ hj⟩

end PrimeSpectrum
