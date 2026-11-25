/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.MonicTensorPresentation.MonicTensorPresentation
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Closed sections of a split monic tensor presentation

Source: Stacks Project, Morphisms, Tag 03HW, final paragraph of lemma-massage-finite
(blueprint: lem-weil-pbc-split-monic-tensor-sections).
-/

@[expose] public section

universe u v

open Polynomial
open scoped TensorProduct

namespace MonicTensorPresentation

/-- The spectra of the evaluation quotients cover the tensor algebra when the monic equations
split. Source: Stacks Project, Tag 03HW, final paragraph of lemma-massage-finite.

Write each equation as a finite product of linear factors. At any prime of the tensor algebra,
pass to its domain quotient. The product of the linear factors of each distinguished root is
zero there, so at least one factor is zero. Choose one such factor for each equation. Evaluation
at the resulting root tuple, followed by the structural map to the domain quotient, agrees with
the quotient map on every tensor factor, hence everywhere. Taking kernels identifies the given
prime as the inverse image of its contraction along this evaluation map. The finite set of all
root tuples supplies all the sections, including the empty tuple when there are no equations.
(blueprint: lem-weil-pbc-split-monic-tensor-sections). -/
theorem exists_cover (R : Type u) [CommRing R] {ι : Type v} [Finite ι]
    (P : ι → R[X]) (hP : ∀ i, (P i).Monic) (hsp : ∀ i, (P i).Splits) :
    ∃ (n : ℕ) (e : Fin n → Tensor P →ₐ[R] R),
      (∀ k, Function.Surjective (e k)) ∧
      ∀ q : PrimeSpectrum (Tensor P),
        ∃ (k : Fin n) (r : PrimeSpectrum R), PrimeSpectrum.comap (e k) r = q := by
  classical
  let _ := Fintype.ofFinite ι
  choose m hm using fun i ↦ (Polynomial.splits_iff_exists_multiset.mp (hsp i))
  have hp (i : ι) : P i = ((m i).map (fun a ↦ X - C a)).prod := by
    simpa [(hP i).leadingCoeff] using hm i
  let K := ∀ i, {a : R // a ∈ m i}
  have : Fintype K := inferInstance
  have hroot (i : ι) (a : {a : R // a ∈ m i}) : aeval (a : R) (P i) = 0 := by
    rw [hp i, aeval_def, eval₂_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.mpr ⟨a, a.property, by simp⟩
  let e (k : K) : Tensor P →ₐ[R] R :=
    presentationMap P (fun i ↦ (k i).val) (fun i ↦ hroot i (k i))
  let equiv := Fintype.equivFin K
  refine ⟨Fintype.card K, fun k ↦ e (equiv.symm k), ?_, ?_⟩
  · intro k r
    exact ⟨algebraMap R (Tensor P) r, (e _).commutes r⟩
  intro q
  let Q := Tensor P ⧸ q.asIdeal
  let φ : Tensor P →ₐ[R] Q := Ideal.Quotient.mkₐ R q.asIdeal
  let y (i : ι) : Q := φ (PiTensorProduct.singleAlgHom i (AdjoinRoot.root (P i)))
  have hy (i : ι) : aeval (y i) (P i) = 0 :=
    AdjoinRoot.aeval_algHom_eq_zero (P i)
      (φ.comp (PiTensorProduct.singleAlgHom (R := R) (A := fun j ↦ AdjoinRoot (P j)) i))
  have hex (i : ι) : ∃ a ∈ m i, y i = algebraMap R Q a := by
    have hz : ((m i).map (fun a ↦ y i - algebraMap R Q a)).prod = 0 := by
      simpa only [hp i, aeval_def, eval₂_multiset_prod, Multiset.map_map,
        Function.comp_def, eval₂_sub, eval₂_X, eval₂_C] using hy i
    obtain ⟨a, ha, he⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
    exact ⟨a, ha, sub_eq_zero.mp he⟩
  choose a ha he using hex
  let k : K := fun i ↦ ⟨a i, ha i⟩
  have hφ : (Algebra.ofId R Q).comp (e k) = φ := by
    apply PiTensorProduct.algHom_ext
    intro i
    apply AdjoinRoot.algHom_ext
    change algebraMap R Q (e k (PiTensorProduct.singleAlgHom i
      (AdjoinRoot.root (P i)))) = y i
    rw [show e k (PiTensorProduct.singleAlgHom i (AdjoinRoot.root (P i))) = a i by
      exact presentationMap_root P _ _ i]
    exact (he i).symm
  refine ⟨equiv k, PrimeSpectrum.comap (algebraMap R (Tensor P)) q, ?_⟩
  dsimp only
  rw [equiv.symm_apply_apply]
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro t
  change algebraMap R (Tensor P) (e k t) ∈ q.asIdeal ↔ t ∈ q.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  have ht : Ideal.Quotient.mk q.asIdeal (algebraMap R (Tensor P) (e k t)) =
      Ideal.Quotient.mk q.asIdeal t := DFunLike.congr_fun hφ t
  exact ⟨fun h ↦ ht.symm.trans h, fun h ↦ ht.trans h⟩

end MonicTensorPresentation
