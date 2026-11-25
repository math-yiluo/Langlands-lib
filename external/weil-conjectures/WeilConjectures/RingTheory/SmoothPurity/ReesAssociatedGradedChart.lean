/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra
public import WeilConjectures.RingTheory.AssociatedGradedRing
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Homogeneous chart for the extended Rees zero fibre

Source: Stacks Tags 0630 and 0632, the affine normal-cone calculation.
(blueprint: lem-pur-rees-associated-graded-chart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open LaurentPolynomial
namespace Ideal
variable {R : Type u} [CommRing R] (I : Ideal R)

private theorem rees_coeff_mem {f : R[T;T⁻¹]} (hf : f ∈ I.extendedReesAlgebra) :
    ∀ k : ℤ, f.coeff k ∈ I ^ (-k).toNat := by
  classical
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain rfl | ⟨a, ha, rfl⟩ := hf
    · intro k
      by_cases hk : k = 1
      · subst k; simp
      · simp [T_apply, Ne.symm hk]
    · intro k
      change (C a * T (-1)).coeff k ∈ _
      rw [← single_eq_C_mul_T]
      by_cases hk : k = -1
      · subst k
        norm_num only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
          neg_neg, Int.toNat_one, pow_one]
        exact ha
      · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hk]
        exact Ideal.zero_mem _
  | algebraMap a =>
    intro k
    change (C a).coeff k ∈ _
    by_cases hk : k = 0
    · subst k; simp
    · simp [hk]
  | add f g _ _ hf hg =>
    intro k
    exact (I ^ (-k).toNat).add_mem (hf k) (hg k)
  | mul f g _ _ hf hg =>
    intro k
    rw [AddMonoidAlgebra.coeff_mul]
    apply Ideal.sum_mem
    intro a _
    apply Ideal.sum_mem
    intro b _
    dsimp only
    split_ifs with hab
    · have hmul := Ideal.mul_mem_mul (hf a) (hg b)
      rw [← pow_add] at hmul
      exact (Ideal.pow_le_pow_right (by omega)) hmul
    · exact Ideal.zero_mem _

private theorem rees_monomial_mem (n : ℕ) (a : R) (ha : a ∈ I ^ n) :
    C a * T (-(n : ℤ)) ∈ I.extendedReesAlgebra := by
  induction n generalizing a with
  | zero => simpa using C_mem_extendedReesAlgebra (I := I) a
  | succ n ih =>
    rw [pow_succ] at ha
    induction ha using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      have heq : C (a * b) * T (-(↑(n + 1) : ℤ)) =
          (C a * T (-(n : ℤ))) * (C b * T (-1)) := by
        have hdeg : -(↑(n + 1) : ℤ) = -(n : ℤ) + -1 := by omega
        rw [hdeg, T_add, map_mul]
        ring
      rw [heq]
      exact Subalgebra.mul_mem _ (ih a ha) (C_mul_T_neg_one_mem_extendedReesAlgebra hb)
    | add a ha b hb iha ihb =>
      simpa only [map_add, add_mul] using Subalgebra.add_mem I.extendedReesAlgebra iha ihb

private def reesMonomial (n : ℕ) (a : (I ^ n : Ideal R)) : I.extendedReesAlgebra :=
  ⟨C a.val * T (-(n : ℤ)), rees_monomial_mem I n a.val a.property⟩

private def reesMonomialAddHom (n : ℕ) : (I ^ n : Ideal R) →+
    I.extendedReesAlgebra ⧸ Ideal.span {I.extendedReesAlgebraT} where
  toFun a := Ideal.Quotient.mk _ (reesMonomial I n a)
  map_zero' := by
    have hh : reesMonomial I n 0 = 0 := by ext; simp [reesMonomial]
    rw [hh, map_zero]
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    simp [reesMonomial, add_mul]

private theorem reesMonomial_vanish (n : ℕ) (a : (I ^ n : Ideal R))
    (ha : a.val ∈ I ^ (n + 1)) : reesMonomialAddHom I n a = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨reesMonomial I (n + 1) ⟨a.val, ha⟩, ?_⟩
  apply Subtype.ext
  change (C a.val * T (-(↑(n + 1) : ℤ))) * T 1 = C a.val * T (-(n : ℤ))
  rw [mul_assoc, ← T_add]
  congr 2
  omega

private def reesPieceMap (n : ℕ) : associatedGradedPiece I n →+
    I.extendedReesAlgebra ⧸ Ideal.span {I.extendedReesAlgebraT} :=
  QuotientAddGroup.lift (Submodule.comap (I ^ n).subtype (I ^ (n + 1))).toAddSubgroup
    (reesMonomialAddHom I n) (fun a ha ↦ reesMonomial_vanish I n a ha)

private def reesGradedMap : associatedGraded I →+*
    I.extendedReesAlgebra ⧸ Ideal.span {I.extendedReesAlgebraT} :=
  DirectSum.toSemiring (reesPieceMap I) (by
    change Ideal.Quotient.mk _ (reesMonomial I 0 ⟨1, by simp⟩) = 1
    have hh : reesMonomial I 0 ⟨1, by simp⟩ = 1 := by ext; simp [reesMonomial]
    rw [hh, map_one]) (by
      intro n m a b
      induction a using Submodule.Quotient.induction_on with
      | _ a =>
        induction b using Submodule.Quotient.induction_on with
        | _ b =>
          change Ideal.Quotient.mk _ (reesMonomial I (n + m) _) =
            Ideal.Quotient.mk _ (reesMonomial I n a) *
              Ideal.Quotient.mk _ (reesMonomial I m b)
          rw [← map_mul]
          congr 1
          apply Subtype.ext
          change C (a.val * b.val) * T (-(↑(n + m) : ℤ)) =
            (C a.val * T (-(n : ℤ))) * (C b.val * T (-(m : ℤ)))
          have hdeg : -(↑(n + m) : ℤ) = -(n : ℤ) + -(m : ℤ) := by omega
          rw [hdeg, T_add, map_mul]
          ring)

private theorem reesGradedMap_of (n : ℕ) (a : (I ^ n : Ideal R)) :
    reesGradedMap I (DirectSum.of (associatedGradedPiece I) n
      (Submodule.Quotient.mk a)) = Ideal.Quotient.mk _ (reesMonomial I n a) :=
  DirectSum.toSemiring_of _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem reesGradedMap_surjective : Function.Surjective (reesGradedMap I) := by
  intro z
  induction z using Quotient.inductionOn' with
  | _ f =>
    obtain ⟨f, hf⟩ := f
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain rfl | ⟨a, ha, rfl⟩ := hf
      · refine ⟨0, ?_⟩
        rw [map_zero]
        symm
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      · refine ⟨DirectSum.of (associatedGradedPiece I) 1
          (Submodule.Quotient.mk (⟨a, by simpa using ha⟩ : (I ^ 1 : Ideal R))), ?_⟩
        rw [reesGradedMap_of]
        rfl
    | algebraMap a =>
      refine ⟨DirectSum.of (associatedGradedPiece I) 0
        (Submodule.Quotient.mk (⟨a, by simp⟩ : (I ^ 0 : Ideal R))), ?_⟩
      rw [reesGradedMap_of]
      apply congrArg (Ideal.Quotient.mk _)
      apply Subtype.ext
      simp [reesMonomial]
    | add f g hf hg ihf ihg =>
      obtain ⟨x, hx⟩ := ihf
      obtain ⟨y, hy⟩ := ihg
      refine ⟨x + y, ?_⟩
      rw [map_add, hx, hy]
      exact (map_add (Ideal.Quotient.mk _)
        (⟨f, hf⟩ : I.extendedReesAlgebra) ⟨g, hg⟩).symm
    | mul f g hf hg ihf ihg =>
      obtain ⟨x, hx⟩ := ihf
      obtain ⟨y, hy⟩ := ihg
      refine ⟨x * y, ?_⟩
      rw [map_mul, hx, hy]
      exact (map_mul (Ideal.Quotient.mk _)
        (⟨f, hf⟩ : I.extendedReesAlgebra) ⟨g, hg⟩).symm

private theorem reesGradedMap_injective : Function.Injective (reesGradedMap I) := by
  classical
  have hker (x : associatedGraded I) (hx : reesGradedMap I x = 0) : x = 0 := by
    choose a ha using fun n ↦ Submodule.Quotient.mk_surjective
      (Submodule.comap (I ^ n).subtype (I ^ (n + 1))) (x n)
    let F : I.extendedReesAlgebra := ∑ n ∈ x.support, reesMonomial I n (a n)
    have hF : Ideal.Quotient.mk (Ideal.span {I.extendedReesAlgebraT}) F =
        reesGradedMap I x := by
      dsimp only [F]
      rw [map_sum]
      simp_rw [← reesGradedMap_of, ha]
      rw [← map_sum, DirectSum.sum_support_of]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (hF.trans hx))
    have hyc (n : ℕ) : (F : R[T;T⁻¹]).coeff (-(n : ℤ)) =
        (y : R[T;T⁻¹]).coeff (-(n : ℤ) - 1) := by
      rw [← hy]
      change ((y : R[T;T⁻¹]) * T 1).coeff (-(n : ℤ)) = _
      rw [mul_comm, coeff_T_mul]
    apply DFinsupp.ext
    intro n
    by_cases hn : n ∈ x.support
    · have hFc : (F : R[T;T⁻¹]).coeff (-(n : ℤ)) = (a n).val := by
        dsimp only [F]
        have hsum : ((∑ m ∈ x.support, reesMonomial I m (a m) :
            I.extendedReesAlgebra) : R[T;T⁻¹]) =
            ∑ m ∈ x.support, C (a m).val * T (-(m : ℤ)) := by
          exact map_sum I.extendedReesAlgebra.val.toRingHom _ _
        rw [hsum]
        simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
          ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
        rw [Finset.sum_eq_single n]
        · exact Finsupp.single_eq_same
        · intro m hm hmn
          apply Finsupp.single_eq_of_ne
          omega
        · exact fun h ↦ False.elim (h hn)
      have hm : (a n).val ∈ I ^ (n + 1) := by
        rw [← hFc, hyc]
        have hb := rees_coeff_mem I y.property (-(n : ℤ) - 1)
        have hn' : (-(-(n : ℤ) - 1)).toNat = n + 1 := by omega
        rwa [hn'] at hb
      rw [← ha n]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hm
    · exact DFinsupp.notMem_support_iff.mp hn
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker (x - y)
  rw [map_sub, hxy, sub_self]

/-- The extended Rees quotient has the associated-graded homogeneous representatives.
Source: Stacks Tags 0630 and 0632, the affine normal-cone calculation.
(blueprint: lem-pur-rees-associated-graded-chart).

Proof: Send the degree-n class of a to a/t^n modulo t. A change by I^(n+1)
is a multiple of t, so the map descends, preserves products, and preserves one.
The quotient is generated by constants and a/t, proving surjectivity. If a finite
sum maps to zero, its Laurent representative is t times an extended Rees element.
The coefficient of t^(-n) therefore lies in I^(n+1); all its graded classes vanish.
This proves injectivity without finiteness or regularity assumptions. -/
theorem rees_associatedGraded_chart :
    ∃ e : associatedGraded I ≃+*
      I.extendedReesAlgebra ⧸ Ideal.span {I.extendedReesAlgebraT},
      ∀ (n : ℕ) (a : (I ^ n : Ideal R)),
        ∃ ha : C a.val * T (-(n : ℤ)) ∈ I.extendedReesAlgebra,
          e (DirectSum.of (associatedGradedPiece I) n (Submodule.Quotient.mk a)) =
            Ideal.Quotient.mk _ ⟨C a.val * T (-(n : ℤ)), ha⟩ := by
  refine ⟨RingEquiv.ofBijective (reesGradedMap I)
    ⟨reesGradedMap_injective I, reesGradedMap_surjective I⟩, ?_⟩
  intro n a
  exact ⟨rees_monomial_mem I n a.val a.property, reesGradedMap_of I n a⟩

end Ideal
