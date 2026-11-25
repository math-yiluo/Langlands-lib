/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.RingTheory.FiniteGabberFlatSplit
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The coefficient relation before passing to the quotient

Source: Stacks Project, More on Algebra, Tag 0EM0, proof of `lemma-helper-finite`.
-/

@[expose] public section

universe u v w z

open scoped BigOperators

namespace Algebra

private theorem faithfullyFlat_of_quotient_equiv
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    [Module.Flat A C] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (α : A ⧸ I ≃+* C ⧸ I.map (algebraMap A C))
    (hα : ∀ a : A, α (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk _ (algebraMap A C a)) : Module.FaithfullyFlat A C := by
  refine (Module.faithfullyFlat_iff A C).2 ⟨inferInstance, ?_⟩
  intro m hm htop
  have hIm : I ≤ m := hI.trans (sInf_le ⟨bot_le, hm⟩)
  let q : A ⧸ I →+* A ⧸ m :=
    Ideal.quotientMap m (RingHom.id A) (by simpa using hIm)
  let r : C →+* A ⧸ m :=
    q.comp (α.symm.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap A C))))
  have hr (a : A) : r (algebraMap A C a) = Ideal.Quotient.mk m a := by
    change q (α.symm (Ideal.Quotient.mk _ (algebraMap A C a))) = _
    rw [← hα, α.symm_apply_apply]
    rfl
  have hker : m.map (algebraMap A C) ≤ RingHom.ker r := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change r (algebraMap A C a) = 0
    rw [hr]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [Ideal.smul_top_eq_map] at htop
  have hone : (1 : C) ∈ m.map (algebraMap A C) := by
    change (1 : C) ∈ (m.map (algebraMap A C)).restrictScalars A
    rw [htop]
    trivial
  have : (1 : A ⧸ m) = 0 := by simpa using hker hone
  exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr (Ideal.Quotient.eq_zero_iff_mem.mp this))

private theorem exists_coefficient_tensor
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (I : Ideal A) (b : B) (k : C) (hk : k ∈ I.map (algebraMap A C)) :
    ∃ t : TensorProduct A C I, ∀ n : ℕ,
      (I.subtype.smulRight (b ^ n)).lTensor C t =
        algebraMap C (TensorProduct A C B) k * ((1 : C) ⊗ₜ[A] b) ^ n := by
  induction hk using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      refine ⟨(1 : C) ⊗ₜ[A] (⟨i, hi⟩ : I), fun n => ?_⟩
      simp only [LinearMap.lTensor_tmul, LinearMap.smulRight_apply,
        Submodule.subtype_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul, Algebra.smul_def]
      simpa only [Algebra.smul_def, mul_one, algebraMap_self, RingHom.id_apply] using
        (TensorProduct.tmul_smul i (1 : C) (b ^ n)).trans
          (TensorProduct.smul_tmul' i (1 : C) (b ^ n))
  | zero =>
      exact ⟨0, fun n => by simp⟩
  | add y z hy hz ihy ihz =>
      obtain ⟨t, ht⟩ := ihy
      obtain ⟨s, hs⟩ := ihz
      exact ⟨t + s, fun n => by rw [map_add, ht, hs, map_add, add_mul]⟩
  | smul c y hy ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨c • t, fun n => ?_⟩
      rw [← LinearMap.smul_lTensor, ht]
      simp [Algebra.smul_def, map_mul]

/-- The upstairs relation with coefficients in the extended ideal, before taking a quotient.
Source: Stacks Project, More on Algebra, Tag 0EM0, proof of `lemma-helper-finite`.
(blueprint: lem-weil-pbc-gabber-upstairs-tensor-coefficients)

Proof: Lift the idempotent (1,0) over an etale neighbourhood preserving A/I (07M4).
Split the finite base change of B into its two idempotent factors. The first factor's
structure map has finite cokernel which is equal to I times itself; Nakayama (00DV)
gives g congruent to 1 modulo I annihilating this cokernel. Localize at g. The first
factor is now a quotient of the base C, and the image of b-1 lifts to a coefficient
in IC. In the second factor b lies in the extended ideal. The integral extended-ideal
annihilator (00H5) gives a monic polynomial congruent to X^e annihilating b there.
Multiply it by X, so its degree d is positive even if the second factor is zero.
Multiplying this polynomial by X-1-a, with a the first-factor lift of b-1, annihilates
both factors. Its difference from (X-1)X^d has degree at most d and coefficients in IC.
Each coefficient in IC is a finite sum of products c*i with c in C and i in I, hence
is represented by an element of C tensor_A I. Evaluation gives the displayed sum,
with signs absorbed into the coefficient tensors. C is flat (etale then localization)
and C/IC is A/I. Every maximal ideal of A contains I and has nonzero fibre in C;
the flat maximal-fibre criterion (00HP) therefore makes C faithfully flat. -/
theorem exists_gabber_upstairs_tensor_relation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (B₁ : Type w) (B₂ : Type z) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* (B₁ × B₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)))
    (h₁ : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B) (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (C : CommRingCat.{u}) (f : A →+* C),
      letI : Algebra A C := f.toAlgebra
      Module.FaithfullyFlat A C ∧ ∃ d : ℕ, 1 ≤ d ∧
        ∃ c : Fin (d + 1) → TensorProduct A C I,
          TensorProduct.tmul A (1 : C) ((b - 1) * b ^ d) =
            ∑ j : Fin (d + 1),
              (I.subtype.smulRight (b ^ (j : ℕ))).lTensor C (c j) := by
  classical
  obtain ⟨C, f, hflat, α, hα, K, L, hKL, a, ha, hxK, hxL⟩ :=
    exists_flat_split_gabber_neighbourhood I B₁ B₂ e he h₁ b hb
  let : Algebra A C := f.toAlgebra
  have : Module.Flat A C := hflat
  have hff := faithfullyFlat_of_quotient_equiv I hI α hα
  refine ⟨C, f, hff, ?_⟩
  cases subsingleton_or_nontrivial C with
  | inl h =>
      exact ⟨1, by omega, fun _ => 0, Subsingleton.elim _ _⟩
  | inr h =>
      let T := TensorProduct A C B
      let x : T := (1 : C) ⊗ₜ[A] b
      let J := I.map (algebraMap A C)
      let q := Ideal.Quotient.mkₐ C L
      have hx : q x ∈ J.map (algebraMap C (T ⧸ L)) := by
        have hx' : q x ∈ (J.map (algebraMap C T)).map (Ideal.Quotient.mk L) :=
          Ideal.mem_quotient_iff_mem_sup.mpr (by simpa only [sup_comm] using hxL)
        rw [Ideal.map_map] at hx'
        exact hx'
      obtain ⟨p, hp, hpx, hpc⟩ :=
        Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hx
      let d := p.natDegree + 1
      let G := Polynomial.X * p
      let H := (Polynomial.X - Polynomial.C (1 + a)) * G
      have hH : Polynomial.aeval x H = 0 := by
        suffices heval : Polynomial.aeval x H ∈ K ⊓ L by
          simpa only [hKL, Submodule.mem_bot] using heval
        constructor
        · dsimp only [H, G]
          simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
            map_add, map_one]
          exact K.mul_mem_right _ (by simpa only [sub_add_eq_sub_sub] using hxK)
        · apply Ideal.Quotient.eq_zero_iff_mem.mp
          change q (Polynomial.aeval x H) = 0
          rw [← Polynomial.aeval_algHom_apply]
          simp [H, G, hpx]
      have hGmonic : G.Monic := Polynomial.monic_X.mul hp
      have hHmonic : H.Monic := (Polynomial.monic_X_sub_C (1 + a)).mul hGmonic
      have hGdeg : G.natDegree = d := by
        rw [Polynomial.Monic.natDegree_mul Polynomial.monic_X hp]
        simp [d, Nat.add_comm]
      have hHdeg : H.natDegree = d + 1 := by
        rw [(Polynomial.monic_X_sub_C (1 + a)).natDegree_mul hGmonic,
          Polynomial.natDegree_X_sub_C, hGdeg, Nat.add_comm]
      let F : Polynomial C := (Polynomial.X - 1) * Polynomial.X ^ d
      have hFmonic : F.Monic :=
        (Polynomial.monic_X_sub_C 1).mul (Polynomial.monic_X.pow d)
      have hFdeg : F.natDegree = d + 1 := by
        change ((Polynomial.X - Polynomial.C (1 : C)) * Polynomial.X ^ d).natDegree = _
        rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C (1 : C))
          (Polynomial.monic_X.pow d)]
        rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_pow]
        omega
      let r := F - H
      have hrdeg : r.natDegree ≤ d := by
        apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro n hn
        dsimp only [r]
        rw [Polynomial.coeff_sub]
        by_cases heq : n = d + 1
        · subst n
          rw [← hFdeg, hFmonic.coeff_natDegree, hFdeg, ← hHdeg,
            hHmonic.coeff_natDegree, sub_self]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), sub_self]
      have hpmap : p.map (Ideal.Quotient.mk J) = Polynomial.X ^ p.natDegree := by
        ext n
        rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
        by_cases hn : n = p.natDegree
        · subst n
          simp [hp.coeff_natDegree]
        · rw [ite_eq_right hn]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpc n hn)
      have hrmap : r.map (Ideal.Quotient.mk J) = 0 := by
        have hamod : Ideal.Quotient.mk J a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
        simp [r, F, H, G, hpmap, hamod, d, pow_succ, mul_assoc, mul_comm, mul_left_comm]
      have hrc (n : ℕ) : r.coeff n ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have := congrArg (fun t : Polynomial (C ⧸ J) => t.coeff n) hrmap
        simpa using this
      have hreval : Polynomial.aeval x r = (x - 1) * x ^ d := by
        simp [r, F, hH]
      have hsum : (x - 1) * x ^ d =
          ∑ j : Fin (d + 1), algebraMap C T (r.coeff j) * x ^ (j : ℕ) := by
        rw [← hreval, Polynomial.aeval_def,
          Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hrdeg)]
        exact (Fin.sum_univ_eq_sum_range _ _).symm
      choose c hc using fun j : Fin (d + 1) =>
        exists_coefficient_tensor I b (r.coeff j) (hrc j)
      refine ⟨d, by dsimp [d]; omega, c, ?_⟩
      calc
        _ = (x - 1) * x ^ d := by
          let κ := Algebra.TensorProduct.includeRight (R := A) (A := C) (B := B)
          change κ ((b - 1) * b ^ d) = (κ b - 1) * κ b ^ d
          rw [map_mul, map_sub, map_one, map_pow]
        _ = _ := hsum
        _ = _ := Finset.sum_congr rfl fun j _ => (hc j j).symm

end Algebra
