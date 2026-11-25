/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.Supported
import WeilConjectures.RingTheory.FiniteHomogeneousGenerators

/-!
# Finite graded free covers

Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, construction of the first free
module.
-/

@[expose] public section

universe u v

namespace MvPolynomial

private noncomputable def flatten {k : Type u} [Field k] {r : ℕ} :
    (Fin r →₀ MvPolynomial (Fin 2) k) ≃ₗ[k] (Fin r × (Fin 2 →₀ ℕ) →₀ k) :=
  (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv k)).trans
    (Finsupp.curryLinearEquiv k).symm

private noncomputable def shiftedGrade {k : Type u} [Field k] {r : ℕ}
    (e : Fin r → ℤ) (j : ℤ) : Submodule k (Fin r →₀ MvPolynomial (Fin 2) k) :=
  (Finsupp.supported k k {z | (z.2.degree : ℤ) + e z.1 = j}).comap
    flatten.toLinearMap

private theorem mem_shiftedGrade {k : Type u} [Field k] {r : ℕ}
    (e : Fin r → ℤ) (j : ℤ) (x : Fin r →₀ MvPolynomial (Fin 2) k) :
    x ∈ shiftedGrade e j ↔
      ∀ a t, (x a).coeff t ≠ 0 → (t.degree : ℤ) + e a = j := by
  simp only [shiftedGrade, Submodule.mem_comap, Finsupp.mem_supported,
    Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq,
    Prod.forall]
  rfl

private theorem shiftedGrade_internal {k : Type u} [Field k] {r : ℕ}
    (e : Fin r → ℤ) :
    DirectSum.IsInternal (fun j ↦ (shiftedGrade (k := k) e j).toAddSubgroup) := by
  classical
  let δ : Fin r × (Fin 2 →₀ ℕ) → ℤ := fun z ↦ (z.2.degree : ℤ) + e z.1
  let A : ℤ → Submodule k (Fin r × (Fin 2 →₀ ℕ) →₀ k) :=
    fun j ↦ Finsupp.supported k k {z | δ z = j}
  have hi : iSupIndep A := by
    intro j
    have hd : Disjoint (Finsupp.supported k k {z | δ z = j})
        (⨆ l : {l : ℤ // l ≠ j}, Finsupp.supported k k {z | δ z = l.1}) := by
      rw [← Finsupp.supported_iUnion]
      apply Finsupp.disjoint_supported_supported
      apply Set.disjoint_left.mpr
      intro z hj hn
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hn
      exact l.property (hl.symm.trans hj)
    simpa only [A, iSup_subtype] using hd
  have hs : iSup A = ⊤ := by
    change (⨆ j, Finsupp.supported k k {z | δ z = j}) = ⊤
    rw [← Finsupp.supported_iUnion]
    have hset : (⋃ j : ℤ, {z | δ z = j}) = Set.univ := by
      ext z
      simp
    rw [hset, Finsupp.supported_univ]
  let E := Submodule.orderIsoMapComap (flatten (k := k) (r := r)).symm
  have hEi : iSupIndep (fun j ↦ E (A j)) := hi.map_orderIso E
  have hEs : (⨆ j, E (A j)) = ⊤ := by
    rw [← E.map_iSup, hs, E.map_top]
  have hI := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hEi hEs
  have hE : (fun j ↦ E (A j)) = fun j ↦ shiftedGrade (k := k) e j := by
    funext j
    exact Submodule.map_equiv_eq_comap_symm _ _
  rw [hE] at hI
  exact hI

private theorem shiftedGrade_coefficient {k : Type u} [Field k] {r : ℕ}
    {e : Fin r → ℤ} {j : ℤ} {x : Fin r →₀ MvPolynomial (Fin 2) k}
    (hx : x ∈ shiftedGrade e j) (a : Fin r) :
    x a = 0 ∨ ∃ n : ℕ, (x a).IsHomogeneous n ∧ (n : ℤ) + e a = j := by
  classical
  by_cases hzero : x a = 0
  · exact Or.inl hzero
  · obtain ⟨t, ht⟩ := exists_coeff_ne_zero hzero
    have hx' := (mem_shiftedGrade e j x).mp hx
    refine Or.inr ⟨t.degree, ?_, hx' a t ht⟩
    intro d hd
    rw [Pi.one_def, ← Finsupp.degree_eq_weight_one]
    have hdt := hx' a d hd
    have htt := hx' a t ht
    omega

private theorem shiftedGrade_smul {k : Type u} [Field k] {r : ℕ}
    (e : Fin r → ℤ) (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k)
    (x : Fin r →₀ MvPolynomial (Fin 2) k)
    (hs : s ∈ homogeneousSubmodule (Fin 2) k n) (hx : x ∈ shiftedGrade e j) :
    s • x ∈ shiftedGrade e ((n : ℤ) + j) := by
  apply (mem_shiftedGrade _ _ _).mpr
  intro a t ht
  rw [Finsupp.smul_apply, smul_eq_mul] at ht
  rcases shiftedGrade_coefficient hx a with hz | ⟨m, hm, he⟩
  · simp [hz] at ht
  · have hmul := (hs : s.IsHomogeneous n).mul hm
    have hdeg := hmul ht
    rw [Pi.one_def, ← Finsupp.degree_eq_weight_one] at hdeg
    rw [hdeg, Nat.cast_add]
    omega

private theorem shiftedGrade_single {k : Type u} [Field k] {r : ℕ}
    (e : Fin r → ℤ) (a : Fin r) :
    Finsupp.single a (1 : MvPolynomial (Fin 2) k) ∈ shiftedGrade e (e a) := by
  classical
  apply (mem_shiftedGrade _ _ _).mpr
  intro a' t ht
  by_cases ha : a' = a
  · subst a'
    simp only [Finsupp.single_eq_same] at ht
    have hdeg := (isHomogeneous_one (Fin 2) k) ht
    rw [Pi.one_def, ← Finsupp.degree_eq_weight_one] at hdeg
    simp [hdeg]
  · simp [ha] at ht

/-- A finite graded module admits a surjection from a finite free module with homogeneous basis.
Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, proof, choose homogeneous
generators (blueprint: lem-sc-p1-graded-free-cover).

Proof: apply `exists_finite_homogeneous_generators` to obtain generators `m a` of degrees
`e a` and its surjective map from `Fin r →₀ S`, where `S = k[x₀,x₁]`. Give this free module
its shifted grading: a vector belongs to degree `j` if its coefficient at `a` belongs to the
polynomial homogeneous part of degree `j - e a`, with that part zero for negative degrees.
Decompose each coefficient into total-degree homogeneous polynomials and collect terms of
common shifted degree. Each vector has only finitely many such terms, and uniqueness follows
coefficientwise from uniqueness of the polynomial decomposition. This proves internality.
Multiplication by a homogeneous polynomial of degree `n` raises each shifted coefficient degree
by `n`, proving scalar compatibility. The standard basis vector at `a` has degree `e a`.
Linearity and the degree assertion of the generator theorem show that the map preserves each
homogeneous part. Take the shift parameter `d a = -e a`. This includes the empty basis when
`M = 0`. The source has universe `u` independently of the target's universe `v`. -/
theorem exists_graded_free_cover {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : M),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j → s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ (F : ModuleCat.{u} (MvPolynomial (Fin 2) k))
      (𝒢 : ℤ → AddSubgroup F) (r : ℕ) (d : Fin r → ℤ)
      (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) F)
      (q : F →ₗ[MvPolynomial (Fin 2) k] M),
      DirectSum.IsInternal 𝒢 ∧
      (∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : F),
        s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒢 j → s • x ∈ 𝒢 ((n : ℤ) + j)) ∧
      (∀ a : Fin r, b a ∈ 𝒢 (-(d a))) ∧
      (∀ (j : ℤ) (x : F), x ∈ 𝒢 j → q x ∈ ℳ j) ∧ Function.Surjective q := by
  classical
  obtain ⟨r, e, m, hm, f, hf, hfb, hfg⟩ :=
    exists_finite_homogeneous_generators ℳ hℳ hsmul
  let F := ModuleCat.of (MvPolynomial (Fin 2) k) (Fin r →₀ MvPolynomial (Fin 2) k)
  let 𝒢 : ℤ → AddSubgroup F := fun j ↦ (shiftedGrade e j).toAddSubgroup
  refine ⟨F, 𝒢, r, fun a ↦ -e a, Finsupp.basisSingleOne, f,
    shiftedGrade_internal e, ?_, ?_, ?_, hf⟩
  · intro n j s x hs hx
    exact shiftedGrade_smul e n j s x hs hx
  · intro a
    change Finsupp.single a 1 ∈ shiftedGrade e (-(-e a))
    simpa only [neg_neg] using shiftedGrade_single e a
  · intro j x hx
    have hxsum : x = ∑ a ∈ x.support, x a • Finsupp.single a 1 := by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      exact (Finsupp.sum_single x).symm
    rw [hxsum, map_sum]
    apply (ℳ j).sum_mem
    intro a ha
    rcases shiftedGrade_coefficient hx a with hz | ⟨n, hn, he⟩
    · simp [hz]
    · rw [← he]
      exact hfg a n (x a) hn

end MvPolynomial
