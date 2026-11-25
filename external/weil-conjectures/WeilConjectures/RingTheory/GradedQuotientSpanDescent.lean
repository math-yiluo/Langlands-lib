/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Descent in degree from generators of the irrelevant quotient

Source: the degree-component argument in `lem-sc-p1-graded-nakayama-generation`, step 2.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- Generation of the irrelevant quotient yields a one-degree descent for homogeneous elements.
Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, expanded graded Nakayama argument,
steps 1–2 (blueprint: lem-sc-p1-graded-quotient-span-descent).

Proof: write `Q` for the polynomial span of the homogeneous lifts. Lift a linear expression
for the quotient class of `x` to `q ∈ Q`. Then `x - q` belongs to `(x₀,x₁)N`, so it is
`x₀ • a + x₁ • b`. The submodule `Q` is homogeneous: expand polynomial coefficients in an
expression in its homogeneous generators, and use additivity of the component projection.
Project the equation to degree `j`. The projection of `q` still belongs to `Q`, while the
projection of `xᵢ • a` is `xᵢ` times the degree `j-1` projection of `a`. These projections of
`a,b` supply the desired decomposition. This argument requires no finite-generation assumption.
-/
theorem homogeneous_decomposition_of_quotient_span {k : Type u} [Field k]
    {N : Type v} [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    [Module k N] [IsScalarTower k (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (d : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : N),
      f ∈ homogeneousSubmodule (Fin 2) k d → x ∈ ℳ j → f • x ∈ ℳ ((d : ℤ) + j))
    (r : ℕ) (n : Fin r → N) (hn : ∀ i : Fin r, SetLike.IsHomogeneousElem ℳ (n i))
    (hgen : Submodule.span k (Set.range (fun i : Fin r ↦
      (Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
        (⊤ : Submodule (MvPolynomial (Fin 2) k) N)).mkQ (n i))) = ⊤)
    (j : ℤ) (x : N) (hx : x ∈ ℳ j) :
    ∃ q ∈ Submodule.span (MvPolynomial (Fin 2) k) (Set.range n),
      ∃ a ∈ ℳ (j - 1), ∃ b ∈ ℳ (j - 1),
        x = q + (X 0 : MvPolynomial (Fin 2) k) • a +
          (X 1 : MvPolynomial (Fin 2) k) • b := by
  classical
  let : DirectSum.Decomposition ℳ := hℳ.chooseDecomposition
  let Q := Submodule.span (MvPolynomial (Fin 2) k) (Set.range n)
  let I := Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
    (⊤ : Submodule (MvPolynomial (Fin 2) k) N)
  let p (e : ℤ) : N →+ N :=
    { toFun := fun y ↦ (DirectSum.decompose ℳ y e : N)
      map_zero' := by simp
      map_add' := by intros; simp }
  have hQhom : ∀ y ∈ Q, ∀ (s : MvPolynomial (Fin 2) k) (e : ℤ), p e (s • y) ∈ Q := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨d, hd⟩ := hn i
      intro s e
      rw [← sum_homogeneousComponent s, Finset.sum_smul, map_sum]
      apply Q.sum_mem
      intro t ht
      have hdeg := hsmul t d _ _ (homogeneousComponent_isHomogeneous t s) hd
      change (DirectSum.decompose ℳ _ e : N) ∈ Q
      by_cases he : (t : ℤ) + d = e
      · rw [DirectSum.decompose_of_mem_same ℳ (he ▸ hdeg)]
        exact Q.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
      · rw [DirectSum.decompose_of_mem_ne ℳ hdeg he]
        exact Q.zero_mem
    | zero => intro s e; simp
    | add a b ha hb ia ib =>
      intro s e
      rw [smul_add, map_add]
      exact Q.add_mem (ia s e) (ib s e)
    | smul a y hy iy =>
      intro s e
      rw [← mul_smul]
      exact iy (s * a) e
  have hshift (i : Fin 2) (e : ℤ) (y : N) :
      p e ((X i : MvPolynomial (Fin 2) k) • y) = (X i : MvPolynomial (Fin 2) k) • p (e - 1) y := by
    apply DirectSum.Decomposition.inductionOn (ℳ := ℳ)
      (motive := fun y ↦ p e ((X i : MvPolynomial (Fin 2) k) • y) =
        (X i : MvPolynomial (Fin 2) k) • p (e - 1) y) ?_ ?_ ?_ y
    · simp
    · intro d z
      have hdeg := hsmul 1 d (X i) z (isHomogeneous_X k i) z.property
      change (DirectSum.decompose ℳ _ e : N) =
        (X i : MvPolynomial (Fin 2) k) • (DirectSum.decompose ℳ (z : N) (e - 1) : N)
      by_cases he : d = e - 1
      · have he' : (1 : ℤ) + d = e := by omega
        rw [DirectSum.decompose_of_mem_same ℳ (he' ▸ hdeg),
          DirectSum.decompose_of_mem_same ℳ (he ▸ z.property)]
      · rw [DirectSum.decompose_of_mem_ne ℳ hdeg (by omega),
          DirectSum.decompose_of_mem_ne ℳ z.property he, smul_zero]
    · intro a b ha hb
      simp only [smul_add, map_add, ha, hb]
  have hlift : ∀ y ∈ Submodule.span k (Set.range (fun i : Fin r ↦ I.mkQ (n i))),
      ∃ q ∈ Q, I.mkQ q = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨n i, Submodule.subset_span (Set.mem_range_self i), rfl⟩
    | zero => exact ⟨0, Q.zero_mem, map_zero _⟩
    | add a b ha hb ia ib =>
      obtain ⟨q, hq, rfl⟩ := ia
      obtain ⟨q', hq', rfl⟩ := ib
      exact ⟨q + q', Q.add_mem hq hq', map_add _ _ _⟩
    | smul a y hy iy =>
      obtain ⟨q, hq, rfl⟩ := iy
      refine ⟨a • q, ?_, ?_⟩
      · rw [← IsScalarTower.algebraMap_smul (MvPolynomial (Fin 2) k) a q]
        exact Q.smul_mem _ hq
      · exact (I.mkQ.restrictScalars k).map_smul a q
  obtain ⟨q, hq, hqx⟩ := hlift (I.mkQ x) (by rw [hgen]; trivial)
  have hI : x - q ∈ I := by
    apply (Submodule.Quotient.mk_eq_zero I).mp
    change I.mkQ (x - q) = 0
    rw [map_sub, hqx, sub_self]
  have hrange : Set.range (X : Fin 2 → MvPolynomial (Fin 2) k) = {X 0, X 1} := by
    ext s
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  change x - q ∈ Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
    (⊤ : Submodule (MvPolynomial (Fin 2) k) N) at hI
  rw [hrange, Ideal.span_insert, Submodule.sup_smul,
    Submodule.ideal_span_singleton_smul, Submodule.ideal_span_singleton_smul] at hI
  obtain ⟨a', ha', b', hb', hab⟩ := Submodule.mem_sup.mp hI
  obtain ⟨a, _, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp ha'
  obtain ⟨b, _, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hb'
  have hxqab : x = q + (X 0 : MvPolynomial (Fin 2) k) • a + (X 1 : MvPolynomial (Fin 2) k) • b := by
    rw [← sub_add_cancel x q, ← hab]
    abel
  refine ⟨p j q, ?_, p (j - 1) a, (DirectSum.decompose ℳ a (j - 1)).property,
    p (j - 1) b, (DirectSum.decompose ℳ b (j - 1)).property, ?_⟩
  · simpa using hQhom q hq 1 j
  · have hpx : p j x = x := DirectSum.decompose_of_mem_same ℳ hx
    rw [← hpx, hxqab, map_add, map_add, hshift, hshift]

end MvPolynomial
