/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.RingTheory.FiniteHomogeneousGenerators

/-!
# A lower degree bound for a finite graded polynomial module

Source: the minimal-degree argument in `lem-sc-p1-graded-nakayama-generation`, step 1.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A finite graded module over the nonnegatively graded polynomial ring is bounded below.
Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, expanded graded Nakayama argument,
step 1 (blueprint: lem-sc-p1-finite-graded-module-lower-bound).

Proof: use finite homogeneous generators of degrees `dᵢ` and choose a common lower bound `B`
for those finitely many integers (also if there are no generators). Expand every polynomial
coefficient into its homogeneous components. Each resulting multiple of generator `i` has
degree `dᵢ + t` for a natural number `t`, hence degree at least `B`. Its component in a degree
`j < B` is therefore zero. Additivity of the component projection proves that every element's
`j`-component is zero. Applying this to an element of the `j`-piece proves that element is zero.
-/
theorem exists_graded_module_lower_bound {k : Type u} [Field k]
    {N : Type v} [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    [Module.Finite (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (t : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : N),
      s ∈ homogeneousSubmodule (Fin 2) k t → x ∈ ℳ j →
        s • x ∈ ℳ ((t : ℤ) + j)) :
    ∃ B : ℤ, ∀ (j : ℤ) (x : N), j < B → x ∈ ℳ j → x = 0 := by
  classical
  let : DirectSum.Decomposition ℳ := hℳ.chooseDecomposition
  obtain ⟨r, d, m, hm, f, hf, hfm, _⟩ :=
    exists_finite_homogeneous_generators ℳ hℳ hsmul
  obtain ⟨B, hB⟩ := (Set.finite_range d).bddBelow
  refine ⟨B, fun j x hj hx ↦ ?_⟩
  let p : N →+ N :=
    { toFun := fun y ↦ (DirectSum.decompose ℳ y j : N)
      map_zero' := by simp
      map_add' := by intros; simp }
  have hsingle (i : Fin r) (s : MvPolynomial (Fin 2) k) : p (s • m i) = 0 := by
    rw [← sum_homogeneousComponent s, Finset.sum_smul, map_sum]
    apply Finset.sum_eq_zero
    intro t ht
    apply DirectSum.decompose_of_mem_ne ℳ
      (hsmul t (d i) _ _ (homogeneousComponent_isHomogeneous t s) (hm i))
    have hBi : B ≤ d i := hB (Set.mem_range_self i)
    omega
  obtain ⟨z, rfl⟩ := hf x
  have hz : p (f z) = 0 := by
    clear hx
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | single i s =>
      rw [← Finsupp.smul_single_one, map_smul, hfm]
      exact hsingle i s
  exact (DirectSum.decompose_of_mem_same ℳ hx).symm.trans hz

end MvPolynomial
