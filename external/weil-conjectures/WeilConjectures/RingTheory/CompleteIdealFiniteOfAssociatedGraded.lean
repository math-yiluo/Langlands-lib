/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.AssociatedGradedIdealApproximation

/-!
# Lifting finite generation from an associated graded ring

Source: Stacks Project, Algebra, Lemma 05GH, proof, second and third paragraphs
(blueprint: lem-weil-pbc-complete-ideal-finite-associated-graded).
-/

@[expose] public section

universe u

open scoped BigOperators

namespace Ideal

/-- Every ideal of an adically complete ring with Noetherian associated graded is finite.
Source: Stacks Project, Algebra, Lemma 05GH, proof, second and third paragraphs
(blueprint: lem-weil-pbc-complete-ideal-finite-associated-graded).

Proof: For an ideal `K`, the images of `K ∩ J^n` in `J^n/J^(n+1)` form a homogeneous
ideal of `gr_J(A)`. Multiplication preserves it because `K` is an ideal. Noetherianity
provides finitely many generators; replace them by all their homogeneous components,
which still lie in this ideal. Lift the resulting homogeneous generators of degrees
`d j` to elements `h j ∈ K ∩ J^(d j)`. For `x ∈ K ∩ J^n`, express its degree-`n`
initial form in these generators and take homogeneous components of the coefficients.
Lift those of degree `n - d j` to `a j ∈ J^(n - d j)`, setting `a j = 0` for `n < d j`.
Then `x - ∑ j, a j * h j ∈ K ∩ J^(n+1)`.

Starting with `x ∈ K`, iterate this operation on the remainders. This gives
`x = ∑ j, (∑ n ≤ N, a j n) * h j + x_(N+1)`, with `x_(N+1) ∈ J^(N+1)` and
`a j n ∈ J^(n - d j)` for `n ≥ d j`. The coefficient partial sums stabilize modulo
each `J^k` once `N ≥ k + d j`. Their compatible residue classes therefore have unique
lifts `A j` by adic completeness. For each `k`, choose `N ≥ k + max j (d j)`;
then the displayed formula gives `x - ∑ j, A j * h j ∈ J^k`. Separatedness, which is
part of completeness, makes this difference zero. Thus the finite family `h` spans
`K`; the reverse inclusion holds since each `h j` belongs to `K`. An empty family
causes no exception: all initial forms vanish, and separatedness gives `K = 0`. -/
theorem fg_of_isAdicComplete_of_associatedGraded {A : Type u} [CommRing A]
    (J K : Ideal A) [IsAdicComplete J A] [IsNoetherianRing (associatedGraded J)] :
    K.FG := by
  classical
  obtain ⟨t, d, h, hhK, _, hstep⟩ := exists_associatedGraded_ideal_approximation J K
  let D := Finset.univ.sup d
  have hd (i : Fin t) : d i ≤ D := Finset.le_sup (Finset.mem_univ i)
  apply Submodule.fg_def.mpr
  refine ⟨Set.range h, Set.finite_range h, le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.mpr (by rintro y ⟨i, rfl⟩; exact hhK i)
  · intro x hx
    have hp (n : ℕ) (z : {y : A // y ∈ K ∧ y ∈ J ^ n}) :
        ∃ a : Fin t → A, (∀ i, a i ∈ J ^ (n - d i)) ∧
          z.val - ∑ i, a i * h i ∈ K ∧ z.val - ∑ i, a i * h i ∈ J ^ (n + 1) :=
      hstep n z.val z.property.1 z.property.2
    choose a ha hremK hremJ using hp
    let r : (n : ℕ) → {y : A // y ∈ K ∧ y ∈ J ^ n} :=
      fun n => Nat.rec ⟨x, hx, by simp⟩
        (fun n z => ⟨z.val - ∑ i, a n z i * h i, hremK n z, hremJ n z⟩) n
    let c (i : Fin t) (n : ℕ) : A := a n (r n) i
    let s (i : Fin t) (N : ℕ) : A := ∑ n ∈ Finset.range N, c i n
    have hdecay (i : Fin t) (n : ℕ) : c i n ∈ J ^ (n - d i) := ha n (r n) i
    have htel (N : ℕ) : x - ∑ i, s i N * h i = (r N).val := by
      induction N with
      | zero => simp [s, r]
      | succ N ih =>
        have hr : (r (N + 1)).val = (r N).val - ∑ i, c i N * h i := rfl
        rw [hr, ← ih]
        simp only [s, Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
        abel
    have hdiff (i : Fin t) (k m n : ℕ) (hmn : m ≤ n) (hkm : k + d i ≤ m) :
        s i n - s i m ∈ J ^ k := by
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have hc : c i n ∈ J ^ k :=
          (Ideal.pow_le_pow_right (by omega : k ≤ n - d i)) (hdecay i n)
        have hs : s i (n + 1) - s i m = (s i n - s i m) + c i n := by
          simp only [s, Finset.sum_range_succ]
          abel
        rw [hs]
        exact (J ^ k).add_mem ih hc
    have hlim (i : Fin t) : ∃ L : A, ∀ k, s i (k + D) - L ∈ J ^ k := by
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (M := A)
        (fun k => s i (k + D)) (by
          intro m n hmn
          rw [SModEq.sub_mem]
          have hm : m + d i ≤ m + D := Nat.add_le_add_left (hd i) m
          have he := (J ^ m).neg_mem (hdiff i m (m + D) (n + D) (by omega) hm)
          simpa only [Ideal.smul_eq_mul, Ideal.mul_top, neg_sub] using he)
      refine ⟨L, fun k => ?_⟩
      simpa only [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] using hL k
    choose L hL using hlim
    have heq : x = ∑ i, L i * h i := by
      apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
      intro k
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
      have hr : x - ∑ i, s i (k + D) * h i ∈ J ^ k := by
        rw [htel]
        exact (Ideal.pow_le_pow_right (by omega : k ≤ k + D)) (r (k + D)).property.2
      have hs : (∑ i, (s i (k + D) - L i) * h i) ∈ J ^ k :=
        Submodule.sum_mem _ (fun i _ => (J ^ k).mul_mem_right (h i) (hL i k))
      have hadd := (J ^ k).add_mem hr hs
      convert hadd using 1
      simp only [sub_mul, Finset.sum_sub_distrib]
      abel
    rw [heq]
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ (L i) (Submodule.subset_span (Set.mem_range_self i)))

end Ideal
