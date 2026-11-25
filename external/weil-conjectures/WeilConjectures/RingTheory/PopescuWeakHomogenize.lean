/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Homogenizing equations evaluated in a prime localization

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07F9,
`lemma-delocalize-weak`, the homogenization and target-denominator paragraphs.
(blueprint: lem-weil-pbc-popescu-weak-homogenize)
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial
open scoped BigOperators

/-- The monomial identity for partial homogenization, before clearing annihilators. -/
private theorem partial_homogenization_eval
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (n m : ℕ) (f : MvPolynomial (Fin (n + m)) R) (d : ℕ)
    (hd : ∀ e ∈ f.support,
      (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) ≤ d)
    (y : Fin (n + m) → A) (t : Fin (n + m + 2) → A) (w : A)
    (ht : ∀ i, t i.castSucc.succ = y i * w ^ (if n ≤ i.val then 1 else 0))
    (hw : t (Fin.last (n + m + 1)) = w) :
    aeval t (∑ e ∈ f.support,
      C (f.coeff e) * (∏ i : Fin (n + m), X i.castSucc.succ ^ e i) *
        X (Fin.last (n + m + 1)) ^
          (d - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)) =
      w ^ d * aeval y f := by
  classical
  have heval : aeval y f = ∑ e ∈ f.support,
      algebraMap R A (f.coeff e) * ∏ i : Fin (n + m), y i ^ e i :=
    eval₂_eq' _ _ _
  rw [heval]
  rw [Finset.mul_sum]
  simp only [map_sum, map_mul, map_prod, map_pow, aeval_C, aeval_X, hw]
  apply Finset.sum_congr rfl
  intro e he
  have hprod : (∏ i : Fin (n + m), t i.castSucc.succ ^ e i) =
      (∏ i : Fin (n + m), y i ^ e i) *
        w ^ (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) := by
    calc
      _ = ∏ i : Fin (n + m), y i ^ e i *
          w ^ (if n ≤ i.val then e i else 0) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [ht]
        split_ifs <;> simp [mul_pow]
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hprod]
  have hp : w ^ (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) *
      w ^ (d - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0) = w ^ d := by
    rw [← pow_add, Nat.add_sub_of_le (hd e he)]
  calc
    _ = (algebraMap R A (f.coeff e) * ∏ i : Fin (n + m), y i ^ e i) *
        (w ^ (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) *
          w ^ (d - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)) := by ring
    _ = _ := by rw [hp]; ring

/-- Homogenize only the last `m` variables and clear their values' denominators.
The first `n` values already belong to the unlocalized ring. No smoothness,
presentation of the source, or Popescu resolution is required here.
Source: Stacks Project, proof of Tag 07F9 (`lemma-delocalize-weak`), lines 2189–2211.
(blueprint: lem-weil-pbc-popescu-weak-homogenize)

Proof: Clear the denominators of the finite family `y` using Mathlib, obtaining
`w` outside `q` and numerators whose images are `w * y i`. Keep the first `n`
coordinates equal to `a`, and use the numerators for the extra coordinates. Choose
`dⱼ` to be the maximum extra-variable degree among the monomials of `fⱼ`, with maximum
of the empty support zero. Define `Fⱼ` by the displayed monomial formula, shifting
all old variables by one and multiplying by `X_last^(dⱼ-extra_degree)`. Assign the
first `n` coordinates their given values, the next `m` coordinates the
numerators, and the last coordinate `w`. In the localization, evaluating `Fⱼ`
equals `w^dⱼ` times the evaluation of `fⱼ`, hence is zero. For each `j`, the
localization equality criterion supplies an annihilator outside `q` for this
unlocalized evaluation. Let coordinate zero be their product. It remains outside
`q` and annihilates every evaluated `Fⱼ`. Thus evaluation kills `X₀*Fⱼ`.
Empty families use the finite-product conventions of Mathlib, and zero polynomials
use degree zero. The same construction works when `n=0`, `m=0`, or `c=0`. -/
theorem exists_homogenized_local_equations
    {R : Type u} {Λ : Type v} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (q : PrimeSpectrum Λ) (n m c : ℕ)
    (f : Fin c → MvPolynomial (Fin (n + m)) R)
    (a : Fin n → Λ) (y : Fin (n + m) → Localization.AtPrime q.asIdeal)
    (hy : ∀ i : Fin n, y (Fin.castAdd m i) =
      algebraMap Λ (Localization.AtPrime q.asIdeal) (a i))
    (hf : ∀ j, aeval y (f j) = 0) :
    ∃ (d : Fin c → ℕ) (F : Fin c → MvPolynomial (Fin (n + m + 2)) R)
      (l : Fin (n + m + 2) → Λ),
      (∀ j : Fin c, ∀ e ∈ (f j).support,
        (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) ≤ d j) ∧
      (∀ j : Fin c, F j =
        ∑ e ∈ (f j).support,
          MvPolynomial.C ((f j).coeff e) *
            (∏ i : Fin (n + m), X i.castSucc.succ ^ e i) *
            X (Fin.last (n + m + 1)) ^
              (d j - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)) ∧
      (∀ i : Fin n, l (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ = a i) ∧
      l 0 ∉ q.asIdeal ∧ l (Fin.last (n + m + 1)) ∉ q.asIdeal ∧
      (∀ j : Fin c, aeval l (X (0 : Fin (n + m + 2)) * F j) = 0) := by
  classical
  let L := Localization.AtPrime q.asIdeal
  let ι : Λ →+* L := algebraMap Λ L
  obtain ⟨w, hw⟩ := IsLocalization.exist_integer_multiples_of_finite q.asIdeal.primeCompl y
  have hz : ∀ i, ∃ z : Λ, ι z = ι w * y i := by
    intro i
    obtain ⟨zi, hzi⟩ := hw i
    exact ⟨zi, by simpa only [Algebra.smul_def] using hzi⟩
  choose z hz using hz
  let b : Fin (n + m) → Λ := fun i ↦ if h : i.val < n then a ⟨i.val, h⟩ else z i
  have hb : ∀ i, ι (b i) = y i * ι w ^ (if n ≤ i.val then 1 else 0) := by
    intro i
    by_cases hi : i.val < n
    · have hcast : Fin.castAdd m (⟨i.val, hi⟩ : Fin n) = i := Fin.ext rfl
      have h := hy ⟨i.val, hi⟩
      rw [hcast] at h
      simp [b, hi, Nat.not_le.mpr hi, h, ι, L]
    · simp [b, hi, Nat.le_of_not_gt hi, hz, mul_comm]
  let d : Fin c → ℕ := fun j ↦ (f j).support.sup
    (fun e ↦ ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)
  have hd : ∀ j e, e ∈ (f j).support →
      (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) ≤ d j := by
    intro j e he
    exact Finset.le_sup (f := fun e ↦
      ∑ i : Fin (n + m), if n ≤ i.val then e i else 0) he
  let F : Fin c → MvPolynomial (Fin (n + m + 2)) R := fun j ↦
    ∑ e ∈ (f j).support,
      C ((f j).coeff e) * (∏ i : Fin (n + m), X i.castSucc.succ ^ e i) *
        X (Fin.last (n + m + 1)) ^
          (d j - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)
  let l' : Λ → Fin (n + m + 2) → Λ := fun u ↦ Fin.cases u (Fin.lastCases (w : Λ) b)
  have hl : ∀ u i, l' u i.castSucc.succ = b i := by
    intro u i
    simp [l']
  have hlw : ∀ u, l' u (Fin.last (n + m + 1)) = w := by
    intro u
    change Fin.cases u (Fin.lastCases (w : Λ) b) (Fin.last (n + m)).succ = (w : Λ)
    rw [Fin.cases_succ, Fin.lastCases_last]
  have hzero : ∀ j, ι (aeval (l' 1) (F j)) = 0 := by
    intro j
    change (IsScalarTower.toAlgHom R Λ L) (aeval (l' 1) (F j)) = 0
    rw [MvPolynomial.comp_aeval_apply (l' 1) (IsScalarTower.toAlgHom R Λ L)]
    change aeval (fun i ↦ ι (l' 1 i)) (F j) = 0
    rw [partial_homogenization_eval n m (f j) (d j) (hd j) y
      (fun i ↦ ι (l' 1 i)) (ι w) (by intro i; rw [hl]; exact hb i)
      (by rw [hlw])]
    rw [hf, mul_zero]
  have hu : ∀ j, ∃ u : q.asIdeal.primeCompl, (u : Λ) * aeval (l' 1) (F j) = 0 := by
    intro j
    exact (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl L _).mp (hzero j)
  choose u hu using hu
  let U : q.asIdeal.primeCompl := ∏ j : Fin c, u j
  have hU : ∀ j, (U : Λ) * aeval (l' 1) (F j) = 0 := by
    intro j
    have hprod : (U : Λ) =
        (∏ k ∈ Finset.univ.erase j, (u k : Λ)) * (u j : Λ) := by
      simp only [U, Submonoid.coe_finsetProd]
      exact (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
    rw [hprod, mul_assoc, hu, mul_zero]
  have heval : ∀ v j, aeval (l' v) (F j) = aeval (l' 1) (F j) := by
    intro v j
    simp only [F, map_sum, map_mul, map_prod, map_pow, aeval_C, aeval_X, hl, hlw]
  refine ⟨d, F, l' U, hd, fun _ ↦ rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hl]
    simp [b, i.isLt]
  · change (U : Λ) ∈ q.asIdeal.primeCompl
    exact U.property
  · rw [hlw]
    exact w.property
  · intro j
    rw [map_mul, aeval_X]
    change (U : Λ) * aeval (l' U) (F j) = 0
    rw [heval]
    exact hU j

end Algebra
