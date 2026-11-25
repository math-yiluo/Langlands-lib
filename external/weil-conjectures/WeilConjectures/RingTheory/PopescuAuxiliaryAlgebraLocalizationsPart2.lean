/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Localizations of the auxiliary algebra in height-zero delocalization

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 16.9.4, Tag 07FA
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations).

The second conjunct asserts an A-algebra equivalence for every l : Fin r between
the localization away from y_l of Q_l and the localization B_{y_l}. The inverse sends
z to 0 and t_(l,j) to y_l⁻¹ (f_j − Σ_{i ≠ l} y_i t_(i,j)), with the stated formulas.
This is the second localization assertion in Stacks Project Tag 07FA; its proof uses
universal properties of polynomial rings, quotients, and localization and checks generators.

(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations-part2).

Proof: construct the maps by the universal properties of multivariate polynomial rings,
ideal quotients, and localization away from one element; verify the displayed generator
formulas and use extensionality on polynomial generators and localization.
-/

@[expose] public section

universe u

open MvPolynomial
open scoped BigOperators

namespace Algebra


/-- This intermediate statement is the corresponding localization conjunct from Stacks
Project Tag 07FA.
The maps are constructed by the universal properties of multivariate polynomial rings, ideal
quotients, and localization away from one element; the displayed generator formulas and
extensionality on generators establish the assertion.
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations-part2). -/
theorem popescu_auxiliaryAlgebra_localizations_part2
    (A : Type u) [CommRing A] (n m r : ℕ) (hr : 1 ≤ r)
    (f : Fin m → MvPolynomial (Fin n) A) :
    (∀ l : Fin r,
      ∃ e : Localization.Away (X (Sum.inr (Sum.inl l)) :
            MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A) ≃ₐ[A]
          Localization.Away (Ideal.Quotient.mkₐ A
            (Ideal.span
              (Set.range (fun j : Fin m =>
                  aeval (fun k : Fin n =>
                    (X (Sum.inl k) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                    ∑ i : Fin r,
                      (X (Sum.inr (Sum.inl i)) :
                        MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                      X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                Set.range (fun i : Fin r =>
                  (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inl i)))))
            (X (Sum.inr (Sum.inl l)) :
              MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)),
        (∀ a : MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A,
          e (algebraMap _ _ a) = algebraMap _ _
            (aeval
              (Sum.elim
                (fun k : Fin n =>
                  Ideal.Quotient.mkₐ A
                  (Ideal.span
                    (Set.range (fun j : Fin m =>
                        aeval (fun k : Fin n =>
                          (X (Sum.inl k) :
                            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                          ∑ i : Fin r,
                            (X (Sum.inr (Sum.inl i)) :
                              MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                            X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                      Set.range (fun i : Fin r =>
                        (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                          MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                          X (Sum.inr (Sum.inl i)))))
                  (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A))
                (Sum.elim
                  (fun i : Fin r =>
                    Ideal.Quotient.mkₐ A
                    (Ideal.span
                      (Set.range (fun j : Fin m =>
                          aeval (fun k : Fin n =>
                            (X (Sum.inl k) :
                              MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                            ∑ i : Fin r,
                              (X (Sum.inr (Sum.inl i)) :
                                MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                              X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                        Set.range (fun i : Fin r =>
                          (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                            X (Sum.inr (Sum.inl i)))))
                    (X (Sum.inr (Sum.inl i)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A))
                  (fun ij : {i : Fin r // i ≠ l} × Fin m =>
                    Ideal.Quotient.mkₐ A
                    (Ideal.span
                      (Set.range (fun j : Fin m =>
                          aeval (fun k : Fin n =>
                            (X (Sum.inl k) :
                              MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                            ∑ i : Fin r,
                              (X (Sum.inr (Sum.inl i)) :
                                MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                              X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                        Set.range (fun i : Fin r =>
                          (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                            X (Sum.inr (Sum.inl i)))))
                    (X (Sum.inr (Sum.inr (Sum.inr (ij.1.val, ij.2)))) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)))) a)) ∧
        e.symm (algebraMap _ _ (Ideal.Quotient.mkₐ A
          (Ideal.span
            (Set.range (fun j : Fin m =>
                aeval (fun k : Fin n =>
                  (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                  ∑ i : Fin r,
                    (X (Sum.inr (Sum.inl i)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
              Set.range (fun i : Fin r =>
                (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                  X (Sum.inr (Sum.inl i)))))
          (X (Sum.inr (Sum.inr (Sum.inl ()))) :
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A))) = 0 ∧
        ∀ j : Fin m,
          e.symm (algebraMap _ _ (Ideal.Quotient.mkₐ A
              (Ideal.span
                (Set.range (fun j : Fin m =>
                    aeval (fun k : Fin n =>
                      (X (Sum.inl k) :
                        MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                      ∑ i : Fin r,
                        (X (Sum.inr (Sum.inl i)) :
                          MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                        X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                  Set.range (fun i : Fin r =>
                    (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                      X (Sum.inr (Sum.inl i)))))
              (X (Sum.inr (Sum.inr (Sum.inr (l, j)))) :
                MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A))) =
            IsLocalization.Away.invSelf
                (S := Localization.Away (X (Sum.inr (Sum.inl l)) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A))
                (X (Sum.inr (Sum.inl l)) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A) *
              algebraMap
                (MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A) _
                (aeval (fun k : Fin n => (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A)) (f j) -
                  ∑ i : {i : Fin r // i ≠ l},
                    (X (Sum.inr (Sum.inl i.val)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A) *
                      X (Sum.inr (Sum.inr (i, j)))))  := by
  classical
  have _ := hr
  intro l
  let P := MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A
  let Q := MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A
  let xp : Fin n → P := fun k => X (Sum.inl k)
  let yp : Fin r → P := fun i => X (Sum.inr (Sum.inl i))
  let zp : P := X (Sum.inr (Sum.inr (Sum.inl ())))
  let tp : Fin r → Fin m → P := fun i j => X (Sum.inr (Sum.inr (Sum.inr (i, j))))
  let xq : Fin n → Q := fun k => X (Sum.inl k)
  let yq : Fin r → Q := fun i => X (Sum.inr (Sum.inl i))
  let tq : {i : Fin r // i ≠ l} → Fin m → Q := fun i j => X (Sum.inr (Sum.inr (i, j)))
  let rel : Fin m → P := fun j => aeval xp (f j) - ∑ i, yp i * tp i j
  let J : Ideal P := Ideal.span (Set.range rel ∪ Set.range (fun i => zp * yp i))
  let B := P ⧸ J
  let q : P →ₐ[A] B := Ideal.Quotient.mkₐ A J
  let L := Localization.Away (yq l)
  let T := Localization.Away (q (yp l))
  let _ : CommRing L := inferInstance
  let _ : CommRing T := inferInstance
  let ν : Q →ₐ[A] L := IsScalarTower.toAlgHom A Q L
  let μ : B →ₐ[A] T := IsScalarTower.toAlgHom A B T
  let α : Q →ₐ[A] B := aeval (Sum.elim (fun k => q (xp k))
    (Sum.elim (fun i => q (yp i)) (fun ij => q (tp ij.1.val ij.2))))
  let d : L := IsLocalization.Away.invSelf (yq l)
  let v : Fin m → L := fun j => d * ν (aeval xq (f j) - ∑ i, yq i.val * tq i j)
  let β : P →ₐ[A] L := aeval (Sum.elim (fun k => ν (xq k))
    (Sum.elim (fun i => ν (yq i))
      (Sum.elim (fun _ => 0) (fun ij => if h : ij.1 = l then v ij.2
        else ν (tq ⟨ij.1, h⟩ ij.2)))))
  have hd : ν (yq l) * d = 1 := IsLocalization.Away.mul_invSelf (yq l)
  have hβx (k : Fin n) : β (xp k) = ν (xq k) := by simp [P, β, xp]
  have hβy (i : Fin r) : β (yp i) = ν (yq i) := by simp [P, β, yp]
  have hβz : β zp = 0 := by simp [P, β, zp]
  have hβt (i : Fin r) (j : Fin m) : β (tp i j) =
      if h : i = l then v j else ν (tq ⟨i, h⟩ j) := by simp [P, β, tp]
  have hβtl (j : Fin m) : β (tp l j) = v j := by rw [hβt, dite_eq_left rfl]
  have hβtn (i : {i : Fin r // i ≠ l}) (j : Fin m) :
      β (tp i.val j) = ν (tq i j) := by rw [hβt, dite_eq_right i.property]
  have hβf (j : Fin m) : β (aeval xp (f j)) = ν (aeval xq (f j)) := by
    have h : β.comp (aeval xp) = ν.comp (aeval xq) := by
      apply MvPolynomial.algHom_ext
      intro k
      simp only [AlgHom.comp_apply, aeval_X, hβx]
    exact AlgHom.congr_fun h (f j)
  have hβ : ∀ a ∈ J, β a = 0 := by
    change J ≤ RingHom.ker β.toRingHom
    apply Ideal.span_le.mpr
    rintro a (⟨j, rfl⟩ | ⟨i, rfl⟩)
    · change β (rel j) = 0
      simp only [rel, map_sub, map_sum, map_mul, hβf, hβy]
      rw [Fintype.sum_eq_add_sum_subtype_ne _ l]
      simp only [hβtl, hβtn]
      simp only [v, map_sub, map_sum, map_mul]
      rw [← mul_assoc, hd, one_mul]
      ring
    · change β (zp * yp i) = 0
      rw [map_mul, hβz, zero_mul]
  let b : B →ₐ[A] L := Ideal.Quotient.liftₐ J β hβ
  have hb (a : P) : b (q a) = β a := by
    exact congrArg (fun h : P →ₐ[A] L => h a) (Ideal.Quotient.liftₐ_comp J β hβ)
  have hαx (k : Fin n) : α (xq k) = q (xp k) := by simp [Q, α, xq]
  have hαy (i : Fin r) : α (yq i) = q (yp i) := by simp [Q, α, yq]
  have hαt (i : {i : Fin r // i ≠ l}) (j : Fin m) :
      α (tq i j) = q (tp i.val j) := by simp [Q, α, tq]
  have hα : α (yq l) = q (yp l) := hαy l
  have hfu : IsUnit ((μ.comp α) (yq l)) := by
    simpa [hα, μ] using
      (IsLocalization.Away.algebraMap_isUnit (S := T) (q (yp l)))
  let F : L →ₐ[A] T := IsLocalization.Away.liftAlgHom (yq l) hfu
  have hF (a : Q) : F (ν a) = μ (α a) := by
    exact IsLocalization.Away.lift_eq (yq l) hfu a
  have hby : b (q (yp l)) = ν (yq l) := by rw [hb, hβy]
  have hgu : IsUnit (b (q (yp l))) := by
    rw [hby]
    exact IsLocalization.Away.algebraMap_isUnit (yq l)
  let G : T →ₐ[A] L := IsLocalization.Away.liftAlgHom (q (yp l)) hgu
  have hG (a : B) : G (μ a) = b a := by
    exact IsLocalization.Away.lift_eq (q (yp l)) hgu a
  have hGF : G.comp F = AlgHom.id A L := by
    apply IsLocalization.algHom_ext (Submonoid.powers (yq l))
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with k | (i | ij)
    · change G (F (ν (xq k))) = ν (xq k)
      rw [hF, hαx, hG, hb, hβx]
    · change G (F (ν (yq i))) = ν (yq i)
      rw [hF, hαy, hG, hb, hβy]
    · change G (F (ν (tq ij.1 ij.2))) = ν (tq ij.1 ij.2)
      rw [hF, hαt, hG, hb, hβt, dite_eq_right ij.1.property]
  have hFx (k : Fin n) : F (ν (xq k)) = μ (q (xp k)) := (hF (xq k)).trans (congrArg μ (hαx k))
  have hFy (i : Fin r) : F (ν (yq i)) = μ (q (yp i)) := (hF (yq i)).trans (congrArg μ (hαy i))
  have hFt (i : {i : Fin r // i ≠ l}) (j : Fin m) :
      F (ν (tq i j)) = μ (q (tp i.val j)) := (hF (tq i j)).trans (congrArg μ (hαt i j))
  have hFf (j : Fin m) : F (ν (aeval xq (f j))) = μ (q (aeval xp (f j))) := by
    have h : (F.comp ν).comp (aeval xq) = (μ.comp q).comp (aeval xp) := by
      apply MvPolynomial.algHom_ext
      intro k
      simp only [AlgHom.comp_apply, aeval_X, hFx]
    exact AlgHom.congr_fun h (f j)
  have hdF : μ (q (yp l)) * F d = 1 := by
    have h := congrArg F hd
    simpa only [map_mul, map_one, hFy] using h
  have hJ (a : P) (ha : a ∈ J) : μ (q a) = 0 := by
    have hq : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [hq, map_zero]
  have hz : μ (q zp) = 0 := by
    have h := hJ (zp * yp l) (Ideal.subset_span (Or.inr ⟨l, rfl⟩))
    simp only [map_mul] at h
    calc
      μ (q zp) = μ (q zp) * (μ (q (yp l)) * F d) := by rw [hdF, mul_one]
      _ = 0 := by rw [← mul_assoc, h, zero_mul]
  have hv (j : Fin m) : F (v j) = μ (q (tp l j)) := by
    have h := hJ (rel j) (Ideal.subset_span (Or.inl ⟨j, rfl⟩))
    simp only [rel, map_sub, map_sum, map_mul, sub_eq_zero] at h
    rw [Fintype.sum_eq_add_sum_subtype_ne _ l] at h
    change F (d * ν (aeval xq (f j) - ∑ i, yq i.val * tq i j)) = _
    simp only [map_mul, map_sub, map_sum, hFf, hFy, hFt]
    rw [h, add_sub_cancel_right]
    calc
      F d * (μ (q (yp l)) * μ (q (tp l j))) =
          (μ (q (yp l)) * F d) * μ (q (tp l j)) := by ring
      _ = μ (q (tp l j)) := by rw [hdF, one_mul]
  have hFG : F.comp G = AlgHom.id A T := by
    apply IsLocalization.algHom_ext (Submonoid.powers (q (yp l)))
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with k | (i | (u | ij))
    · change F (G (μ (q (xp k)))) = μ (q (xp k))
      rw [hG, hb, hβx, hFx]
    · change F (G (μ (q (yp i)))) = μ (q (yp i))
      rw [hG, hb, hβy, hFy]
    · cases u
      change F (G (μ (q zp))) = μ (q zp)
      rw [hG, hb, hβz, map_zero, hz]
    · change F (G (μ (q (tp ij.1 ij.2)))) = μ (q (tp ij.1 ij.2))
      rw [hG, hb, hβt]
      split_ifs with hi
      · subst hi
        exact hv ij.2
      · exact hFt ⟨ij.1, hi⟩ ij.2
  let e : L ≃ₐ[A] T := AlgEquiv.ofAlgHom F G hFG hGF
  refine ⟨e, ?_, ?_, ?_⟩
  · exact hF
  · change G (μ (q zp)) = 0
    rw [hG, hb]
    exact hβz
  · intro j
    change G (μ (q (tp l j))) = v j
    rw [hG, hb]
    exact hβtl j

end Algebra
