/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizations of the auxiliary algebra in height-zero delocalization

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 16.9.4, Tag 07FA
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations).

The first conjunct asserts an A-algebra map from the auxiliary quotient B to the
localization of the polynomial ring over C, with prescribed images of x, y, z, and t.
It also asserts an algebra equivalence between B_z and that target restricting to the map.
This is the first localization assertion in Stacks Project Tag 07FA; its proof uses
universal properties of polynomial rings, quotients, and localization and checks generators.

(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations-part1).

Proof: construct the maps by the universal properties of multivariate polynomial rings,
ideal quotients, and localization away from one element; verify the displayed generator
formulas and use extensionality on polynomial generators and localization.
the maps by universal properties of polynomial rings, quotients, and localization and checks
the generators.
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
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations-part1). -/
theorem popescu_auxiliaryAlgebra_localizations_part1
    (A : Type u) [CommRing A] (n m r : ℕ) (hr : 1 ≤ r)
    (f : Fin m → MvPolynomial (Fin n) A) :
    (∃ phi : (MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A ⧸
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
                  X (Sum.inr (Sum.inl i)))))) →ₐ[A]
        Localization.Away (X (Sum.inr ()) :
          MvPolynomial ((Fin r × Fin m) ⊕ Unit)
            (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))),
      (∀ k : Fin n,
        phi (Ideal.Quotient.mkₐ A
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
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) =
          algebraMap (MvPolynomial ((Fin r × Fin m) ⊕ Unit)
              (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))) _
            (MvPolynomial.C (Ideal.Quotient.mkₐ A (Ideal.span (Set.range f)) (X k)))) ∧
      (∀ i : Fin r,
        phi (Ideal.Quotient.mkₐ A
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
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) = 0) ∧
      phi (Ideal.Quotient.mkₐ A
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
          MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) =
        algebraMap (MvPolynomial ((Fin r × Fin m) ⊕ Unit)
            (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))) _
          (X (Sum.inr ())) ∧
      (∀ ij : Fin r × Fin m,
        phi (Ideal.Quotient.mkₐ A
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
          (X (Sum.inr (Sum.inr (Sum.inr ij))) :
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) =
          algebraMap (MvPolynomial ((Fin r × Fin m) ⊕ Unit)
              (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))) _
            (X (Sum.inl ij))) ∧
      ∃ e : Localization.Away (Ideal.Quotient.mkₐ A
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
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) ≃ₐ[A]
          Localization.Away (X (Sum.inr ()) :
            MvPolynomial ((Fin r × Fin m) ⊕ Unit)
              (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))),
        ∀ b : MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A ⧸
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
                    X (Sum.inr (Sum.inl i))))),
          e (algebraMap _ _ b) = phi b)  := by
  classical
  have _ := hr
  let S := MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A
  let x : Fin n → S := fun k ↦ X (Sum.inl k)
  let y : Fin r → S := fun i ↦ X (Sum.inr (Sum.inl i))
  let z : S := X (Sum.inr (Sum.inr (Sum.inl ())))
  let t : Fin r × Fin m → S := fun ij ↦ X (Sum.inr (Sum.inr (Sum.inr ij)))
  let J : Ideal S := Ideal.span
    (Set.range (fun j ↦ aeval x (f j) - ∑ i : Fin r, y i * t (i, j)) ∪
      Set.range (fun i ↦ z * y i))
  let B := S ⧸ J
  let q : S →ₐ[A] B := Ideal.Quotient.mkₐ A J
  let C₀ := MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)
  let c : MvPolynomial (Fin n) A →ₐ[A] C₀ :=
    Ideal.Quotient.mkₐ A (Ideal.span (Set.range f))
  let D := MvPolynomial ((Fin r × Fin m) ⊕ Unit) C₀
  let w : D := X (Sum.inr ())
  let T := Localization.Away w
  let d : D →ₐ[A] T := IsScalarTower.toAlgHom A D T
  let cx : C₀ →ₐ[A] T := d.comp (IsScalarTower.toAlgHom A C₀ D)
  let g : (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) → T :=
    Sum.elim (fun k ↦ cx (c (X k)))
      (Sum.elim (fun _ ↦ 0)
        (Sum.elim (fun _ ↦ d w) (fun ij ↦ d (X (Sum.inl ij)))))
  let F : S →ₐ[A] T := aeval g
  have Fx (k : Fin n) : F (x k) = cx (c (X k)) := by
    exact aeval_X g (Sum.inl k)
  have Fy (i : Fin r) : F (y i) = 0 := by
    exact aeval_X g (Sum.inr (Sum.inl i))
  have Fz : F z = d w := by
    exact aeval_X g (Sum.inr (Sum.inr (Sum.inl ())))
  have Ft (ij : Fin r × Fin m) : F (t ij) = d (X (Sum.inl ij)) := by
    exact aeval_X g (Sum.inr (Sum.inr (Sum.inr ij)))
  have Ff (p : MvPolynomial (Fin n) A) : F (aeval x p) = cx (c p) := by
    have h : F.comp (aeval x) = cx.comp c := by
      apply MvPolynomial.algHom_ext
      intro k
      simpa using Fx k
    exact AlgHom.congr_fun h p
  have FJ : ∀ a ∈ J, F a = 0 := by
    change J ≤ RingHom.ker F.toRingHom
    apply Ideal.span_le.mpr
    rintro a (ha | ha)
    · obtain ⟨j, rfl⟩ := ha
      change F (aeval x (f j) - ∑ i : Fin r, y i * t (i, j)) = 0
      rw [map_sub, Ff]
      have hc : c (f j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
      simp [hc, map_sum, map_mul, Fy]
    · obtain ⟨i, rfl⟩ := ha
      change F (z * y i) = 0
      simp [map_mul, Fy]
  let phi : B →ₐ[A] T := Ideal.Quotient.liftₐ J F FJ
  have phiq (a : S) : phi (q a) = F a :=
    AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp J F FJ) a
  refine ⟨phi, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (phiq (x k)).trans (Fx k)
  · intro i
    exact (phiq (y i)).trans (Fy i)
  · exact (phiq z).trans Fz
  · intro ij
    exact (phiq (t ij)).trans (Ft ij)
  · let L := Localization.Away (q z)
    let b : B →ₐ[A] L := IsScalarTower.toAlgHom A B L
    have zy (i : Fin r) : q (z * y i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
    have by0 (i : Fin r) : b (q (y i)) = 0 := by
      apply (IsLocalization.Away.algebraMap_isUnit (S := L) (q z)).mul_left_cancel
      change b (q z) * b (q (y i)) = b (q z) * 0
      rw [← map_mul, ← map_mul, zy, map_zero, mul_zero]
    let H : MvPolynomial (Fin n) A →ₐ[A] L := (b.comp q).comp (aeval x)
    have Hf (j : Fin m) : H (f j) = 0 := by
      have hq : q (aeval x (f j) - ∑ i : Fin r, y i * t (i, j)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨j, rfl⟩))
      have h := congrArg b hq
      simp only [map_sub, map_sum, map_mul, by0, zero_mul, Finset.sum_const_zero,
        sub_zero, map_zero] at h
      exact h
    have HI : ∀ a ∈ Ideal.span (Set.range f), H a = 0 := by
      change Ideal.span (Set.range f) ≤ RingHom.ker H.toRingHom
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Hf j
    let c' : C₀ →ₐ[A] L := Ideal.Quotient.liftₐ (Ideal.span (Set.range f)) H HI
    have c'c (p : MvPolynomial (Fin n) A) : c' (c p) = H p :=
      AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp (Ideal.span (Set.range f)) H HI) p
    let v : ((Fin r × Fin m) ⊕ Unit) → L :=
      Sum.elim (fun ij ↦ b (q (t ij))) (fun _ ↦ b (q z))
    let G : D →ₐ[A] L := aevalTower c' v
    have Gw : G w = b (q z) := aevalTower_X c' v (Sum.inr ())
    have Gt (ij : Fin r × Fin m) : G (X (Sum.inl ij)) = b (q (t ij)) :=
      aevalTower_X c' v (Sum.inl ij)
    have GC (a : C₀) : G (MvPolynomial.C a) = c' a := aevalTower_C c' v a
    have phiz : phi (q z) = d w := (phiq z).trans Fz
    have unitF : IsUnit (phi (q z)) := by
      rw [phiz]
      exact IsLocalization.Away.algebraMap_isUnit (S := T) w
    let forward : L →ₐ[A] T := IsLocalization.Away.liftAlgHom (q z) unitF
    have forward_b (a : B) : forward (b a) = phi a :=
      IsLocalization.Away.lift_eq (q z) unitF a
    have unitG : IsUnit (G w) := by
      rw [Gw]
      exact IsLocalization.Away.algebraMap_isUnit (S := L) (q z)
    let backward : T →ₐ[A] L := IsLocalization.Away.liftAlgHom w unitG
    have backward_d (a : D) : backward (d a) = G a :=
      IsLocalization.Away.lift_eq w unitG a
    have backward_cx (p : MvPolynomial (Fin n) A) :
        backward (cx (c p)) = b (q (aeval x p)) := by
      change backward (d (MvPolynomial.C (c p))) = _
      rw [backward_d, GC, c'c]
      rfl
    have forward_c' : forward.comp c' = cx := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro k
      change forward (c' (c (X k))) = cx (c (X k))
      rw [c'c]
      change forward (b (q (aeval x (X k)))) = _
      rw [aeval_X, forward_b, phiq, Fx]
    have left : backward.comp forward = AlgHom.id A L := by
      apply IsLocalization.algHom_ext (Submonoid.powers (q z))
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro a
      change backward (forward (b (q (X a)))) = b (q (X a))
      rw [forward_b, phiq]
      rcases a with k | i | u | ij
      · change backward (F (x k)) = b (q (x k))
        rw [Fx, backward_cx, aeval_X]
      · change backward (F (y i)) = b (q (y i))
        rw [Fy, map_zero, by0]
      · cases u
        change backward (F z) = b (q z)
        rw [Fz, backward_d, Gw]
      · change backward (F (t ij)) = b (q (t ij))
        rw [Ft, backward_d, Gt]
    have right : forward.comp backward = AlgHom.id A T := by
      apply IsLocalization.algHom_ext (Submonoid.powers w)
      apply MvPolynomial.algHom_ext'
      · apply AlgHom.ext
        intro a
        change forward (backward (d (MvPolynomial.C a))) = d (MvPolynomial.C a)
        rw [backward_d, GC]
        exact AlgHom.congr_fun forward_c' a
      · intro a
        change forward (backward (d (X a))) = d (X a)
        rw [backward_d]
        rcases a with ij | u
        · rw [Gt, forward_b, phiq, Ft]
        · cases u
          change forward (G w) = d w
          rw [Gw, forward_b, phiq, Fz]
    refine ⟨AlgEquiv.ofAlgHom forward backward right left, ?_⟩
    intro a
    exact forward_b a

end Algebra
