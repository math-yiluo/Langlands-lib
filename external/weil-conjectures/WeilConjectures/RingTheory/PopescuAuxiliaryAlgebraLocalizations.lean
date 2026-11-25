/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra
import WeilConjectures.RingTheory.PopescuAuxiliaryAlgebraLocalizationsPart1
import WeilConjectures.RingTheory.PopescuAuxiliaryAlgebraLocalizationsPart2

/-!
# Localizations of the auxiliary algebra in height-zero delocalization

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 16.9.4, Tag 07FA
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations).
-/

@[expose] public section

universe u

open MvPolynomial
open scoped BigOperators

namespace Algebra

/-- The two localizations of the auxiliary algebra in Stacks Project, Tag 07FA.
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations)

The statement is written without `let`. The variable indices of
`S = MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A` are, in order, `x`, `y`, `z`
and `t`; `B` is `S` modulo the span of the `f_j - ∑ y_i t_ij` and the `z y_i`, `C` is
`MvPolynomial (Fin n) A` modulo the span of the `f_j`, and the variable indices of
`T = MvPolynomial ((Fin r × Fin m) ⊕ Unit) C` are `t` and `z`. In
`Q_l = MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i // i ≠ l} × Fin m))) A` the row of `t`
indexed by `l` is omitted.

Proof (the seven steps of the node):
1. Use the universal properties of multivariate polynomials, quotients, and localization
away from an element (the three statement dependencies).
2. Evaluate `x` in `C`, `y` at zero, and `z,t` at the corresponding variables in `Tz`.
Both families of defining relations vanish. Descend to `phi : B →ₐ[A] Tz` and localize at `z`.
3. In `Bz`, the relations `z*y = 0` give `y = 0`, and hence every `f j` vanishes.
Thus the map from the original polynomial ring factors through `C`; adjoining `t,z`
and inverting `z` constructs the reverse map.
4. The composites fix every generator. Quotient and localization uniqueness show they
are identity maps. This proves the first equivalence, with its prescribed images.
5. For each `l`, evaluate the variables of `Q` at their classes in `B` and localize at `y l`.
6. Construct the reverse map by sending `z` to zero and each omitted `t (l,j)` to
`(y l)⁻¹ * (f j - ∑ i ≠ l, y i * t (i,j))`. The defining relations vanish, so it
descends to `B` and then localizes at `y l`.
7. In `By`, `z = 0` and the relation for `f j` determines `t (l,j)` by precisely this
formula. Both composites fix the generators, proving the second equivalence.
The polynomial, quotient, and localization notions are respectively
`def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-algebra-hom-quotient`, and
`def-weil-ring-localization-away`. -/
theorem popescu_auxiliaryAlgebra_localizations
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
          e (algebraMap _ _ b) = phi b) ∧
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
                      X (Sum.inr (Sum.inr (i, j))))) := by
  exact ⟨popescu_auxiliaryAlgebra_localizations_part1 A n m r hr f,
    popescu_auxiliaryAlgebra_localizations_part2 A n m r hr f⟩

end Algebra
