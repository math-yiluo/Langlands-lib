/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import WeilConjectures.RingTheory.PopescuPolynomialCoefficientLocalizationSmooth
import WeilConjectures.RingTheory.SingularIdealLocalizationSmooth
import WeilConjectures.RingTheory.SmoothOfLocalizationSpanUniverses

/-!
# The polynomial quotient used in separable Popescu preparation

Source: Stacks Project, proof of Lemma 07FE, first paragraph.
-/

@[expose] public section

universe u v

namespace Algebra

/-- The equations of the explicit quotient in Stacks, proof of Lemma 07FE.
(blueprint: lem-weil-pbc-popescu-polynomial-quotient-smooth). -/
noncomputable def popescuPolynomialRelations {A : Type v} [CommRing A] (d n : ℕ) {m : ℕ}
    (a : Fin m → A) (i : Fin d) : MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A :=
  MvPolynomial.X (Sum.inl i) ^ n -
    ∑ j : Fin m, MvPolynomial.X (Sum.inr (i, j)) * MvPolynomial.C (a j)

/-- The actual polynomial quotient, before improving its presentation.
(blueprint: lem-weil-pbc-popescu-polynomial-quotient-smooth). -/
abbrev PopescuPolynomialQuotient {A : Type v} [CommRing A] (d n : ℕ) {m : ℕ}
    (a : Fin m → A) :=
  MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A ⧸
    Ideal.span (Set.range (popescuPolynomialRelations d n a))

/-- The polynomial base map sends `X i` to the class of the corresponding variable.
(blueprint: lem-weil-pbc-popescu-polynomial-quotient-smooth). -/
noncomputable def popescuPolynomialBaseMap {k : Type u} {A : Type v}
    [CommRing k] [CommRing A] [Algebra k A] (d n : ℕ) {m : ℕ} (a : Fin m → A) :
    MvPolynomial (Fin d) k →ₐ[k] PopescuPolynomialQuotient d n a :=
  MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)))

/-- The explicit quotient is finitely presented over the polynomial base; its opens at
singular-ideal generators and at the base variables are smooth.
Source: Stacks Project, proof of Lemma 07FE, first paragraph.
(blueprint: lem-weil-pbc-popescu-polynomial-quotient-smooth).

Proof: write `P=A[X_i,Z_ij]` and impose the finitely many displayed relations. The
finite presentation of A over k, together with the finitely many Z variables and
relations, gives a finite presentation over R=k[X_i]. For each generator a_j,
A_(a_j) is smooth over k because a_j belongs to H_(A/k). Invert a_j and solve each
relation uniquely for Z_ij; this identifies B_(a_j) with a polynomial ring in the
remaining Z variables over A_(a_j)[X_i]. Smoothness follows by base change,
polynomial smoothness and composition. In B_(X_i), the equation X_i^n=Σ Z_ij a_j
shows that the images of all a_j generate the unit ideal. Smoothness is local on
this principal cover, so B_(X_i) is smooth over R. If m=0, that equation says
X_i^n=0; its localization is the zero ring, which is smooth over R. If d=0,
there are no relations or X opens and the construction is A itself. These
arguments apply also when A or a localization is the zero ring. -/
theorem popescuPolynomialQuotient_smooth
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [FinitePresentation k A] (d n : ℕ) (hn : 1 ≤ n) {m : ℕ} (a : Fin m → A)
    (ha : Ideal.span (Set.range a) = singularIdeal k A) :
    let B := PopescuPolynomialQuotient d n a
    letI := (popescuPolynomialBaseMap (k := k) d n a).toRingHom.toAlgebra
    FinitePresentation (MvPolynomial (Fin d) k) B ∧
      (∀ j : Fin m, Smooth (MvPolynomial (Fin d) k)
        (Localization.Away (algebraMap A B (a j)))) ∧
      ∀ i : Fin d, Smooth (MvPolynomial (Fin d) k)
        (Localization.Away
          (algebraMap (MvPolynomial (Fin d) k) B (MvPolynomial.X i))) := by
  classical
  let B := PopescuPolynomialQuotient d n a
  let : Algebra (MvPolynomial (Fin d) k) B :=
    (popescuPolynomialBaseMap (k := k) d n a).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin d) k) B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      exact (popescuPolynomialBaseMap (k := k) d n a).commutes r |>.symm
  have : FinitePresentation k B :=
    FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  have hfp : FinitePresentation (MvPolynomial (Fin d) k) B :=
    FinitePresentation.of_restrict_scalars_finitePresentation k (MvPolynomial (Fin d) k) B
  have hj : ∀ j : Fin m, Smooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap A B (a j))) := by
    intro j
    have hmem : a j ∈ singularIdeal k A := by
      rw [← ha]
      exact Ideal.subset_span (Set.mem_range_self j)
    exact popescuPolynomialCoefficientLocalization_smooth d n a j
      (smooth_localization_of_mem_singularIdeal k A (a j) hmem)
  refine ⟨hfp, hj, ?_⟩
  intro i
  let x : B := algebraMap (MvPolynomial (Fin d) k) B (MvPolynomial.X i)
  let C := Localization.Away x
  let s : Set C := Set.range (fun j : Fin m ↦ algebraMap A C (a j))
  have hrel : x ^ n = ∑ j : Fin m,
      Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr (i, j))) * algebraMap A B (a j) := by
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self (f := popescuPolynomialRelations d n a) i))
    have hx : x = Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)) := by
      change (popescuPolynomialBaseMap (k := k) d n a) (MvPolynomial.X i) = _
      exact MvPolynomial.aeval_X _ i
    change Ideal.Quotient.mk _ (popescuPolynomialRelations d n a i) = 0 at hzero
    rw [popescuPolynomialRelations, map_sub, sub_eq_zero, map_pow, map_sum] at hzero
    rw [hx]
    simpa only [map_mul, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap] using hzero
  have hs : Ideal.span s = ⊤ := by
    have hmem : algebraMap B C (x ^ n) ∈ Ideal.span s := by
      rw [hrel, map_sum]
      apply Ideal.sum_mem
      intro j _
      rw [map_mul, ← IsScalarTower.algebraMap_apply A B C]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
    exact (Ideal.span s).eq_top_of_isUnit_mem hmem
      (by simpa only [map_pow, Nat.sub_add_cancel hn] using
        (IsLocalization.Away.algebraMap_isUnit (S := C) x).pow (n - 1 + 1))
  apply smooth_of_localization_span_universes (MvPolynomial (Fin d) k) C s hs
  rintro ⟨c, hc⟩
  obtain ⟨j, rfl⟩ := hc
  let b : B := algebraMap A B (a j)
  have : Smooth (MvPolynomial (Fin d) k) (Localization.Away b) := hj j
  let D := Localization.Away (algebraMap B (Localization.Away b) x)
  let E := Localization.Away (algebraMap B C b)
  have : Smooth (Localization.Away b) D :=
    Smooth.of_isLocalization_Away (algebraMap B (Localization.Away b) x)
  have : Smooth (MvPolynomial (Fin d) k) D :=
    Smooth.comp (MvPolynomial (Fin d) k) (Localization.Away b) D
  have : IsLocalization.Away (x * b) D := inferInstance
  have : IsLocalization.Away (x * b) E := inferInstance
  have hE : Smooth (MvPolynomial (Fin d) k) E := Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (x * b)) D E).restrictScalars
      (MvPolynomial (Fin d) k))
  change Smooth (MvPolynomial (Fin d) k)
    (Localization.Away (algebraMap B C (algebraMap A B (a j)))) at hE
  rwa [← IsScalarTower.algebraMap_apply A B C] at hE

end Algebra
