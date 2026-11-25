/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth

import WeilConjectures.RingTheory.PopescuReductionPresentation
import WeilConjectures.RingTheory.PopescuCorrectionReduction
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Ideal.Operations

/-! # A factor algebra with standard smooth reduction

Source: Stacks Project, Tag 07CK, the construction of `A'` before lifting the equations.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

private theorem exists_sum_of_mem_map
    {R : Type u} [CommRing R] {Λ : Type v} [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (x : Λ) (hx : x ∈ I.map (algebraMap R Λ)) :
    ∃ (k : ℕ) (ε : Fin k → I) (μ : Fin k → Λ),
      x = ∑ j, algebraMap R Λ (ε j) * μ j := by
  classical
  have hrange : (algebraMap R Λ) '' (I : Set R) =
      Set.range (fun a : I ↦ algebraMap R Λ a) := by
    ext y
    simp
  rw [Ideal.map, hrange, Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, hc⟩ := hx
  let e := (Fintype.equivFin c.support).symm
  refine ⟨Fintype.card c.support, (fun j ↦ (e j).val), (fun j ↦ c (e j).val), ?_⟩
  rw [← hc]
  change (∑ a ∈ c.support, c a * algebraMap R Λ a) = _
  rw [← Finset.sum_attach]
  simpa only [mul_comm, Finset.attach_eq_univ] using
    (e.sum_comp (fun a : c.support ↦ c a.val * algebraMap R Λ a.val)).symm

/-- A map into an algebra with ind standard smooth reduction factors through a finitely
presented algebra whose reduction is itself standard smooth.

Source: Stacks Project, Smoothing Ring Maps, Tag 07CK (lemma-lift-once), construction
of `A'` (blueprint: lem-weil-pbc-popescu-standard-reduction-factor).

Proof: Reducing a finite presentation of `A` shows that `A/IA` is finitely presented
over `R/I`. The map induced by `φ` therefore factors through a standard smooth stage
`C` of the given filtered colimit (Tag 00QO). Since `C` is finitely presented over
`R/I` and `A/IA` is finite type over it, `C` is finitely presented over `A/IA`
(Tag 00F4). Write `C = (A/IA)[t]/(gbar)` with finite lists of variables and relations.
Lift the images of the variables to elements `λ` of `Λ`, and lift the coefficients of
`gbar` to polynomials `g` over `A`. Each evaluation `φ(g)(λ)` lies in `IΛ`, because
its image in the quotient is zero by the factorization through `C`. Write it as a
finite sum of products `ε * μ`, with `ε` in `I`. Adjoin one variable `δ` for each
such product and impose the relations `g - sum ε * δ`. Evaluation at `λ` and `μ`
defines the map to `Λ`; its restriction to `A` is `φ`. This quotient is finitely
presented over `A` and therefore over `R`. Modulo `I` the correction terms vanish,
so the reduction is `C[δ]`. Adjoining finitely many variables preserves a standard
smooth presentation: retain the original equations and original invertible Jacobian
minor, with the new variables outside that minor. The finite polynomial quotient
has carrier universe at most `max u v w`; use `ULift` to reach that universe exactly.
This argument also covers empty lists, the zero ring, and `I = top`; it uses no
nilpotence hypothesis. -/
theorem exists_standardSmooth_reduction_factorization
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ IsStandardSmooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (A' : Type (max u v w)) (_ : CommRing A') (_ : Algebra R A'),
      FinitePresentation R A' ∧
      ∃ (ι : A →ₐ[R] A') (φ' : A' →ₐ[R] Λ), φ'.comp ι = φ ∧
        IsStandardSmooth (R ⧸ I) (A' ⧸ I.map (algebraMap R A')) := by
  classical
  obtain ⟨n, m, g, lifts, hg, hstd⟩ :=
    exists_popescu_reduction_presentation R Λ I hΛ A φ
  choose N ε μ hsum using (fun i ↦ exists_sum_of_mem_map I _ (hg i))
  let V := PopescuCorrectionVariables.{max u v w} n m N
  let P := MvPolynomial V A
  let J : Ideal P := popescuCorrectionIdeal.{u, w, max u v w} R A I n m N g ε
  let A' := P ⧸ J
  let values : V → Λ := Sum.elim lifts (fun j ↦ μ j.down.1 j.down.2)
  let ev : P →ₐ[R] Λ :=
    { toRingHom := MvPolynomial.eval₂Hom φ.toRingHom values
      commutes' := fun r ↦ by
        exact (MvPolynomial.eval₂Hom_C φ.toRingHom values (algebraMap R A r)).trans
          (φ.commutes r) }
  have hrel (i : Fin m) :
      ev (popescuCorrectionRelation.{u, w, max u v w} R A I n m N g ε i) = 0 := by
    change MvPolynomial.eval₂Hom φ.toRingHom values
      (popescuCorrectionRelation.{u, w, max u v w} R A I n m N g ε i) = 0
    dsimp only [popescuCorrectionRelation, V, PopescuCorrectionVariables] at values ⊢
    rw [map_sub, map_sum]
    simp only [MvPolynomial.eval₂Hom_rename, map_mul, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X']
    apply sub_eq_zero.mpr
    calc
      _ = MvPolynomial.eval₂ φ.toRingHom lifts (g i) := rfl
      _ = ∑ j, algebraMap R Λ (ε i j) * μ i j := hsum i
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        exact (φ.commutes (ε i j)).symm
  have hJ : J ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hrel i
  let φ' : A' →ₐ[R] Λ := Ideal.Quotient.liftₐ J ev (fun p hp ↦ hJ hp)
  let ι : A →ₐ[R] A' := (Ideal.Quotient.mkₐ R J).comp (IsScalarTower.toAlgHom R A P)
  have hcomp : φ'.comp ι = φ := by
    ext a
    change ev (algebraMap A P a) = φ a
    exact MvPolynomial.eval₂_C _ _ _
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have : FinitePresentation R A' := FinitePresentation.quotient hfg
  refine ⟨A', inferInstance, inferInstance, inferInstance, ι, φ', hcomp, ?_⟩
  obtain ⟨e⟩ := nonempty_popescuCorrectionQuotient_reduction_equiv.{u, w, max u v w}
    R A I n m N g ε
  let B := MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
    Ideal.span (Set.range fun i ↦
      MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i))
  let D := ULift.{max u v w} (Σ i : Fin m, Fin (N i))
  have : IsStandardSmooth (R ⧸ I) B := hstd
  have : IsStandardSmooth B (MvPolynomial D B) :=
    IsStandardSmoothOfRelativeDimension.isStandardSmooth (Nat.card D)
  have : IsStandardSmooth (R ⧸ I) (MvPolynomial D B) :=
    IsStandardSmooth.trans (R ⧸ I) B (MvPolynomial D B)
  exact IsStandardSmooth.of_algEquiv e.symm

end Algebra
