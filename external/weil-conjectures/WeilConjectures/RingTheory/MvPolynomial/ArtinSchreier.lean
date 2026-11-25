/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# The Artin–Schreier map of a polynomial ring

The ring map `A[n] → A[n]`, `Xᵢ ↦ Xᵢ ^ q - Xᵢ`, inducing the Artin–Schreier map
`x ↦ x ^ q - x` of affine space. It is finite for `q ≠ 1`, and étale when `q = 0` in `A`: as an
`A[n]`-algebra (via the map) the target is `A[n][Yᵢ] ⧸ (Yᵢ ^ q - Yᵢ - Xᵢ)`, whose naive
presentation has Jacobian matrix `q Yᵢ ^ (q - 1) - 1 = -1`.

## Main definitions

- `MvPolynomial.artinSchreierRingHom`: the ring map `Xᵢ ↦ Xᵢ ^ q - Xᵢ`.

## Main statements

- `MvPolynomial.finite_artinSchreierRingHom`: it is finite for `q ≠ 1`.
- `MvPolynomial.etale_artinSchreierRingHom`: it is étale if `q = 0` in `A`.
-/

@[expose] public section

universe u

noncomputable section

namespace MvPolynomial


variable {A : Type u} [CommRing A] (n : Type u) (q : ℕ)

/-- The Artin–Schreier relations `Yᵢ ^ q - Yᵢ - Xᵢ` in `A[n][Y]`. -/
abbrev artinSchreierRel (i : n) : MvPolynomial n (MvPolynomial n A) :=
  X i ^ q - X i - C (X i)

variable (A) in
/-- The ideal `(Yᵢ ^ q - Yᵢ - Xᵢ)` of `A[n][Y]`. -/
abbrev artinSchreierIdeal : Ideal (MvPolynomial n (MvPolynomial n A)) :=
  Ideal.span (Set.range (artinSchreierRel (A := A) n q))

/-- The quotient `A[n][Yᵢ] ⧸ (Yᵢ ^ q - Yᵢ - Xᵢ)`. -/
abbrev ArtinSchreierQuot (A : Type u) [CommRing A] : Type u :=
  MvPolynomial n (MvPolynomial n A) ⧸ artinSchreierIdeal A n q

/-- If `q = 0` in `A`, the naive presentation of `A[n][Yᵢ] ⧸ (Yᵢ ^ q - Yᵢ - Xᵢ)` over `A[n]`
is submersive, with Jacobian matrix `-1`. -/
def artinSchreierSubmersivePresentation [Finite n] (hq : (q : A) = 0) :
    Algebra.SubmersivePresentation (MvPolynomial n A) (ArtinSchreierQuot n q A) n n where
  __ := Algebra.PreSubmersivePresentation.naive (v := artinSchreierRel (A := A) n q) id
    Function.injective_id
  jacobian_isUnit := by
    classical
    cases nonempty_fintype n
    have hq' : (q : MvPolynomial n (MvPolynomial n A)) = 0 := by
      rw [← map_natCast (algebraMap A _), hq, map_zero]
    have hJ : (Algebra.PreSubmersivePresentation.naive (v := artinSchreierRel (A := A) n q) id
        Function.injective_id).jacobiMatrix = -1 := by
      ext i j
      rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
      simp [hq', Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hJ, Matrix.det_neg,
      Matrix.det_one, mul_one]
    exact (isUnit_neg_one.pow _).map _

variable (A) in
/-- The Artin–Schreier ring map `A[n] → A[n]`, `Xᵢ ↦ Xᵢ ^ q - Xᵢ`. -/
def artinSchreierRingHom : MvPolynomial n A →+* MvPolynomial n A :=
  (aeval fun i ↦ X i ^ q - X i : MvPolynomial n A →ₐ[A] MvPolynomial n A).toRingHom

@[simp]
lemma artinSchreierRingHom_X (i : n) : artinSchreierRingHom A n q (X i) = X i ^ q - X i := by
  simp [artinSchreierRingHom]

variable (A) in
/-- The map `A[n][Yᵢ] ⧸ (Yᵢ ^ q - Yᵢ - Xᵢ) → A[n]`, `Yᵢ ↦ Xᵢ`, restricting to the
Artin–Schreier map on `A[n]`. -/
def artinSchreierQuotToPoly : ArtinSchreierQuot n q A →+* MvPolynomial n A :=
  Ideal.Quotient.lift (artinSchreierIdeal A n q)
    (eval₂Hom (artinSchreierRingHom A n q) (X : n → MvPolynomial n A)) fun a ha ↦ by
    refine (Ideal.span_le (I := RingHom.ker
      (eval₂Hom (artinSchreierRingHom A n q) (X : n → MvPolynomial n A)))).mpr ?_ ha
    rintro - ⟨i, rfl⟩
    simp [artinSchreierRingHom]

variable (A) in
/-- The map `A[n] → A[n][Yᵢ] ⧸ (Yᵢ ^ q - Yᵢ - Xᵢ)`, `Xᵢ ↦ Yᵢ`. -/
def artinSchreierPolyToQuot : MvPolynomial n A →+* ArtinSchreierQuot n q A :=
  eval₂Hom (algebraMap A _) fun i ↦ Ideal.Quotient.mk (artinSchreierIdeal A n q) (X i)

/-- `artinSchreierQuotToPoly` on representatives. -/
@[simp]
lemma artinSchreierQuotToPoly_mk (a : MvPolynomial n (MvPolynomial n A)) :
    artinSchreierQuotToPoly A n q (Ideal.Quotient.mk _ a) =
      eval₂Hom (artinSchreierRingHom A n q) (X : n → MvPolynomial n A) a :=
  rfl

/-- The map `artinSchreierPolyToQuot` sends `Xᵢ ^ q - Xᵢ` to `Xᵢ`. -/
lemma artinSchreierPolyToQuot_comp_artinSchreierRingHom :
    (artinSchreierPolyToQuot A n q).comp (artinSchreierRingHom A n q) =
      (Ideal.Quotient.mk (artinSchreierIdeal A n q)).comp C := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) fun i ↦ ?_
  · simp [artinSchreierRingHom, artinSchreierPolyToQuot]
    rfl
  · have h : Ideal.Quotient.mk (artinSchreierIdeal A n q) (artinSchreierRel n q i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [map_sub, map_sub, map_pow] at h
    rw [RingHom.comp_apply, RingHom.comp_apply, artinSchreierRingHom_X, map_sub, map_pow,
      artinSchreierPolyToQuot, eval₂Hom_X']
    linear_combination h

variable (A) in
/-- The quotient `A[n][Yᵢ] ⧸ (Yᵢ ^ q - Yᵢ - Xᵢ)` is isomorphic to `A[n]`, via `Yᵢ ↦ Xᵢ`;
under this isomorphism the structure map becomes the Artin–Schreier map. -/
def artinSchreierQuotEquiv : ArtinSchreierQuot n q A ≃+* MvPolynomial n A :=
  RingEquiv.ofRingHom (artinSchreierQuotToPoly A n q) (artinSchreierPolyToQuot A n q)
    (MvPolynomial.ringHom_ext (fun r ↦ by
      rw [RingHom.comp_apply, artinSchreierPolyToQuot, eval₂Hom_C,
        IsScalarTower.algebraMap_apply A (MvPolynomial n (MvPolynomial n A)),
        Ideal.Quotient.algebraMap_eq,
        MvPolynomial.algebraMap_apply, artinSchreierQuotToPoly_mk, eval₂Hom_C]
      simp [artinSchreierRingHom]) fun i ↦ by
      simp [artinSchreierPolyToQuot])
    (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a ↦ by
      simpa using RingHom.congr_fun (artinSchreierPolyToQuot_comp_artinSchreierRingHom n q) a)
      fun i ↦ by
      simp [artinSchreierPolyToQuot]))

lemma artinSchreierQuotEquiv_comp_algebraMap :
    (artinSchreierQuotEquiv A n q : ArtinSchreierQuot n q A →+* MvPolynomial n A).comp
      (algebraMap (MvPolynomial n A) (ArtinSchreierQuot n q A)) =
      artinSchreierRingHom A n q := by
  refine RingHom.ext fun a ↦ ?_
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (MvPolynomial n A)
    (MvPolynomial n (MvPolynomial n A)) (ArtinSchreierQuot n q A), Ideal.Quotient.algebraMap_eq,
    MvPolynomial.algebraMap_eq, RingHom.coe_coe]
  simp [artinSchreierQuotEquiv]

/-- If `q = 0` in `A`, the algebra `A[n][Yᵢ] ⧸ (Yᵢ ^ q - Yᵢ - Xᵢ)` is standard smooth of
relative dimension `0` over `A[n]`. -/
lemma isStandardSmoothOfRelativeDimension_artinSchreierQuot [Finite n] (hq : (q : A) = 0) :
    Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial n A) (ArtinSchreierQuot n q A) :=
  (artinSchreierSubmersivePresentation n q hq).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

/-- If `q = 0` in `A`, the Artin–Schreier ring map `A[n] → A[n]`, `Xᵢ ↦ Xᵢ ^ q - Xᵢ`, is
étale. -/
lemma etale_artinSchreierRingHom [Finite n] (hq : (q : A) = 0) :
    (artinSchreierRingHom A n q).Etale := by
  have := isStandardSmoothOfRelativeDimension_artinSchreierQuot n q hq
  rw [← artinSchreierQuotEquiv_comp_algebraMap]
  exact RingHom.Etale.stableUnderComposition (R := MvPolynomial n A)
    (S := ArtinSchreierQuot n q A) (T := MvPolynomial n A) _ _
    (RingHom.etale_algebraMap.mpr inferInstance)
    (RingHom.Etale.of_bijective (artinSchreierQuotEquiv A n q).bijective)

/-- The Artin–Schreier ring map is a map of `A`-algebras. -/
@[simp]
lemma artinSchreierRingHom_comp_C : (artinSchreierRingHom A n q).comp C = C := by
  ext
  simp [artinSchreierRingHom]

/-- For `q ≠ 1`, the Artin–Schreier ring map `A[n] → A[n]`, `Xᵢ ↦ Xᵢ ^ q - Xᵢ`, is integral:
each `Xᵢ` is a root of the monic `T ^ q - T - (Xᵢ ^ q - Xᵢ)` (of `T - (1 - Xᵢ)` if `q = 0`). -/
lemma isIntegral_artinSchreierRingHom {q : ℕ} (hq : q ≠ 1) :
    (artinSchreierRingHom A n q).IsIntegral := by
  intro x
  induction x using MvPolynomial.induction_on with
  | C a =>
    have : artinSchreierRingHom A n q (C a) = C a := by simp [artinSchreierRingHom]
    rw [← this]
    exact RingHom.isIntegralElem_map _
  | add x y hx hy => exact hx.add _ hy
  | mul_X x i hx =>
    refine hx.mul _ ?_
    obtain rfl | hq2 := Nat.eq_zero_or_pos q
    · refine ⟨Polynomial.X - Polynomial.C (1 - X i), Polynomial.monic_X_sub_C _, ?_⟩
      simp [artinSchreierRingHom]
    · refine ⟨Polynomial.X ^ q - (Polynomial.X + Polynomial.C (X i)),
        Polynomial.monic_X_pow_sub (lt_of_le_of_lt (b := 1) ?_ ?_), ?_⟩
      · compute_degree
      · exact_mod_cast (by omega : 1 < q)
      · simp [artinSchreierRingHom]

/-- For `q ≠ 1` and finitely many variables, the Artin–Schreier ring map `A[n] → A[n]`,
`Xᵢ ↦ Xᵢ ^ q - Xᵢ`, is finite. -/
lemma finite_artinSchreierRingHom [Finite n] {q : ℕ} (hq : q ≠ 1) :
    (artinSchreierRingHom A n q).Finite := by
  refine (isIntegral_artinSchreierRingHom n hq).to_finite
    (RingHom.FiniteType.of_comp_finiteType (f := C) ?_)
  rw [artinSchreierRingHom_comp_C]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end MvPolynomial
