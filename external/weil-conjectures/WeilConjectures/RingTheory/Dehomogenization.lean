/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!

# Dehomogenization at a variable

Let `R[T₀, T₁, …, Tₙ] = MvPolynomial (Option n) R` carry its total-degree grading. This file
identifies the degree-zero part of the localization away from the variable `T₀ = X none`
with the polynomial ring in the remaining variables:

`MvPolynomial.dehomogenizeEquiv : Away (homogeneousSubmodule (Option n) R) (X none) ≃+*
MvPolynomial n R`.

It sends the fraction `a / T₀ ^ k`, for `a` homogeneous of degree `k`, to the dehomogenized
polynomial `a(1, T₁, …, Tₙ)`, and its inverse sends `Tᵢ` to `Tᵢ / T₀`.

Geometrically this is the standard affine chart `𝔸ⁿ ≅ D₊(T₀) ⊆ ℙⁿ`; see
`WeilConjectures.Compactification.ProjectiveSpace`.

## Main definitions

- `MvPolynomial.dehomogenize` — the ring map `R[T₀, …, Tₙ] →+* R[T₁, …, Tₙ]` given by
  `T₀ ↦ 1` and `Tᵢ ↦ Tᵢ`.
- `MvPolynomial.dehomogenizeEquiv` — the resulting isomorphism on the degree-zero part of
  the localization away from `T₀`.

-/

@[expose] public section

open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MvPolynomial

variable {n R : Type*} [CommRing R]

local notation3 "𝒜" => homogeneousSubmodule (Option n) R

lemma isHomogeneous_X_none : (X none : MvPolynomial (Option n) R) ∈ 𝒜 1 :=
  isHomogeneous_X R none

variable (n R) in
/-- Dehomogenization at the variable `T₀`: the ring map `R[T₀, T₁, …] →+* R[T₁, …]` sending
`T₀` to `1` and `Tᵢ` to `Tᵢ`. -/
noncomputable def dehomogenize : MvPolynomial (Option n) R →+* MvPolynomial n R :=
  eval₂Hom C fun i ↦ i.elim 1 X

@[simp]
lemma dehomogenize_C (r : R) : dehomogenize n R (C r) = C r := by
  simp [dehomogenize]

@[simp]
lemma dehomogenize_X_none : dehomogenize n R (X none) = 1 := by
  simp [dehomogenize]

@[simp]
lemma dehomogenize_X_some (i : n) : dehomogenize n R (X (some i)) = X i := by
  simp [dehomogenize]

variable (n R) in
/-- Homogenization at the variable `T₀`: the ring map `R[T₁, …] →+* (R[T₀, T₁, …]_{T₀})₀`
sending `Tᵢ` to `Tᵢ / T₀`. It is inverse to the map induced by `dehomogenize`, see
`MvPolynomial.dehomogenizeEquiv`. -/
noncomputable def homogenizeAway : MvPolynomial n R →+* Away 𝒜 (X none) :=
  eval₂Hom ((fromZeroRingHom 𝒜 _).comp (homogeneousSubmoduleZeroEquiv (Option n) R).toRingHom)
    fun i ↦ Away.mk 𝒜 isHomogeneous_X_none 1 (X (some i))
      (by simpa using isHomogeneous_X R (some i))

variable (n R) in
/-- The ring map `(R[T₀, T₁, …]_{T₀})₀ →+* R[T₁, …]` induced by dehomogenization. -/
noncomputable def dehomogenizeAway : Away 𝒜 (X none) →+* MvPolynomial n R :=
  (Localization.awayLift (dehomogenize n R) (X none) (by simp)).comp
    (algebraMap (Away 𝒜 (X none)) (Localization.Away (X none)))

@[simp]
lemma homogenizeAway_X (i : n) :
    homogenizeAway n R (X i) = Away.mk 𝒜 isHomogeneous_X_none 1 (X (some i))
      (by simpa using isHomogeneous_X R (some i)) := by
  simp [homogenizeAway]

@[simp]
lemma homogenizeAway_C (r : R) :
    homogenizeAway n R (C r) =
      fromZeroRingHom 𝒜 _ (homogeneousSubmoduleZeroEquiv (Option n) R r) := by
  simp [homogenizeAway]

@[simp]
lemma dehomogenizeAway_mk (k : ℕ) (a : MvPolynomial (Option n) R) (ha : a ∈ 𝒜 (k • 1)) :
    dehomogenizeAway n R (Away.mk 𝒜 isHomogeneous_X_none k a ha) = dehomogenize n R a := by
  rw [dehomogenizeAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Localization.awayLift_mk _ _ _ 1 (by simp)]
  simp

variable (n R) in
/-- The composite `R[T₀, …] →+* R[T₁, …] →+* (R[T₀, …]_{T₀})₀ →+* R[T₀, …]_{T₀}`, an
auxiliary map for `MvPolynomial.homogenizeAway_dehomogenize`. -/
private noncomputable def dehomogenizeVal :
    MvPolynomial (Option n) R →+* Localization.Away (X none : MvPolynomial (Option n) R) :=
  ((algebraMap (Away 𝒜 (X none)) (Localization.Away (X none))).comp
    (homogenizeAway n R)).comp (dehomogenize n R)

private lemma dehomogenizeVal_eq_eval₂Hom :
    dehomogenizeVal n R = eval₂Hom ((algebraMap (MvPolynomial (Option n) R)
      (Localization.Away (X none : MvPolynomial (Option n) R))).comp C)
      (fun o ↦ dehomogenizeVal n R (X o)) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun o ↦ by simp)
  simp only [dehomogenizeVal, RingHom.comp_apply, dehomogenize_C, homogenizeAway_C,
    HomogeneousLocalization.algebraMap_apply, eval₂Hom_C]
  exact Localization.mk_one_eq_algebraMap
    (M := Submonoid.powers (X none : MvPolynomial (Option n) R)) (C r)

private lemma algebraMap_eq_eval₂Hom :
    (algebraMap (MvPolynomial (Option n) R)
        (Localization.Away (X none : MvPolynomial (Option n) R)) :
      MvPolynomial (Option n) R →+* Localization.Away (X none : MvPolynomial (Option n) R)) =
      eval₂Hom ((algebraMap (MvPolynomial (Option n) R) (Localization.Away (X none))).comp C)
        (fun o ↦ algebraMap (MvPolynomial (Option n) R) (Localization.Away (X none)) (X none) *
          dehomogenizeVal n R (X o)) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun o ↦ ?_)
  rw [eval₂Hom_X']
  match o with
  | none => simp [dehomogenizeVal]
  | some i =>
    simp only [dehomogenizeVal, RingHom.comp_apply, dehomogenize_X_some, homogenizeAway_X,
      HomogeneousLocalization.algebraMap_apply, Away.val_mk, pow_one, Localization.mk_eq_mk']
    exact (IsLocalization.mk'_spec' _ _ _).symm

/-- Dehomogenizing a homogeneous polynomial of degree `k` and homogenizing back gives the
fraction `a / T₀ ^ k`. -/
lemma homogenizeAway_dehomogenize {k : ℕ} {a : MvPolynomial (Option n) R} (ha : a ∈ 𝒜 (k • 1)) :
    homogenizeAway n R (dehomogenize n R a) = Away.mk 𝒜 isHomogeneous_X_none k a ha := by
  have ha' : a.IsHomogeneous k := by simpa using ha
  have h3 : algebraMap (MvPolynomial (Option n) R) (Localization.Away (X none)) a =
      algebraMap (MvPolynomial (Option n) R) (Localization.Away (X none)) (X none) ^ k *
        dehomogenizeVal n R a := by
    conv_lhs => rw [show (algebraMap (MvPolynomial (Option n) R)
      (Localization.Away (X none : MvPolynomial (Option n) R)) a) =
      (algebraMap (MvPolynomial (Option n) R)
        (Localization.Away (X none : MvPolynomial (Option n) R)) :
        MvPolynomial (Option n) R →+* _) a from rfl, algebraMap_eq_eval₂Hom]
    rw [coe_eval₂Hom, ha'.eval₂_const_mul, ← coe_eval₂Hom, ← dehomogenizeVal_eq_eval₂Hom]
  have hu : IsUnit ((algebraMap (MvPolynomial (Option n) R)
      (Localization.Away (X none : MvPolynomial (Option n) R))) (X none) ^ k) :=
    (IsLocalization.Away.algebraMap_isUnit (X none)).pow k
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk]
  change dehomogenizeVal n R a = _
  refine hu.mul_left_cancel ?_
  rw [← h3, Localization.mk_eq_mk', ← map_pow]
  exact (IsLocalization.mk'_spec' _ _ _).symm

@[simp]
lemma dehomogenizeAway_fromZeroRingHom (x : 𝒜 0) :
    dehomogenizeAway n R (fromZeroRingHom 𝒜 (Submonoid.powers (X none)) x) =
      dehomogenize n R x := by
  have hx : (fromZeroRingHom 𝒜 (Submonoid.powers (X none)) x).val =
      algebraMap (MvPolynomial (Option n) R)
        (Localization.Away (X none : MvPolynomial (Option n) R)) (x : MvPolynomial (Option n) R) :=
    Localization.mk_one_eq_algebraMap
      (M := Submonoid.powers (X none : MvPolynomial (Option n) R)) _
  rw [dehomogenizeAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, hx]
  exact IsLocalization.lift_eq _ _

variable (n R) in
/-- **Dehomogenization at `T₀`**: the degree-zero part of the localization of
`R[T₀, T₁, …, Tₙ]` away from `T₀` is the polynomial ring `R[T₁, …, Tₙ]`, via
`a / T₀ ^ k ↦ a(1, T₁, …, Tₙ)`. Geometrically this is the standard affine chart
`𝔸ⁿ ≅ D₊(T₀) ⊆ ℙⁿ`. -/
noncomputable def dehomogenizeEquiv : Away 𝒜 (X none) ≃+* MvPolynomial n R :=
  RingEquiv.ofRingHom (dehomogenizeAway n R) (homogenizeAway n R)
    (MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun i ↦ by simp))
    (RingHom.ext fun z ↦ by
      obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 isHomogeneous_X_none z
      simp [homogenizeAway_dehomogenize ha])

@[simp]
lemma dehomogenizeEquiv_apply (z : Away 𝒜 (X none)) :
    dehomogenizeEquiv n R z = dehomogenizeAway n R z := rfl

@[simp]
lemma dehomogenizeEquiv_symm_apply (p : MvPolynomial n R) :
    (dehomogenizeEquiv n R).symm p = homogenizeAway n R p := rfl

end MvPolynomial
