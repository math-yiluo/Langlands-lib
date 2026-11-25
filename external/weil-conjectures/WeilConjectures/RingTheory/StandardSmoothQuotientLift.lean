/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Lifting a standard smooth algebra across a quotient of its base

Source: Stacks Project, Tag 07CK, the Jacobian presentation construction of `B`.
-/

@[expose] public section

universe u v

namespace Algebra

-- Compose with the inverse-Jacobian presentation; the new Jacobian is the old one squared.
private theorem isStandardSmooth_jacobianLocalization
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    {ι σ : Type*} [Finite ι] [Finite σ] (P : PreSubmersivePresentation R A ι σ) :
    IsStandardSmooth R (Localization.Away P.jacobian) := by
  let Q := PreSubmersivePresentation.localizationAway
    (Localization.Away P.jacobian) P.jacobian
  have hd : IsUnit (algebraMap A (Localization.Away P.jacobian) P.jacobian) :=
    IsLocalization.map_units _ (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
  let T : SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ ι) (Unit ⊕ σ) :=
    { Q.comp P with
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        exact hd.mul (by simpa [Q] using hd) }
  exact T.isStandardSmooth

/-- A standard smooth algebra over `R/I` is the reduction of a standard smooth
algebra over `R`. This only lifts the presentation, not a map into another algebra.

Source: Stacks Project, Smoothing Ring Maps, Tag 07CK (lemma-lift-once), the construction
of `B` (blueprint: lem-weil-pbc-standard-smooth-quotient-lift).

Proof: Choose a finite submersive presentation of `C` over `R/I`, with equations
`fbar` and an invertible Jacobian minor `Dbar`. Lift the coefficients of its finitely
many equations to `R`, giving equations `f`, and let `D` be the corresponding Jacobian
minor. Form the finite polynomial quotient `B = R[x,z]/(f,z*D-1)`. Choose the old
minor variables together with `z`. Since the equations `f` do not involve `z`, this
Jacobian matrix is block triangular, with the old matrix and `D` on its diagonal.
Its determinant is `D^2`, a unit in `B` since `z*D=1`. Thus this quotient has a
submersive presentation and is standard smooth. Reduction of polynomial coefficients
commutes with partial derivatives and determinants. Reducing `B` modulo `I` gives
`(R/I)[x,z]/(fbar,z*Dbar-1)`. Map it to `C` by the presentation generators and send
`z` to the inverse of `Dbar`. The inverse sends the presentation generators of `C`
to the classes of `x`. The composites fix these generators and also `z`, since
inverses are unique. Both maps commute with the `R/I`-algebra structure. The quotient
has universe at most `u`; lift its carrier to `max u v` and transport the structures
and equivalence. Empty equation lists use determinant `1` and eliminate `z`; the
zero algebra is covered by the same presentation argument. No property of `I` other
than being an ideal is used. -/
theorem exists_standardSmooth_quotient_lift
    (R : Type u) [CommRing R] (I : Ideal R)
    (C : Type v) [CommRing C] [Algebra (R ⧸ I) C] [IsStandardSmooth (R ⧸ I) C] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      IsStandardSmooth R B ∧
        Nonempty ((B ⧸ I.map (algebraMap R B)) ≃ₐ[R ⧸ I] C) := by
  classical
  obtain ⟨ι, σ, hσ, hι, ⟨P₀⟩⟩ := (inferInstance : IsStandardSmooth (R ⧸ I) C).out
  let := hσ
  let := hι
  -- Raising the generator universe makes the explicit model inhabit `Type (max u v)`.
  let P := P₀.reindex (Equiv.ulift : ULift.{max u v} ι ≃ ι) (Equiv.refl σ)
  let : Algebra R C := Algebra.compHom C (Ideal.Quotient.mk I)
  let : IsScalarTower R (R ⧸ I) C := IsScalarTower.of_algebraMap_eq' rfl
  let : P.HasCoeffs R := ⟨by
    intro x _
    exact Ideal.Quotient.mk_surjective x⟩
  let Q := P.toPreSubmersivePresentation.ofHasCoeffs R
  let B := Localization.Away Q.jacobian
  let e := P.tensorModelOfHasCoeffsEquiv R
  have hd : e ((1 : R ⧸ I) ⊗ₜ[R] Q.jacobian) = P.jacobian := by
    let : Fintype σ := Fintype.ofFinite σ
    rw [Q.jacobian_eq_jacobiMatrix_det]
    change e ((1 : R ⧸ I) ⊗ₜ[R]
      Ideal.Quotient.mk _ (P.jacobianOfHasCoeffs R)) = P.jacobian
    dsimp only [e]
    rw [Presentation.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul]
    exact P.aeval_jacobianOfHasCoeffs R
  -- Reduction is base change, which commutes with localization at the Jacobian.
  let e₁ := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  let e₂ := IsLocalization.Away.tensorProductEquivTMulRight R (R ⧸ I) Q.jacobian B
  let e₃ := IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers ((1 : R ⧸ I) ⊗ₜ[R] Q.jacobian))
    (T := Submonoid.powers P.jacobian)
    (Localization.Away ((1 : R ⧸ I) ⊗ₜ[R] Q.jacobian))
    (Localization.Away P.jacobian) e (by simp [Submonoid.map_powers, hd])
  let e₄ := (IsLocalization.atUnit C (Localization.Away P.jacobian)
    P.jacobian P.jacobian_isUnit).symm.restrictScalars (R ⧸ I)
  exact ⟨B, inferInstance, inferInstance, isStandardSmooth_jacobianLocalization Q,
    ⟨e₁.trans (e₂.trans (e₃.trans e₄))⟩⟩

end Algebra
