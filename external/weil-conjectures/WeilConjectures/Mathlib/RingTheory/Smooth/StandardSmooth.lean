/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Polynomial algebras are standard smooth

The polynomial algebra `R[Xᵢ : i ∈ σ]` in finitely many variables is standard smooth of relative
dimension `#σ` over `R`: the presentation with the variables as generators and no relations is
submersive.

## Main statements

- `MvPolynomial.isStandardSmoothOfRelativeDimension`: `R[Xᵢ : i ∈ σ]` is standard smooth of
  relative dimension `Nat.card σ` over `R`.
-/

@[expose] public section

universe u v

namespace MvPolynomial

open Algebra

variable (R : Type u) [CommRing R] (σ : Type v) [Finite σ]

/-- The submersive presentation of `R[Xᵢ : i ∈ σ]` with the variables as generators and no
relations. -/
noncomputable def submersivePresentation :
    SubmersivePresentation R (MvPolynomial σ R) σ PEmpty.{1} where
  __ := (PreSubmersivePresentation.naive (v := (PEmpty.elim : PEmpty.{1} → MvPolynomial σ R))
    PEmpty.elim (fun a ↦ a.elim)).ofAlgEquiv
      ((Ideal.quotientEquivAlgOfEq R (by simp)).trans (AlgEquiv.quotientBot R _))
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [Matrix.det_isEmpty]

/-- The polynomial algebra `R[Xᵢ : i ∈ σ]` in finitely many variables is standard smooth of
relative dimension `#σ` over `R`. -/
instance isStandardSmoothOfRelativeDimension :
    IsStandardSmoothOfRelativeDimension (Nat.card σ) R (MvPolynomial σ R) :=
  (submersivePresentation R σ).isStandardSmoothOfRelativeDimension (by
    simp [Presentation.dimension])

end MvPolynomial
