/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.DiagonalOrientationQbar
public import WeilConjectures.SmoothPurity.UpperShriekUnitDualizable

/-!
# The orientation from the fundamental class of the diagonal

Let `f : X ⟶ Y` be smooth of pure relative dimension `d`, with projections `p₁, p₂` and diagonal
`Δ` of `X ×_Y X`. Given the fundamental class `RΔ^!(ℚ̄_ℓ(d)[2d]) ≅ ℚ̄_ℓ,X` of the diagonal and the
invertibility of the base change map `Lp₂^* ω_f ⟶ ω_{p₁}`, the diagonal construction
(`ProEtale.CondensedRing.dualizingComplexTateTwistIsoOfDiagonal`) gives `ω_f ≅ ℚ̄_ℓ,X(d)[2d]`: its
remaining input, the invertibility of the purity map of `Δ` at `ω_{p₁}`, holds because `ω_{p₁}`
is dualizable (`ProEtale.CondensedRing.isDualizable_upperShriek_unit_of_smoothOfRelativeDimension`,
`p₁` being smooth of relative dimension `d` as a base change of `f`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

/-- The first projection of `X ×_Y X` is smooth of relative dimension `d`, as a base change of
`f`. -/
instance smoothOfRelativeDimension_pullback_fst_left :
    SmoothOfRelativeDimension d (pullback.fst f f).left :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  MorphismProperty.of_isPullback (isPullback_pullback_left f f).flip ‹_›

omit [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] in
include d in
/-- The purity map of the diagonal at `ω_{p₁}` is invertible, `ω_{p₁}` being dualizable. -/
lemma isIso_upperShriekUnitTensorMap_diagonal_upperShriek_unit :
    IsIso (upperShriekUnitTensorMap ℓ (pullback.diagonal f)
      ((boundedConstructibleUpperShriek ℓ (pullback.fst f f)).obj (𝟙_ _))) :=
  isIso_upperShriekUnitTensorMap_of_isDualizable ℓ _
    (isDualizable_upperShriek_unit_of_smoothOfRelativeDimension ℓ (pullback.fst f f) d)

/-- Blueprint `proposition-relative-dualizing-complex--1` (`ℚ̄_ℓ`-coefficients): **the orientation
`ℚ̄_ℓ,X(d)[2d] ≅ ω_f` from the fundamental class of the diagonal**, given the invertibility of the
base change map `Lp₂^* ω_f ⟶ ω_{p₁}`. -/
noncomputable def tateTwistIsoUpperShriekUnitOfDiagonal
    (cl : (boundedConstructibleUpperShriek ℓ (pullback.diagonal f)).obj
      (boundedConstructibleTateTwist ℓ (pullback f f) d (2 * d)) ≅ 𝟙_ _)
    (hbc : IsIso (diagonalBaseChangeMap ℓ f)) :
    boundedConstructibleTateTwist ℓ X d (2 * d) ≅
      (boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _) :=
  (dualizingComplexTateTwistIsoOfDiagonal ℓ f d cl hbc
    (isIso_upperShriekUnitTensorMap_diagonal_upperShriek_unit ℓ f d)).symm

end AlgebraicGeometry.ProEtale.CondensedRing
