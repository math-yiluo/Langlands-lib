/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.Basic

/-!
# The étale Tate sheaves as tensor powers

Let `Λ` be a commutative ring of positive characteristic `n`, and `X` a scheme on which `n` is
invertible. This file identifies the sheaf `(μₙ ⊗ Λ)^{⊗ d}` underlying the Tate twist `Λ_X(d)`,
`d ∈ ℕ` (`AlgebraicGeometry.Etale.tateTwistSheaf`), defined as a pullback from the universal base
`Spec ℤ[1/n]`, with the iterated tensor power `tateSheafPow Λ X d` of the Tate sheaf
`Λ_X(1) = μₙ ⊗ Λ` of `X` itself.

## Main definitions

- `AlgebraicGeometry.Etale.tateSheafPow`: the tensor powers `(⋯(𝟙 ⊗ Λ_X(1)) ⊗ ⋯) ⊗ Λ_X(1)`.
- `AlgebraicGeometry.Etale.tateTwistSheafNatIso`: `tateTwistSheaf Λ X d ≅ tateSheafPow Λ X d`.
- `AlgebraicGeometry.Etale.tateObjectNatIsoSingleFunctor`: the Tate twist `Λ_X(d)` is
  `tateSheafPow Λ X d` placed in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- For `g : X ⟶ Y` with the characteristic of `Λ` invertible on `Y`, the comparison
`g^* Λ_Y(1) ⟶ Λ_X(1)` of the Tate sheaves is an isomorphism. -/
theorem isIso_upperStarTateSheafToTateSheaf_of_isUnit [NeZero (ringChar Λ)] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (hn : IsUnit ((ringChar Λ : ℕ) : Γ(Y, ⊤))) :
    IsIso (upperStarTateSheafToTateSheaf Λ g) := by
  have := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit (ringChar Λ) g hn
  dsimp only [upperStarTateSheafToTateSheaf]
  infer_instance

/-- The tensor powers `Λ_X(1)^{⊗ d} = (⋯(𝟙 ⊗ Λ_X(1)) ⊗ ⋯) ⊗ Λ_X(1)` of the Tate sheaf. -/
noncomputable def tateSheafPow (X : Scheme.{u}) :
    ℕ → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  | 0 => 𝟙_ _
  | d + 1 => tateSheafPow X d ⊗ tateSheaf Λ X

variable [NeZero (ringChar Λ)] (X : Scheme.{u}) [HasInvertibleExponent Λ X]

/-- The pullback of the Tate sheaf of `Spec ℤ[1/n]` is the Tate sheaf of `X`. -/
noncomputable def upperStarTateSheafIso :
    (toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ].obj
        (tateSheaf Λ (invertibleExponentBase.{u} Λ)) ≅ tateSheaf Λ X :=
  haveI := isIso_upperStarTateSheafToTateSheaf_of_isUnit Λ (toInvertibleExponentBase (Λ := Λ) X)
    (isUnit_ringChar_invertibleExponentBase Λ)
  asIso (upperStarTateSheafToTateSheaf Λ _)

/-- The sheaf `(μₙ ⊗ Λ)^{⊗ d}` underlying the Tate twist `Λ_X(d)`, `d ∈ ℕ`, is the `d`-th
tensor power of the Tate sheaf of `X`. -/
noncomputable def tateTwistSheafNatIso : (d : ℕ) → tateTwistSheaf Λ X d ≅ tateSheafPow Λ X d
  | 0 => (Functor.Monoidal.εIso _).symm
  | d + 1 => (Functor.Monoidal.μIso _ _ _).symm ≪≫
      tensorIso (upperStarTateSheafIso Λ X) (tateTwistSheafNatIso d) ≪≫ β_ _ _

/-- The Tate twist `Λ_X(d)`, `d ∈ ℕ`, of the Tate twist datum `hasTateTwist` is the `d`-th tensor
power of the Tate sheaf of `X` placed in degree zero. -/
noncomputable def tateObjectNatIsoSingleFunctor (d : ℕ) :
    tateObject Λ X d ≅
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
        (tateSheafPow Λ X d) :=
  tateTwistObjectIsoSingleFunctor Λ X d ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (tateTwistSheafNatIso Λ X d)

end Etale

end AlgebraicGeometry
