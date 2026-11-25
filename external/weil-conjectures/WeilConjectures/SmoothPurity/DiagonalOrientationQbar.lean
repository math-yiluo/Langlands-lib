/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverPullbackFiniteType
public import WeilConjectures.AlgebraicGeometry.OverProper
public import WeilConjectures.SmoothPurity.TateTwistDualizable
public import WeilConjectures.TraceFormula.Dualizing
public import WeilConjectures.TraceFormula.ExceptionalKunnethFunctoriality
public import WeilConjectures.TraceFormula.PurityTensorMapDualizable

/-!

# The diagonal construction of the orientation with `ℚ̄_ℓ`-coefficients

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type, with projections
`p₁, p₂ : X ×_Y X ⟶ X` and diagonal `Δ : X ⟶ X ×_Y X`. This file carries out, on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`, the formal part of the diagonal construction of
the identification `ω_f = Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ,X(d)[2d]`
(blueprint `proposition-relative-dualizing-complex--1`):

1. `Lp₂^* ω_f ⟶ ω_{p₁}` is the exceptional base change map at the unit
   (`ProEtale.CondensedRing.diagonalBaseChangeMap`, blueprint
   `proposition-exceptional-inverse-image-smooth-morphism--7`);
2. `RΔ^! ω_{p₁} ≅ R(𝟙 X)^! ℚ̄_ℓ ≅ ℚ̄_ℓ,X` is the composition isomorphism
   (`ProEtale.CondensedRing.upperShriekDiagonalDualizingIso`);
3. for a dualizable `T` and a `K` with invertible purity map `LΔ^* K ⊗ RΔ^! ℚ̄_ℓ ⟶ RΔ^! K`
   (`ProEtale.CondensedRing.upperShriekUnitTensorMap`), identifications `RΔ^! K ≅ ℚ̄_ℓ ≅ RΔ^! T`
   exhibit `LΔ^* K` and `LΔ^* T` as inverses of the same object `RΔ^! ℚ̄_ℓ`, hence
   `LΔ^* K ≅ LΔ^* T` (`ProEtale.CondensedRing.upperStarIsoOfUpperShriekIsoUnit`).

Applied to `K = ω_{p₁}` and the Tate twist `T = ℚ̄_ℓ(d)[2d]` of `X ×_Y X`, with the fundamental
class `RΔ^! T ≅ ℚ̄_ℓ,X` of the diagonal as input, this gives
`ω_f ≅ LΔ^* Lp₂^* ω_f ≅ LΔ^* ω_{p₁} ≅ LΔ^* T ≅ ℚ̄_ℓ,X(d)[2d]`
(`ProEtale.CondensedRing.dualizingComplexTateTwistIsoOfDiagonal`). Every step is a canonical
isomorphism; the inputs are the fundamental class of the diagonal and the invertibility of the
base change map and of the purity map of `Δ` at `ω_{p₁}`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

/-- Two objects `A`, `B` which are both inverse to the same object `D`, `A ⊗ D ≅ 𝟙` and
`B ⊗ D ≅ 𝟙`, are isomorphic: `A ≅ A ⊗ (D ⊗ B) ≅ (A ⊗ D) ⊗ B ≅ B`. -/
def isoOfTensorIsoUnit {A B D : C} (eA : A ⊗ D ≅ 𝟙_ C) (eB : B ⊗ D ≅ 𝟙_ C) : A ≅ B :=
  (ρ_ A).symm ≪≫ whiskerLeftIso A ((β_ D B) ≪≫ eB).symm ≪≫ (α_ A D B).symm ≪≫
    whiskerRightIso eA B ≪≫ λ_ B

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Inverse

variable {B V : Over (Spec (.of k))}
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

/-- Let `s : B ⟶ V`, `T` dualizable on `V` and `K` on `V` with invertible purity map
`Ls^* K ⊗ Rs^! ℚ̄_ℓ ⟶ Rs^! K`. Identifications `Rs^! K ≅ ℚ̄_ℓ` and `Rs^! T ≅ ℚ̄_ℓ` exhibit
`Ls^* K` and `Ls^* T` as inverses of `Rs^! ℚ̄_ℓ`, hence identify them. -/
noncomputable def upperStarIsoOfUpperShriekIsoUnit (s : B ⟶ V)
    {K T : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (hT : IsDualizable T)
    (hK : IsIso (upperShriekUnitTensorMap ℓ s K))
    (eK : (boundedConstructibleUpperShriek ℓ s).obj K ≅ 𝟙_ _)
    (eT : (boundedConstructibleUpperShriek ℓ s).obj T ≅ 𝟙_ _) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s).obj K ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s).obj T :=
  haveI := isIso_upperShriekUnitTensorMap_of_isDualizable ℓ s hT
  isoOfTensorIsoUnit (asIso (upperShriekUnitTensorMap ℓ s K) ≪≫ eK)
    (asIso (upperShriekUnitTensorMap ℓ s T) ≪≫ eT)

end Inverse

section Diagonal

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

/-- The base change map `Lp₂^* ω_f ⟶ ω_{p₁}` of the relative dualizing complexes for the
cartesian square of the projections of `X ×_Y X`: the exceptional base change map at the unit
followed by `Rp₁^!` of `Lf^* ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,X` (blueprint
`proposition-exceptional-inverse-image-smooth-morphism--7`). -/
noncomputable def diagonalBaseChangeMap :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (pullback.snd f f)).obj
        ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _)) ⟶
      (boundedConstructibleUpperShriek ℓ (pullback.fst f f)).obj (𝟙_ _) :=
  upperShriekBaseChange ℓ (IsPullback.of_hasPullback f f).flip (𝟙_ _) ≫
    (boundedConstructibleUpperShriek ℓ (pullback.fst f f)).map
      (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f))

/-- `RΔ^! ω_{p₁} ≅ ℚ̄_ℓ,X`: the composition isomorphism `RΔ^! Rp₁^! ≅ R(Δ ≫ p₁)^! = R(𝟙 X)^!`
followed by `R(𝟙 X)^! ≅ 𝟭`. -/
noncomputable def upperShriekDiagonalDualizingIso :
    (boundedConstructibleUpperShriek ℓ (pullback.diagonal f)).obj
        ((boundedConstructibleUpperShriek ℓ (pullback.fst f f)).obj (𝟙_ _)) ≅ 𝟙_ _ :=
  ((boundedConstructibleUpperShriekCompOfEq ℓ (pullback.diagonal_fst f)).app (𝟙_ _)).symm ≪≫
    (boundedConstructibleUpperShriekId ℓ X).app (𝟙_ _)

/-- `LΔ^* Lp₂^* K ≅ K`: the composition isomorphism `LΔ^* Lp₂^* ≅ L(Δ ≫ p₂)^* = L(𝟙 X)^*`
followed by `L(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def upperStarDiagonalPullbackSndIso (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (pullback.diagonal f)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (pullback.snd f f)).obj K) ≅ K :=
  ((boundedConstructibleUpperStarCompOfEq ℓ (pullback.diagonal_snd f)).app K).symm ≪≫
    (boundedConstructibleUpperStarId _ ℓ X).app K

/-- Blueprint `proposition-relative-dualizing-complex--1` (`ℚ̄_ℓ`-coefficients, formal part): **the
identification `ω_f ≅ ℚ̄_ℓ,X(d)[2d]` from the fundamental class of the diagonal**. Given an
identification `cl : RΔ^!(ℚ̄_ℓ(d)[2d]) ≅ ℚ̄_ℓ,X` (the fundamental class of the diagonal), and
assuming the base change map `Lp₂^* ω_f ⟶ ω_{p₁}` and the purity map of `Δ` at `ω_{p₁}` invertible,
```
ω_f ≅ LΔ^* Lp₂^* ω_f ≅ LΔ^* ω_{p₁} ≅ LΔ^*(ℚ̄_ℓ(d)[2d]) ≅ ℚ̄_ℓ,X(d)[2d],
```
the third isomorphism identifying both `LΔ^* ω_{p₁}` and `LΔ^*(ℚ̄_ℓ(d)[2d])` with the inverse of
`RΔ^! ℚ̄_ℓ` (`upperStarIsoOfUpperShriekIsoUnit`), through `RΔ^! ω_{p₁} ≅ ℚ̄_ℓ,X`
(`upperShriekDiagonalDualizingIso`) and `cl`. -/
noncomputable def dualizingComplexTateTwistIsoOfDiagonal (d : ℕ)
    (cl : (boundedConstructibleUpperShriek ℓ (pullback.diagonal f)).obj
      (boundedConstructibleTateTwist ℓ (pullback f f) d (2 * d)) ≅ 𝟙_ _)
    (hbc : IsIso (diagonalBaseChangeMap ℓ f))
    (hK : IsIso (upperShriekUnitTensorMap ℓ (pullback.diagonal f)
      ((boundedConstructibleUpperShriek ℓ (pullback.fst f f)).obj (𝟙_ _)))) :
    (boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _) ≅
      boundedConstructibleTateTwist ℓ X d (2 * d) :=
  (upperStarDiagonalPullbackSndIso ℓ f _).symm ≪≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (pullback.diagonal f)).mapIso (@asIso _ _ _ _ _ hbc) ≪≫
    upperStarIsoOfUpperShriekIsoUnit ℓ (pullback.diagonal f)
      (isDualizable_boundedConstructibleTateTwist_shift ℓ d (2 * d)) hK
      (upperShriekDiagonalDualizingIso ℓ f) cl ≪≫
    boundedConstructibleUpperStarTateTwistIso ℓ (pullback.diagonal f) d (2 * d)

end Diagonal

end AlgebraicGeometry.ProEtale.CondensedRing
