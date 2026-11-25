/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardDataProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardDataRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriek

/-!
# The compact-support base change on `Dᵇc(-)⟦𝒪_E⟧` for proper morphisms

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` and `sq : IsPullback g' p' p g` a cartesian square
of separated `k`-schemes of finite type with `p` and `p'` proper. This file shows that the
compact-support base change `Ex_! : Lg^* Rp_! ⟶ Rp'_! Lg'^*` on bounded constructible
`𝒪_E`-complexes (`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicIntegers`)
is, through the isomorphisms `κ_p : Rp_! ≅ Rp_*` and `κ_{p'} : Rp'_! ≅ Rp'_*`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`), the proper
base change morphism `Ex_* : Lg^* Rp_* ⟶ Rp'_* Lg'^*`
(`ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructibleBaseChange`), i.e. the mate of
the pullback square comparison `θ_sq : Lg^* ⋙ Lp'^* ≅ Lp^* ⋙ Lg'^*` under the adjunctions
`Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`.

This is the `𝒪_E` analogue of
`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper'`; it is
the instance for the pushforward datum of `𝒪_E` of
`ProEtale.CondensedRing.BoundedConstructiblePushforwardData.lowerShriekBaseChange_of_isProper`.

## Main results

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicIntegers_of_isProper`:
  `Ex_! ≫ κ_{p'} = κ_p ≫ Ex_*`.
- `boundedConstructibleLowerShriekBaseChange_padicIntegers_of_isProper_mateEquiv`:
  `κ_p ≫ mateEquiv (Lp^* ⊣ Rp_*) (Lp'^* ⊣ Rp'_*) θ_sq = Ex_! ≫ κ_{p'}`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- The isomorphism `Rp_! ≅ Rp_*` on bounded constructible `𝒪_E`-complexes for a proper `p` is the
one of the pushforward datum of `𝒪_E`. -/
lemma boundedConstructibleLowerShriekIsoLowerStar_padicIntegers_eq_pushforwardData (p : X ⟶ Y)
    [IsProper p.left] :
    boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p =
      BoundedConstructiblePushforwardData.lowerShriekIsoLowerStar
        (isIsoRefinementPushforward_padicIntegersPushforwardData ℓ k E) p := by
  unfold boundedConstructibleLowerShriekIsoLowerStar_padicIntegers
    boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers
  rfl

variable {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left]
  [IsProper p'.left]

/-- **`Ex_!` on `𝒪_E`-complexes for proper vertical maps is `Ex_*`**: under the identifications
`κ_p : Rp_! ≅ Rp_*` and `κ_{p'} : Rp'_! ≅ Rp'_*`, the compact-support base change of a cartesian
square with `p` and `p'` proper is the proper base change morphism `Ex_* : Lg^* Rp_* ⟶ Rp'_* Lg'^*`:
`Ex_! ≫ κ_{p'} = κ_p ≫ Ex_*`. -/
theorem boundedConstructibleLowerShriekBaseChange_padicIntegers_of_isProper
    (sq : IsPullback g' p' p g) :
    boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq ≫
        Functor.whiskerLeft
          (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ g')
          (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p').hom =
      Functor.whiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p).hom
          (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ g) ≫
        PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E sq.toCommSq := by
  -- Normalize the structure maps before identifying the adjunctions and square comparison.
  obtain ⟨Xl, ⟨⟨⟩⟩, Xh⟩ := X
  obtain ⟨Xl', ⟨⟨⟩⟩, Xh'⟩ := X'
  obtain ⟨pl, ⟨⟨⟨⟩⟩⟩, pw⟩ := p
  obtain ⟨pl', ⟨⟨⟨⟩⟩⟩, pw'⟩ := p'
  change Xl ⟶ Y.left at pl
  change Xl' ⟶ Y'.left at pl'
  obtain rfl : Xh = pl ≫ Y.hom := by simpa using pw.symm
  obtain rfl : Xh' = pl' ≫ Y'.hom := by simpa using pw'.symm
  rewrite [boundedConstructibleLowerShriekBaseChange_padicIntegers_eq_pushforwardData,
    boundedConstructibleLowerShriekIsoLowerStar_padicIntegers_eq_pushforwardData,
    boundedConstructibleLowerShriekIsoLowerStar_padicIntegers_eq_pushforwardData,
    PadicIntegersRingObj.boundedConstructibleBaseChange_eq_exchangeRight]
  have key := BoundedConstructiblePushforwardData.lowerShriekBaseChange_of_isProper
    (isIsoRefinementPushforward_padicIntegersPushforwardData ℓ k E) sq
  exact key

/-- **`Ex_!` on `𝒪_E`-complexes for proper vertical maps is the mate of the pullback square
comparison**: under the identifications `κ_p : Rp_! ≅ Rp_*` and `κ_{p'} : Rp'_! ≅ Rp'_*`
(`boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`), the compact-support base change
`Ex_! : Rp_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rp'_!` of a cartesian square with `p` and `p'` proper is the mate
`Rp_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rp'_*` of the pullback square comparison
`θ_sq : Lg^* ⋙ Lp'^* ≅ Lp^* ⋙ Lg'^*` under the adjunctions `Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`:
`κ_p ≫ mateEquiv θ_sq = Ex_! ≫ κ_{p'}` (as morphisms `Rp_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rp'_*`). -/
theorem boundedConstructibleLowerShriekBaseChange_padicIntegers_of_isProper_mateEquiv
    (sq : IsPullback g' p' p g) :
    Functor.whiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p).hom
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ g) ≫
      (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ
          sq.toCommSq).hom) =
    boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq ≫
      Functor.whiskerLeft
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ g')
        (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p').hom := by
  rw [boundedConstructibleLowerShriekBaseChange_padicIntegers_of_isProper,
    PadicIntegersRingObj.boundedConstructibleBaseChange_eq_exchangeRight,
    Adjunction.exchangeRight_eq_mateEquiv]

end AlgebraicGeometry.ProEtale.CondensedRing
