/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
public import WeilConjectures.SixFunctors.Etale.ZModCoefficients

/-!
# Higher direct images from the complement of a divisor, and base change

Let `j : U ⟶ X` be an open immersion and `i : D ⟶ X` a closed immersion. We say that `j` has
the *higher direct images of the complement of the divisor `i`* (with `ℤ/ℓ` coefficients) when

`R⁰j_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j_* ℤ/ℓ ≅ i_* ℤ/ℓ` and `R^q j_* ℤ/ℓ = 0` for `q ≥ 2`

(`AlgebraicGeometry.Etale.HasDivisorComplementDirectImages`). This is what purity gives near a
point of a regular divisor `D` of a smooth scheme over an algebraically closed field, the Tate
twist `ℤ/ℓ(-1)` being trivialized (blueprint `lemma-punctured-surface-punctured-curve--1`).

The property is transported along every Cartesian square on which the base change maps of the
constant sheaf `ℤ/ℓ` are isomorphisms
(`AlgebraicGeometry.Etale.HasDivisorComplementDirectImages.of_isPullback`), e.g. along étale
morphisms and along limits of étale morphisms; the closed part uses proper base change for the
closed immersion `i` in degree zero.

## Main definitions

- `AlgebraicGeometry.Etale.HasDivisorComplementDirectImages`

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_upperStar_higherDirectImage_constantZModModule`
- `AlgebraicGeometry.Etale.HasDivisorComplementDirectImages.of_isPullback`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

/-- The higher direct images of the constant sheaf `ℤ/ℓ` commute with base change along `p`
as soon as the degree-`q` base change map of the Cartesian square at `ℤ/ℓ` is an isomorphism:
`p^* R^q g_* ℤ/ℓ ≅ R^q h_* ℤ/ℓ`. -/
theorem nonempty_iso_upperStar_higherDirectImage_constantZModModule {X S T Y : Scheme.{u}}
    {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) (ℓ : ℕ) (q : ℤ)
    (H : IsIso (baseChangeHomologyMap (ZModCoeff.{u} ℓ) sq q (constantZModModule T ℓ))) :
    Nonempty ((p)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj
        (higherDirectImage (ZModCoeff.{u} ℓ) g q (constantZModModule T ℓ)) ≅
      higherDirectImage (ZModCoeff.{u} ℓ) h q (constantZModModule Y ℓ)) :=
  ⟨((baseChangeSourceFunctorIso (ZModCoeff.{u} ℓ) p g q).app _).symm ≪≫
    asIso (baseChangeHomologyMap (ZModCoeff.{u} ℓ) sq q (constantZModModule T ℓ)) ≪≫
    (baseChangeTargetFunctorIso (ZModCoeff.{u} ℓ) e h q).app _ ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0 ⋙ R+((h)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)]) ⋙
      DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) e).app _)⟩

/-- Proper base change in degree zero for the pushforward of the constant sheaf `ℤ/ℓ` along a
closed immersion `i : D ⟶ X`: for any `p : X' ⟶ X`, `p^* i_* ℤ/ℓ ≅ i'_* ℤ/ℓ`, with
`i' : D ×_X X' ⟶ X'` the base change of `i`. -/
theorem nonempty_iso_upperStar_lowerStar_constantZModModule {X X' D : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (p : X' ⟶ X) (ℓ : ℕ) :
    Nonempty ((p)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj
        ((i)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D ℓ)) ≅
      (pullback.snd i p)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj
        (constantZModModule (pullback i p) ℓ)) := by
  have := isIso_baseChangeMap_of_isProper (ZModCoeff.{u} ℓ) (IsPullback.of_hasPullback i p)
  exact ⟨asIso ((baseChangeMap (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))
      (IsPullback.of_hasPullback i p).toCommSq).app (constantZModModule D ℓ)) ≪≫
    (pullback.snd i p)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))
        (pullback.fst i p)).app _)⟩

/-- An open immersion `j : U ⟶ X` has the *higher direct images of the complement of the
divisor* `i : D ⟶ X`, with coefficients `ℤ/ℓ`, if

`R⁰j_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j_* ℤ/ℓ ≅ i_* ℤ/ℓ` and `R^q j_* ℤ/ℓ = 0` for `q ≥ 2`.

This is the local form of purity for a regular divisor `D` of a smooth scheme over an
algebraically closed field, the Tate twist `ℤ/ℓ(-1)` being trivialized by a primitive `ℓ`-th
root of unity (blueprint `lemma-punctured-surface-punctured-curve--1`). The definition does not tie
`i` to `j`; in applications `D` is the complement of `U`. -/
def HasDivisorComplementDirectImages (ℓ : ℕ) {U X D : Scheme.{u}} (j : U ⟶ X) (i : D ⟶ X) :
    Prop :=
  (∀ q : ℕ, 2 ≤ q → IsZero (higherDirectImage (ZModCoeff.{u} ℓ) j q (constantZModModule U ℓ))) ∧
    Nonempty (higherDirectImage (ZModCoeff.{u} ℓ) j 0 (constantZModModule U ℓ) ≅
      constantZModModule X ℓ) ∧
    Nonempty (higherDirectImage (ZModCoeff.{u} ℓ) j 1 (constantZModModule U ℓ) ≅
      (i)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D ℓ))

namespace HasDivisorComplementDirectImages

variable {ℓ : ℕ} {U X D : Scheme.{u}} {j : U ⟶ X} {i : D ⟶ X}

/-- **Base change of the direct images from the complement of a divisor.** If the base change
maps of the constant sheaf `ℤ/ℓ` along `p` are isomorphisms for the Cartesian square of `j` and
`p` (for instance if `p` is étale, or a limit of étale morphisms), then the base change `j'` of
`j` has the higher direct images of the complement of the base change of `i`. -/
theorem of_isPullback (hj : HasDivisorComplementDirectImages ℓ j i) [IsClosedImmersion i]
    {X' U' : Scheme.{u}} (p : X' ⟶ X) {e : U' ⟶ U} {j' : U' ⟶ X'} (sq : IsPullback e j' j p)
    (H : ∀ q : ℕ, IsIso (baseChangeHomologyMap (ZModCoeff.{u} ℓ) sq q (constantZModModule U ℓ))) :
    HasDivisorComplementDirectImages ℓ j' (pullback.snd i p) := by
  obtain ⟨h₂, ⟨e₀⟩, ⟨e₁⟩⟩ := hj
  refine ⟨fun q hq ↦ ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := nonempty_iso_upperStar_higherDirectImage_constantZModModule sq ℓ q (H q)
    exact (Functor.map_isZero _ (h₂ q hq)).of_iso e.symm
  · obtain ⟨e⟩ := nonempty_iso_upperStar_higherDirectImage_constantZModModule sq ℓ 0 (H 0)
    exact ⟨e.symm ≪≫ (p)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].mapIso e₀ ≪≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) p).app _⟩
  · obtain ⟨e⟩ := nonempty_iso_upperStar_higherDirectImage_constantZModModule sq ℓ 1 (H 1)
    obtain ⟨e'⟩ := nonempty_iso_upperStar_lowerStar_constantZModModule i p ℓ
    exact ⟨e.symm ≪≫ (p)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].mapIso e₁ ≪≫ e'⟩

/-- The higher direct images of the complement of a divisor only depend on the pushforward of
`ℤ/ℓ` along the divisor. -/
theorem of_iso_lowerStar (hj : HasDivisorComplementDirectImages ℓ j i) {D' : Scheme.{u}}
    {i' : D' ⟶ X}
    (e : (i)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D ℓ) ≅
      (i')_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D' ℓ)) :
    HasDivisorComplementDirectImages ℓ j i' :=
  ⟨hj.1, hj.2.1, hj.2.2.map (· ≪≫ e)⟩

end HasDivisorComplementDirectImages

end AlgebraicGeometry.Etale
