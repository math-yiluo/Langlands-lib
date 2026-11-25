/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.SixFunctors.Etale.DivisorComplementDirectImage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Stalks of the direct images from the complement of a divisor

If `j : U ⟶ X` has the higher direct images of the complement of a divisor `i : D ⟶ X`
(`AlgebraicGeometry.Etale.HasDivisorComplementDirectImages`), the stalks of `R^q j_* ℤ/ℓ` at a
geometric point of `D` are `ℤ/ℓ` for `q ≤ 1` and zero for `q ≥ 2` (blueprint
`lemma-punctured-surface-punctured-curve--1`): the stalks of a constant sheaf are its value, and the
stalk of `i_* G` at a geometric point of `D` is the stalk of `G = i^* i_* G`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_constantZModModule`
- `AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_lowerStar_constantZModModule`
- `AlgebraicGeometry.Etale.HasDivisorComplementDirectImages.subsingleton_sheafFiber`
- `AlgebraicGeometry.Etale.HasDivisorComplementDirectImages.nonempty_addEquiv_sheafFiber`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ℓ : ℕ)

/-- The stalk of the constant sheaf `ℤ/ℓ` at a geometric point is `ℤ/ℓ`. -/
theorem nonempty_addEquiv_sheafFiber_constantZModModule {X : Scheme.{u}}
    (s : Spec (.of Ω) ⟶ X) :
    Nonempty (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))).obj
      (constantZModModule X ℓ) ≃+ ZMod ℓ) :=
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  ⟨((pointSmallEtale s).sheafFiberConstantSheafIso
    (ModuleCat.of (ZModCoeff.{u} ℓ) (ZModCoeff.{u} ℓ))).toLinearEquiv.toAddEquiv.trans
      AddEquiv.ulift⟩

/-- The stalk of `i_* ℤ/ℓ`, for a closed immersion `i : D ⟶ X`, at a geometric point of `D`
is `ℤ/ℓ`. -/
theorem nonempty_addEquiv_sheafFiber_lowerStar_constantZModModule {X D : Scheme.{u}}
    (i : D ⟶ X) [IsClosedImmersion i] (s : Spec (.of Ω) ⟶ D) :
    Nonempty (((pointSmallEtale (s ≫ i)).sheafFiber
        (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))).obj
      ((i)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D ℓ)) ≃+ ZMod ℓ) := by
  obtain ⟨e⟩ := nonempty_addEquiv_sheafFiber_constantZModModule ℓ s
  let c := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) i).counit.app
    (constantZModModule D ℓ)
  exact ⟨(((upperStarCompSheafFiberIso (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) i s).app
      _).symm ≪≫ (pointSmallEtale s).sheafFiber.mapIso (asIso c)).toLinearEquiv.toAddEquiv.trans
    e⟩

namespace HasDivisorComplementDirectImages

variable {ℓ} {U X D : Scheme.{u}} {j : U ⟶ X} {i : D ⟶ X}

/-- The stalks of `R^q j_* ℤ/ℓ` vanish for `q ≥ 2`. -/
theorem subsingleton_sheafFiber (hj : HasDivisorComplementDirectImages ℓ j i)
    (s : Spec (.of Ω) ⟶ X) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (((pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))).obj
        (higherDirectImage (ZModCoeff.{u} ℓ) j q (constantZModModule U ℓ))) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))
  exact ModuleCat.subsingleton_of_isZero (Functor.map_isZero _ (hj.1 q hq))

/-- The stalks of `R⁰j_* ℤ/ℓ` are `ℤ/ℓ`. -/
theorem nonempty_addEquiv_sheafFiber_zero (hj : HasDivisorComplementDirectImages ℓ j i)
    (s : Spec (.of Ω) ⟶ X) :
    Nonempty (((pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))).obj
        (higherDirectImage (ZModCoeff.{u} ℓ) j 0 (constantZModModule U ℓ)) ≃+ ZMod ℓ) := by
  obtain ⟨e₀⟩ := hj.2.1
  obtain ⟨e⟩ := nonempty_addEquiv_sheafFiber_constantZModModule ℓ s
  exact ⟨((pointSmallEtale s).sheafFiber.mapIso e₀).toLinearEquiv.toAddEquiv.trans e⟩

/-- The stalks of `R¹j_* ℤ/ℓ` at geometric points of `D` are `ℤ/ℓ`. -/
theorem nonempty_addEquiv_sheafFiber_one (hj : HasDivisorComplementDirectImages ℓ j i)
    [IsClosedImmersion i] (s : Spec (.of Ω) ⟶ D) :
    Nonempty (((pointSmallEtale (s ≫ i)).sheafFiber
      (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))).obj
        (higherDirectImage (ZModCoeff.{u} ℓ) j 1 (constantZModModule U ℓ)) ≃+ ZMod ℓ) := by
  obtain ⟨e₁⟩ := hj.2.2
  obtain ⟨e⟩ := nonempty_addEquiv_sheafFiber_lowerStar_constantZModModule ℓ i s
  exact ⟨((pointSmallEtale (s ≫ i)).sheafFiber.mapIso e₁).toLinearEquiv.toAddEquiv.trans e⟩

end HasDivisorComplementDirectImages

end AlgebraicGeometry.Etale
