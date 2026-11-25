/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.StrictLocalizationVanishing
public import WeilConjectures.SixFunctors.Etale.ZModCoefficients

/-!
# Cohomology over the strict localization as a stalk of a higher direct image

Let `f : U ⟶ Z` be quasi-compact and quasi-separated, `s : Spec Ω ⟶ Z` a geometric point with
`Ω` algebraically closed and `S = Z_(s)` the strict localization. By the stalk formula (Stacks
03Q9, `AlgebraicGeometry.Etale.strictHenselizationStalkFormula`) the abelian cohomology of the
pullback of a sheaf `F` of `Λ`-modules to `U ×_Z S` is the stalk at `s` of `R^q f_* F`. For the
constant sheaf `ℤ/ℓ`:

`H^q(U ×_Z S, ℤ/ℓ) ≅ (R^q f_* ℤ/ℓ)_s`

(blueprint `lemma-punctured-surface-punctured-curve--1`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_forget₂_sheafFiber_higherDirectImage`
- `AlgebraicGeometry.Etale.nonempty_addEquiv_sheafH_constantZMod_sheafFiber`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- **The stalk formula, after forgetting `Λ`** (Stacks 03Q9): the stalk at a geometric point
`s` of `R^q f_* F` is, as an abelian group, the cohomology of the pullback of `F` to
`U ×_Z Z_(s)`. -/
theorem nonempty_iso_forget₂_sheafFiber_higherDirectImage {Λ : Type (u + 1)} [CommRing Λ]
    {U Z : Scheme.{u}} (f : U ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Z)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Nonempty ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((Scheme.pointSmallEtale s).sheafFiber.obj (higherDirectImage Λ f q F)) ≅
      (Sheaf.functorH.{u + 1} _ q).obj ((sheafForget₂ Λ _).obj
        ((pullback.fst f (Scheme.strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F))) := by
  let : PreservesColimitsOfSize.{u, u} (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
  let p := pullback.fst f (Scheme.strictLocalizationToBase s)
  obtain ⟨e₁⟩ := nonempty_higherDirectImage_forget_iso Λ f q F
  obtain ⟨r, -, hr⟩ := unrestricted_strictHenselization_stalk f s ((sheafForget₂ Λ _).obj F) q
  obtain ⟨e₂⟩ := Scheme.nonempty_sheafH_extDerivedIso (pullback f
    (Scheme.strictLocalizationToBase s)) q
  let E := (Scheme.pointSmallEtale s).sheafFiberCompIso.{u, u, u + 1, u + 1, u + 1, u + 2, u + 2}
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  exact ⟨(E.app _).symm ≪≫ (Scheme.pointSmallEtale s).sheafFiber.mapIso e₁ ≪≫
    asIso (r ≫ strictHenselizationCohomologyComparison s f ((sheafForget₂ Λ _).obj F) q) ≪≫
    (Etale.cohomology AddCommGrpCat.{u + 1} _ (q : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (asIso (upperStarForget₂Comparison Λ p F))) ≪≫ (e₂.app _).symm⟩

/-- **The stalk formula for the constant sheaf `ℤ/ℓ`** (blueprint
`lemma-punctured-surface-punctured-curve--1`, Stacks 03Q9): for `f : U ⟶ Z` quasi-compact and
quasi-separated and a geometric point `s` of `Z`,

`H^q(U ×_Z Z_(s), ℤ/ℓ) ≅ (R^q f_* ℤ/ℓ)_s`. -/
theorem nonempty_addEquiv_sheafH_constantZMod_sheafFiber {U Z : Scheme.{u}} (f : U ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Z) (ℓ : ℕ) (q : ℕ) :
    Nonempty (Sheaf.H ((pullback f (Scheme.strictLocalizationToBase s)).constantZMod ℓ) q ≃+
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} (ZModCoeff.{u} ℓ))).obj
        (higherDirectImage (ZModCoeff.{u} ℓ) f q (constantZModModule U ℓ))) := by
  obtain ⟨e⟩ := nonempty_iso_forget₂_sheafFiber_higherDirectImage f s
    (constantZModModule U ℓ) q
  let e' : (sheafForget₂ (ZModCoeff.{u} ℓ) _).obj
      ((pullback.fst f (Scheme.strictLocalizationToBase s))^*[ModuleCat.{u + 1}
        (ZModCoeff.{u} ℓ)].obj (constantZModModule U ℓ)) ≅
      (pullback f (Scheme.strictLocalizationToBase s)).constantZMod ℓ :=
    (sheafForget₂ (ZModCoeff.{u} ℓ) _).mapIso
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) _).app _) ≪≫
      (constantSheafSheafComposeForget₂Iso (ZModCoeff.{u} ℓ)).app _
  exact ⟨((Sheaf.functorH.{u + 1} _ q).mapIso e'.symm ≪≫ e.symm).addCommGroupIsoToAddEquiv⟩

end AlgebraicGeometry.Etale
