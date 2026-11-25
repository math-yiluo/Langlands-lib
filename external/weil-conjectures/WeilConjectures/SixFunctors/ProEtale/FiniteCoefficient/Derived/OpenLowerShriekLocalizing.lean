/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek

/-!
# Extension by zero on the localizing closures of `Dctf`

Let `Λ` be a finite ring and `j : U ⟶ X` a quasi-compact open immersion. This file shows that
the extension by zero `j_! : D(U_proét, Λ) ⥤ D(X_proét, Λ)`, applied levelwise to complexes,
carries `Dctf(U, Λ)` into `Dctf(X, Λ)`, preserves direct sums and therefore restricts to an
exact, sum-preserving functor `Loc(Dctf(U, Λ)) ⥤ Loc(Dctf(X, Λ))` between the localizing
closures (`CategoryTheory.ObjectProperty.localizingClosure`).

## Main statements

- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_mapDerivedCategory_openImmersionLowerShriek`:
  `j_!` preserves `Dctf`.
- `AlgebraicGeometry.ProEtale.localizingClosure_constructibleFiniteTor_openImmersionLowerShriek`
  (`proposition-proper-direct-image-extension-zero`, finite coefficient stages).

## Implementation notes

On the pro-étale site, bounded constructibility at a finite coefficient ring is étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`). An object of
`Dctf(U_proét, Λ)` is `ν^* K'` with `K'` in `Dctf(U_ét, Λ)` (the comparison `ν^*` detects Tor
amplitude), and `j_! ν^* K' ≅ ν^* j_! K'`, so the statement reduces to its étale counterpart (in the
namespace `AlgebraicGeometry.Etale`)
`boundedConstructible_and_torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek`
(`proposition-proper-direct-image-extension-zero--8`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j] [QuasiCompact j]

/-- For a finite ring `Λ` and a quasi-compact open immersion `j : U ⟶ X`, the extension by zero
`j_!` carries `Dctf(U_proét, Λ)` into `Dctf(X_proét, Λ)`. Writing an object of `Dctf(U_proét, Λ)`
as `ν^* K'` for some `K'` in `Dctf(U_ét, Λ)`, this follows from `j_! ν^* K' ≅ ν^* j_! K'` and the
étale case `proposition-proper-direct-image-extension-zero--8`. -/
theorem constructibleFiniteTor_mapDerivedCategory_openImmersionLowerShriek
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj K) := by
  obtain ⟨hbc, a', b', hta⟩ := hK
  obtain ⟨K', hK', ⟨e⟩⟩ := (DerivedCategory.boundedConstructible_iff _ _ K).1 hbc
  have hta' : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) U a' b' K' :=
    (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a' b' K').1
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) U a' b').prop_of_iso e.symm hta)
  obtain ⟨a, b, h⟩ :=
    (Etale.DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K').2
      ⟨hK', a', b', hta'⟩
  have h' := Etale.constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek
    Λ j a b h
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).prop_of_iso
    ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso _ j).app K' ≪≫
      D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapIso e)
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ ⟨h'.1.1, a, b, h'.2⟩)

/-- The extension by zero `j_! : D(U_proét) ⥤ D(X_proét)` along an open immersion preserves
direct sums (indeed all colimits), being left adjoint to `j^*`. -/
instance (J : Type w) :
    PreservesColimitsOfShape (Discrete J)
      D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) :=
  have : PreservesColimitsOfSize.{w, w}
      D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) :=
    (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).leftAdjoint_preservesColimits
  this.preservesColimitsOfShape

/-- Blueprint `proposition-proper-direct-image-extension-zero`: Extension by zero on the localizing
categories.

Let `Λ` be a finite ring (a finite coefficient stage `A`) and `j : U ⟶ X` a quasi-compact open
immersion. Then the extension by zero `j_! : D(U_proét, Λ) ⥤ D(X_proét, Λ)` maps `Dctf(U, Λ)`
into `Dctf(X, Λ)`, preserves direct sums, and maps `Loc(Dctf(U, Λ))` into `Loc(Dctf(X, Λ))`.
The functor `j_!` is exact (`Functor.mapDerivedCategory` of an exact functor is triangulated),
so its restriction `Loc(Dctf(U, Λ)) ⥤ Loc(Dctf(X, Λ))` is exact and preserves direct sums. The
last assertion is `proposition-proper-direct-image-extension-zero`
(`CategoryTheory.ObjectProperty.localizingClosure_le_inverseImage`) applied to the first two. -/
theorem localizingClosure_constructibleFiniteTor_openImmersionLowerShriek :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U ≤
        (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).inverseImage
          D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) ∧
      (∀ J : Type w, PreservesColimitsOfShape (Discrete J)
        D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)) ∧
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U).localizingClosure ≤
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure
          ).inverseImage D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) :=
  ⟨fun _ hK ↦ constructibleFiniteTor_mapDerivedCategory_openImmersionLowerShriek Λ j hK,
    fun _ ↦ inferInstance,
    ObjectProperty.localizingClosure_le_inverseImage _ _ fun _ hK ↦
      ObjectProperty.le_localizingClosure _ _
        (constructibleFiniteTor_mapDerivedCategory_openImmersionLowerShriek Λ j hK)⟩

end AlgebraicGeometry.ProEtale
