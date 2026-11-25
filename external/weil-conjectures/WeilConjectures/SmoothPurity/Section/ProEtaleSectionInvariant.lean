/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-!
# The pro-étale section invariant

For a finite coefficient ring `Λ`, a compactifiable morphism `g : V ⟶ B` and a section `s` of
`g`, the *pro-étale section invariant* is `𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` on the small
pro-étale site of `B` (blueprint `lemma-section-normal-bundle--1`). No hypothesis on the base or on
the coefficients beyond finiteness is needed for the definition.

The pro-étale exceptional inverse image is `Rg^! = ν_V^* ∘ g^× ∘ Rν_{B,*}`, so the pro-étale
section invariant is, canonically, the comparison pullback `ν_B^*` of the étale one
(`AlgebraicGeometry.ProEtale.sectionInvariantComparisonIso`): `Rν_* Λ_B = Λ_B` and `ν^*` commutes
with derived pullbacks. Every construction with étale section invariants transports along this
identification; this file does so for base change.

## Main definitions

- `AlgebraicGeometry.ProEtale.sectionInvariant`: the pro-étale section invariant.
- `AlgebraicGeometry.ProEtale.sectionInvariantComparisonIso`: `𝒞(g, s) ≅ ν_B^* 𝒞_ét(g, s)`.
- `AlgebraicGeometry.ProEtale.sectionInvariantBaseChangeIso`: `Lg^* 𝒞(f, s) ≅ 𝒞(f', s')` in a
  cartesian square, transported from `AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lemma-section-normal-bundle--1`: the section invariant
`𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` on the small pro-étale site of `B`, for a finite coefficient
ring `Λ`, a compactifiable `g : V ⟶ B` and `s : B ⟶ V`. Its geometric properties concern closed
sections of smooth morphisms; the definition makes sense for any `s`. -/
noncomputable def sectionInvariant {V B : Scheme.{u}} (g : V ⟶ B) [HasCompactification g]
    (s : B ⟶ V) : DerivedCategory (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} Λ)) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} Λ) s).leftDerivedFunctor.obj (dualizingComplex Λ g)

/-- The pro-étale section invariant is the comparison pullback of the étale one,
`𝒞(g, s) ≅ ν_B^* 𝒞_ét(g, s)`: by definition `ω_g = ν_V^* g^× Rν_{B,*} Λ_B`, and
`Rν_{B,*} Λ_B ≅ Λ_B` (`AlgebraicGeometry.ProEtale.rightDerivedComparisonLowerStarUnitIso`) and
`Ls^* ν_V^* ≅ ν_B^* Ls^*` (`AlgebraicGeometry.ProEtale.derivedComparisonUpperStarUpperStarIso`). -/
noncomputable def sectionInvariantComparisonIso {V B : Scheme.{u}} (g : V ⟶ B)
    [HasCompactification g]
    (s : B ⟶ V) :
    sectionInvariant Λ g s ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.obj
        (Etale.sectionInvariant Λ g s) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} Λ) s).leftDerivedFunctor.mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.mapIso
        ((Etale.rightDerivedUpperShriek Λ g).mapIso
          (rightDerivedComparisonLowerStarUnitIso B Λ))) ≪≫
    (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) s).app
      (Etale.dualizingComplex Λ g)

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- Blueprint `prose-09-12` (1): *base change of pro-étale section invariants.*
In a cartesian square `g' ≫ f = f' ≫ g` whose base change map of étale dualizing complexes is
invertible (for instance `f` smooth,
`AlgebraicGeometry.Etale.isIso_dualizingComplexBaseChangeMap_of_smoothOfRelativeDimension`), and
for sections `s` of `f` and `s'` of `f'` with `s' ≫ g' = g ≫ s`,

`Lg^* 𝒞(f, s) ≅ Lg^* ν^* 𝒞_ét(f, s) ≅ ν^* Lg^* 𝒞_ét(f, s) ≅ ν^* 𝒞_ét(f', s') ≅ 𝒞(f', s')`,

through `AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso`. -/
noncomputable def sectionInvariantBaseChangeIso (sq : IsPullback g' f' f g)
    [IsIso (Etale.dualizingComplexBaseChangeMap Λ sq)] (s : Y ⟶ X) (s' : Y' ⟶ X')
    (hs : s' ≫ g' = g ≫ s) :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj (sectionInvariant Λ f s) ≅
      sectionInvariant Λ f' s' :=
  (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.mapIso
      (sectionInvariantComparisonIso Λ f s) ≪≫
    (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) g).app _ ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.mapIso
      (Etale.sectionInvariantBaseChangeIso Λ sq s s' hs) ≪≫
    (sectionInvariantComparisonIso Λ f' s').symm

end BaseChange

end ProEtale

end AlgebraicGeometry
