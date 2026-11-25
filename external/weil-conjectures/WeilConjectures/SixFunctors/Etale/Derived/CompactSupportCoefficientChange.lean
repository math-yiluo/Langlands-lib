/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-!
# Change of finite coefficients for compact support

Let `Λ` be a finite coefficient ring (the stage `A = A_{E,n}`), `J` an ideal of `Λ` (so that
`B = Λ ⧸ J`, for instance `A_{E,m} = A_{E,n} ⧸ ϖ_E^m`, `m ≤ n`) and `f : X ⟶ Y` a morphism admitting
a compactification. Blueprint `lemma-sp-reduction--1` asserts that the
canonical coefficient comparison

`(Rf_! K) ⊗ᴸ_A B ⟶ Rf_!(K ⊗ᴸ_A B)`

is an isomorphism. As everywhere in the repository (see
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegralOfSupport`), the reduction
`K ⊗ᴸ_A B` is realised as the complex `K ⊗ᴸ (Λ ⧸ J)_X` of `Λ`-modules
(`AlgebraicGeometry.Etale.reductionModIdeal`), the restriction of scalars along `A ⟶ B` of the
blueprint's `B`-complex, which is how compact support with `B`-coefficients is computed inside
`D(-, A)`. The canonical comparison is the projection map
`PF : Rf_! K ⊗ᴸ (Λ ⧸ J)_Y ⟶ Rf_!(K ⊗ᴸ Lf^* (Λ ⧸ J)_Y)` of the tensor comparison, followed by
`Lf^* (Λ ⧸ J)_Y ≅ (Λ ⧸ J)_X`; it is an isomorphism because the projection formula holds at a
finite coefficient ring (`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`). In
particular neither the finite Tor amplitude nor the constructibility of `K` is needed, and no
flatness of `A ⟶ B` is used.

## Main statements

- `AlgebraicGeometry.Etale.hasProjectionFormula_constantQuotient_of_finite`: the comparison map
  is an isomorphism.
- `AlgebraicGeometry.Etale.compactSupportCoefficientChangeIso`: the resulting natural
  isomorphism `(Rf_! K) ⊗ᴸ_A B ≅ Rf_!(K ⊗ᴸ_A B)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasCompactification f] (J : Ideal Λ)

/-- The constant complex `(Λ ⧸ J)_Y` placed in degree `0`, the coefficient object `B = Λ ⧸ J`
of the reduction `AlgebraicGeometry.Etale.reductionModIdeal`. -/
noncomputable abbrev constantQuotient (Y : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (Λ ⧸ J)))

/-- Blueprint `lemma-sp-reduction--1`: Change of finite coefficients for
compact support, the comparison map.

For a finite coefficient ring `A = Λ` and `B = Λ ⧸ J`, the canonical coefficient comparison
`(Rf_! K) ⊗ᴸ_A B ⟶ Rf_!(K ⊗ᴸ_A Lf^* B)`, the projection map at the constant complex
`(Λ ⧸ J)_Y`, is an isomorphism for every `K` (in particular for every bounded constructible `K`
of finite Tor amplitude). -/
theorem hasProjectionFormula_constantQuotient_of_finite
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HasProjectionFormula (ModuleCat.{u + 1} Λ) f K (constantQuotient Λ J Y) :=
  hasProjectionFormula_of_finite Λ f K _

/-- Blueprint `lemma-sp-reduction--1`: Change of finite coefficients for
compact support.

Let `Λ` be a finite coefficient ring (`A = A_{E,n}`), `J` an ideal of `Λ` (`B = A_{E,m}`,
`J = (ϖ_E^m)`, `m ≤ n`) and `f : X ⟶ Y` a morphism admitting a compactification. The canonical
coefficient comparison is a natural isomorphism

`(Rf_! K) ⊗ᴸ_A B ≅ Rf_!(K ⊗ᴸ_A B)`,

the reductions `- ⊗ᴸ_A B` being realised as complexes of `Λ`-modules
(`AlgebraicGeometry.Etale.reductionModIdeal`). Its component at `K` is the projection map
`Rf_! K ⊗ᴸ (Λ ⧸ J)_Y ⟶ Rf_!(K ⊗ᴸ Lf^* (Λ ⧸ J)_Y)`
(`AlgebraicGeometry.Etale.compactSupportCoefficientChangeIso_hom_app`), an isomorphism by
`AlgebraicGeometry.Etale.hasProjectionFormula_constantQuotient_of_finite`, followed by the
identification `Lf^* (Λ ⧸ J)_Y ≅ (Λ ⧸ J)_X`. -/
noncomputable def compactSupportCoefficientChangeIso :
    R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ] :=
  have : ∀ K, IsIso ((((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f)).app
      (constantQuotient Λ J Y)).app K) := hasProjectionFormula_constantQuotient_of_finite Λ f J
  have := NatIso.isIso_of_isIso_app
    (((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f)).app
      (constantQuotient Λ J Y))
  (asIso (((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f)).app
      (constantQuotient Λ J Y)) : R(f)_![ModuleCat.{u + 1} Λ] ⋙
        derivedTensorRight _ Y (constantQuotient Λ J Y) ≅
      derivedTensorRight _ X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (constantQuotient Λ J Y)) ⋙
        R(f)_![ModuleCat.{u + 1} Λ]) ≪≫
    Functor.isoWhiskerRight ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).flip.mapIso
      (leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} Λ) f
        (ModuleCat.of Λ (Λ ⧸ J)))) _

/-- The component of the coefficient change at `K` is the projection map at `(Λ ⧸ J)_Y`,
followed by `Lf^* (Λ ⧸ J)_Y ≅ (Λ ⧸ J)_X`. -/
lemma compactSupportCoefficientChangeIso_hom_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactSupportCoefficientChangeIso Λ f J).hom.app K =
      ((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app (constantQuotient Λ J Y) ≫
        (R(f)_![ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).map
            (leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} Λ) f _).hom) := by
  simp [compactSupportCoefficientChangeIso]

end Etale

end AlgebraicGeometry
