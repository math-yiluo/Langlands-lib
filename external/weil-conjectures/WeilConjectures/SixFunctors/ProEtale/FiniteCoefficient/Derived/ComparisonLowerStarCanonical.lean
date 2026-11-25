/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison

/-!
# The canonical comparison of derived direct images

For a morphism of schemes `f : X ⟶ Y`, the comparison pullbacks `ν^*` from étale to pro-étale
sheaves and the direct images `f_*` are related by the canonical base change morphism
`ν_Y^* f_* ⟶ f_* ν_X^*` (`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange`),
the mate under the adjunctions `ν^* ⊣ ν_*` of the identification `ν_{Y,*} f_* ≅ f_* ν_{X,*}`.
Since `ν^*` is exact, it induces a canonical base change morphism of bounded below right derived
functors `ν_Y^* ∘ Rf_* ⟶ Rf_* ∘ ν_X^*`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusBaseChange`), and for `f`
quasi-compact and quasi-separated this morphism is an isomorphism (blueprint
`theorem-bounded-below-cohomology-comparison`, the comparison direct image): the underived morphism
is invertible and `ν^*` sends injective étale sheaves to `f_*`-acyclic pro-étale sheaves.

This makes the isomorphism of
`AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar`
canonical, so that constructions built on it (the compact-support comparison
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`) are canonical as well.

## Main definitions

- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusBaseChange`: the canonical
  base change morphism `ν_Y^* ∘ R⁺f_* ⟶ R⁺f_* ∘ ν_X^*`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusIso`: for `f` quasi-compact and
  quasi-separated, the same morphism as an isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The canonical base change morphism `ν_Y^* ∘ R⁺f_* ⟶ R⁺f_* ∘ ν_X^*` of functors
`D⁺(X_ét) ⥤ D⁺(Y_proét)`: the base change morphism of bounded below right derived functors
induced by the underived base change morphism `ν_Y^* f_* ⟶ f_* ν_X^*`
(`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange`), itself the mate of the
identification `ν_{Y,*} f_* ≅ f_* ν_{X,*}`. It is characterized by its compatibility with the
units of the derived functors
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusBaseChange_fac`). -/
noncomputable def rightDerivedLowerStarComparisonPlusBaseChange :
    R+(Etale.lowerStar A f) ⋙ D+(ν^*(Y)[A]) ⟶ D+(ν^*(X)[A]) ⋙ R+(ProEtale.lowerStar A f) :=
  Functor.rightDerivedFunctorPlusBaseChange (lowerStarComparisonUpperStarBaseChange f A)

/-- The canonical base change morphism `ν_Y^* ∘ R⁺f_* ⟶ R⁺f_* ∘ ν_X^*` is the unique morphism
which, on the image of a bounded below complex `K`, is the underived base change morphism
`ν_Y^* f_* K ⟶ f_* ν_X^* K` followed by the unit `f_* ν_X^* K ⟶ R⁺f_* (ν_X^* K)`. -/
@[reassoc]
theorem rightDerivedLowerStarComparisonPlusBaseChange_fac :
    (Functor.whiskerRight (Etale.lowerStar A f).rightDerivedFunctorPlusUnith D+(ν^*(Y)[A]) ≫
        (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        (rightDerivedLowerStarComparisonPlusBaseChange f A) =
    Functor.rightDerivedFunctorPlusBaseChangeAux (lowerStarComparisonUpperStarBaseChange f A) :=
  Functor.rightDerivedFunctorPlusBaseChange_fac _

/-- Blueprint `theorem-bounded-below-cohomology-comparison`, the comparison direct image: for `f`
quasi-compact and quasi-separated, the canonical base change morphism
`ν_Y^* ∘ R⁺f_* ⟶ R⁺f_* ∘ ν_X^*` is an isomorphism. The underived base change morphism is invertible
(`AlgebraicGeometry.ProEtale.isIso_lowerStarComparisonUpperStarBaseChange`) and `ν_X^*` sends
injective étale sheaves to `f_*`-acyclic pro-étale sheaves
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective`). -/
instance isIso_rightDerivedLowerStarComparisonPlusBaseChange [QuasiCompact f]
    [QuasiSeparated f] : IsIso (rightDerivedLowerStarComparisonPlusBaseChange f A) :=
  have := isIso_lowerStarComparisonUpperStarBaseChange f A
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (asIso (lowerStarComparisonUpperStarBaseChange f A))
    (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective A f I)

/-- Blueprint `theorem-comparison-direct-images--1` (and
`theorem-bounded-below-cohomology-comparison`, the comparison direct image): for `f` quasi-compact
and quasi-separated, the canonical isomorphism `ν_Y^* Rf_* ≅ Rf_* ν_X^*` on bounded below derived
categories, the base change morphism
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusBaseChange` of right derived functors
induced by the underived comparison `ν_Y^* f_* ⟶ f_* ν_X^*`
(`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange`). -/
noncomputable def rightDerivedLowerStarComparisonPlusIso [QuasiCompact f] [QuasiSeparated f] :
    R+(Etale.lowerStar A f) ⋙ D+(ν^*(Y)[A]) ≅ D+(ν^*(X)[A]) ⋙ R+(ProEtale.lowerStar A f) :=
  asIso (rightDerivedLowerStarComparisonPlusBaseChange f A)

@[simp]
theorem rightDerivedLowerStarComparisonPlusIso_hom [QuasiCompact f] [QuasiSeparated f] :
    (rightDerivedLowerStarComparisonPlusIso f A).hom =
      rightDerivedLowerStarComparisonPlusBaseChange f A :=
  rfl

end AlgebraicGeometry.ProEtale
