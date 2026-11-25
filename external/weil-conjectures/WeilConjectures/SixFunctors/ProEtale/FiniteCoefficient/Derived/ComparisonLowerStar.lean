/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp

/-!
# The derived comparison functor commutes with derived direct images

For a morphism of schemes `g : X ⟶ Y`, the underived restriction functors
`ν_* : Sh(-_proét, A) ⥤ Sh(-_ét, A)` commute with the direct images along `g`
(`AlgebraicGeometry.ProEtale.lowerStarCompComparisonLowerStarIso`). Since the pro-étale direct
image `g_*` and the restriction `ν_*(X)` are right adjoints of exact functors, they preserve
K-injective complexes, so both composites of total right derived functors on the unbounded derived
categories are the total right derived functor of the common underived composite, and we obtain

`Rg_* ⋙ Rν_*(Y) ≅ Rν_*(X) ⋙ Rg_*`

(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompComparisonLowerStarIso`), characterized by
its compatibility with the units of the derived functors
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompComparisonLowerStarIso_fac_app`).

## Main definitions

- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompComparisonLowerStarIso`: the isomorphism
  `R(g_*) ⋙ R(ν_*(Y)) ≅ R(ν_*(X)) ⋙ R(g_*)` of functors `D(X_proét) ⥤ D(Y_ét)`.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The restriction `ν_*` preserves K-injective complexes, being right adjoint to the exact
functor `ν^*`. -/
instance preservesKInjectiveComplexes_comparisonLowerStar (X : Scheme.{u}) :
    (ν_*(X)[A]).PreservesKInjectiveComplexes :=
  (comparisonAdjunction A X).preservesKInjectiveComplexes

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The derived comparison functors commute with the derived direct images: for a morphism of
schemes `g : X ⟶ Y`, the isomorphism `R(g_*) ⋙ R(ν_*(Y)) ≅ R(ν_*(X)) ⋙ R(g_*)` of functors
`D(X_proét) ⥤ D(Y_ét)` on the unbounded derived categories. Both composites are identified with
the total right derived functor of `ν_*(X) ⋙ g_*`, the pro-étale direct image `g_*` and `ν_*(X)`
preserving K-injective complexes, using the underived isomorphism
`AlgebraicGeometry.ProEtale.lowerStarCompComparisonLowerStarIso`. -/
noncomputable def rightDerivedLowerStarCompComparisonLowerStarIso :
    R(ProEtale.lowerStar A g) ⋙ R(ν_*(Y)[A]) ≅ R(ν_*(X)[A]) ⋙ R(Etale.lowerStar A g) :=
  Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompComparisonLowerStarIso g A) ≪≫
    Functor.rightDerivedFunctorCompIso _ _

/-- The isomorphism `rightDerivedLowerStarCompComparisonLowerStarIso` is characterized by its
compatibility with the units of the derived functors: on a complex `K` of pro-étale sheaves on
`X`, the composite unit of `R(g_*) ⋙ R(ν_*(Y))` followed by it is the underived isomorphism
`g_* ⋙ ν_*(Y) ≅ ν_*(X) ⋙ g_*` followed by the composite unit of `R(ν_*(X)) ⋙ R(g_*)`. -/
@[reassoc]
lemma rightDerivedLowerStarCompComparisonLowerStarIso_fac_app
    (K : HomotopyCategory (Sheaf (ProEt.topology X) A) (ComplexShape.up ℤ)) :
    (ν_*(Y)[A]).rightDerivedFunctorUnit.app
        (((ProEtale.lowerStar A g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (R(ν_*(Y)[A])).map ((ProEtale.lowerStar A g).rightDerivedFunctorUnit.app K) ≫
        (rightDerivedLowerStarCompComparisonLowerStarIso A g).hom.app
          (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (lowerStarCompComparisonLowerStarIso g A).hom (ComplexShape.up ℤ)).app K) ≫
        (Etale.lowerStar A g).rightDerivedFunctorUnit.app
          (((ν_*(X)[A]).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (R(Etale.lowerStar A g)).map ((ν_*(X)[A]).rightDerivedFunctorUnit.app K) := by
  rw [rightDerivedLowerStarCompComparisonLowerStarIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.rightDerivedFunctorCompIso'_fac_app_assoc,
    Functor.rightDerivedFunctorCompIso_fac_app, Functor.rightDerivedFunctorCompUnit_app]

end AlgebraicGeometry.ProEtale
