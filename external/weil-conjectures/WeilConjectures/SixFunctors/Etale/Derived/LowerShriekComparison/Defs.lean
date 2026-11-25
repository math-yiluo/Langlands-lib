/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange

/-!

# The comparison of derived lower shrieks along a refinement: definitions

## Main definitions

- `AlgebraicGeometry.Etale.refinementLowerStarComp`: the composition isomorphism
  `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards attached to a refinement.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`: the
  comparison `Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+`. (blueprint: `BA43-RHO`)

See `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison` for the construction and
the implementation notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The composition isomorphism `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards on étale
sheaves attached to a refinement `r : c.Refinement d`, coming from
`Etale.lowerStarComp` and the relation `r.hom ≫ d.g = c.g`. -/
noncomputable def refinementLowerStarComp : (r.hom)_*[A] ⋙ (d.g)_*[A] ≅ (c.g)_*[A] :=
  Etale.lowerStarComp A r.hom d.g ≪≫ eqToIso (by rw [r.hom_g])

/-- The base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*` on bounded below derived
categories, induced by `Compactification.Refinement.openImmersionLowerShriekBaseChange` for
a refinement whose square over `X` is cartesian. -/
noncomputable def refinementLowerShriekBaseChangeDerivedPlusIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    (c.i)_!open[A].mapDerivedCategoryPlus ≅
      (d.i)_!open[A].mapDerivedCategoryPlus ⋙ (r.hom)^*[A].mapDerivedCategoryPlus :=
  haveI := r.isIso_openImmersionLowerShriekBaseChange A hcart
  Functor.mapDerivedCategoryPlusNatIso (asIso (r.openImmersionLowerShriekBaseChange A)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The comparison `Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+` of the bounded below derived lower shrieks
attached to two compactifications `c`, `d` of `f : X ⟶ Y` linked by a refinement
`r : c.Refinement d` whose square over `X` is cartesian.

It is the composite of the unit of the derived adjunction
`D(r.hom)^* ⊣ R(r.hom)_*`, the inverse of the base change isomorphism
`D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*`, and the composition isomorphism
`R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`. Note that it goes from the coarser compactification `d`
to the finer one `c`. (blueprint: `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) : Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+ :=
  haveI : ((r.hom)_*[A]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A r.hom)
  Functor.whiskerRight (Functor.whiskerLeft (d.i)_!open[A].mapDerivedCategoryPlus
      (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit)
      (d.g)_*[A].rightDerivedFunctorPlus ≫
    Functor.whiskerRight (refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).inv
      ((r.hom)_*[A].rightDerivedFunctorPlus ⋙ (d.g)_*[A].rightDerivedFunctorPlus) ≫
    Functor.whiskerLeft (c.i)_!open[A].mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusCompIso' (r.hom)_*[A] (d.g)_*[A]
        (refinementLowerStarComp A r)).hom

/-- The comparison isomorphism `Functor.mapDerivedCategoryPlusNatIso` and the composition
isomorphism `Functor.mapDerivedCategoryPlusCompIso` out of which
`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso` is built are both
characterized by their compatibility with the factorizations
`Functor.mapDerivedCategoryPlusFactorsh` through the localization functors; this is the
resulting characterization of the base change isomorphism itself. -/
@[reassoc]
lemma refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).hom.app
          (DerivedCategory.Plus.Qh.obj K) ≫
        ((r.hom)^*[A]).mapDerivedCategoryPlus.map
          (((d.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((d.i)_!open[A]).mapHomotopyCategoryPlus.obj K) =
      ((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (r.openImmersionLowerShriekBaseChange A)).app K) := by
  simp only [refinementLowerShriekBaseChangeDerivedPlusIso, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh]
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  simp only [asIso_hom]

end Etale

end AlgebraicGeometry
