/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!

# Independence of the unbounded derived lower shriek of the compactification

Let `f : X ⟶ Y` be a morphism of schemes. This file is the unbounded counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison` and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence`. For a refinement
`r : c.Refinement d` of compactifications of `f` whose square over `X` is cartesian, it
constructs the comparison

`Rf_!(d)[A] ⟶ Rf_!(c)[A]`

of the derived lower shrieks on the unbounded derived categories, from the coarser
compactification `d` to the finer one `c`, in the same way as its bounded below version
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`: the unit of
the derived adjunction `D(r.hom)^* ⊣ R(r.hom)_*`, the inverse of the base change isomorphism
`D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*`, and the composition isomorphism
`R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`. Since `(r.hom)^*` is exact, the adjunction is
`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction`, and no monoidal structure
on the coefficient category `A` is needed.

When `f` is quasi-compact, passing through the common refinement `Compactification.inf c d`
gives an isomorphism `Rf_!(c)[A] ≅ Rf_!(d)[A]` for any two compactifications, and in
particular an isomorphism `Rf_!(c)[A] ≅ R(f)_![A]` with the derived lower shriek defined by
the chosen compactification.

On bounded below objects, whiskering `rightDerivedLowerShriekOfCompactificationIso c d` by
`DerivedCategory.Plus.ι` should give the isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusιIso c d` built from the
bounded below comparisons. This is not proved yet: it needs the compatibility of the
unbounded derived unit, base change and composition isomorphisms with their bounded below
counterparts.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`: the
  comparison `Rf_!(d)[A] ⟶ Rf_!(c)[A]` along a refinement with cartesian square over `X`;
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationIso`: the isomorphism
  `Rf_!(c)[A] ≅ Rf_!(d)[A]`;
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`: the isomorphism
  `Rf_!(c)[A] ≅ R(f)_![A]`.

## Main results

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`: the
  comparison is an isomorphism. Not proved yet, see its docstring for the missing hypotheses.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*` on unbounded derived
categories, induced by `Compactification.Refinement.openImmersionLowerShriekBaseChange` for a
refinement whose square over `X` is cartesian. This is the unbounded counterpart of
`refinementLowerShriekBaseChangeDerivedPlusIso`. -/
noncomputable def refinementLowerShriekBaseChangeDerivedIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    D((c.i)_!open[A]) ≅ D((d.i)_!open[A]) ⋙ D((r.hom)^*[A]) :=
  haveI := r.isIso_openImmersionLowerShriekBaseChange A hcart
  Functor.mapDerivedCategoryNatIso (asIso (r.openImmersionLowerShriekBaseChange A)) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The comparison `Rf_!(d)[A] ⟶ Rf_!(c)[A]` of the unbounded derived lower shrieks attached
to two compactifications `c`, `d` of `f : X ⟶ Y` linked by a refinement `r : c.Refinement d`
whose square over `X` is cartesian. With `q = r.hom`, it is the composite

```
D(d.i)_! ⋙ R(d.g)_* ──η──▶ D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*
   ──(bc)⁻¹──▶ D(c.i)_! ⋙ Rq_* ⋙ R(d.g)_* ──comp──▶ D(c.i)_! ⋙ R(c.g)_*
```

of the unit `η` of the derived adjunction `Dq^* ⊣ Rq_*`, the inverse of the base change
isomorphism `refinementLowerShriekBaseChangeDerivedIso`, and the composition isomorphism
`Rq_* ⋙ R(d.g)_* ≅ R(c.g)_*`. As in the bounded below case
(`rightDerivedLowerShriekOfCompactificationPlusComparison`), it goes from the coarser
compactification `d` to the finer one `c`. (blueprint: unbounded analogue of `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) : Rf_!(d)[A] ⟶ Rf_!(c)[A] :=
  Functor.whiskerRight (Functor.whiskerLeft D((d.i)_!open[A])
      (Etale.mapDerivedUpperStarLowerStarAdjunction A r.hom).unit) R((d.g)_*[A]) ≫
    Functor.whiskerRight (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv
      (R((r.hom)_*[A]) ⋙ R((d.g)_*[A])) ≫
    Functor.whiskerLeft D((c.i)_!open[A])
      (Functor.rightDerivedFunctorCompIso' (r.hom)_*[A] (d.g)_*[A]
        (refinementLowerStarComp A r)).hom

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **The unit of `D(q^*) ⊣ Rq_*` at an extension by zero is an isomorphism.** Let
`r : c.Refinement d` be a refinement of compactifications whose square over `X` is cartesian,
and write `q = r.hom : c.Z ⟶ d.Z` and `j = d.i`. For torsion coefficients the unit
`j_! K ⟶ Rq_* q^* j_! K` is an isomorphism. It is checked on the open `X` and on its closed
complement `i : W ⟶ d.Z`:

* over `X`, `q^* j_! = (c.i)_!` is fully faithful, so the unit is invisible to `j^*`
  (`CategoryTheory.Adjunction.isIso_map_unit_app_obj`);
* over `W`, both sides vanish: `i^* j_! K = 0`, and by proper base change for the proper `q`,
  `i^* Rq_* q^* j_! K` is computed on `q⁻¹(W)`, which does not meet `X`. -/
theorem isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).unit.app
      (D((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K)) := by
  apply isIso_of_isIso_mapDerivedCategoryUpperStar_map _ d.i d.i.closedComplement
    d.i.range_closedComplement
  · have : D((d.i)_!open[ModuleCat.{u + 1} Λ]).Full :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction _ d.i).fullyFaithfulLOfIsIsoUnit.full
    have : D((d.i)_!open[ModuleCat.{u + 1} Λ]).Faithful :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction _ d.i).fullyFaithfulLOfIsIsoUnit.faithful
    have : D((c.i)_!open[ModuleCat.{u + 1} Λ]).Full :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction _ c.i).fullyFaithfulLOfIsIsoUnit.full
    have : D((c.i)_!open[ModuleCat.{u + 1} Λ]).Faithful :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction _ c.i).fullyFaithfulLOfIsIsoUnit.faithful
    have : (D((d.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ D((r.hom)^*[ModuleCat.{u + 1} Λ])).Full :=
      Functor.Full.of_iso (refinementLowerShriekBaseChangeDerivedIso _ r hcart)
    have : (D((d.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ D((r.hom)^*[ModuleCat.{u + 1} Λ])).Faithful :=
      Functor.Faithful.of_iso (refinementLowerShriekBaseChangeDerivedIso _ r hcart)
    exact Adjunction.isIso_map_unit_app_obj _
      (derivedOpenImmersionLowerShriekUpperStarAdjunction _ d.i) K
  · have hdisj : Disjoint (Set.range d.i.closedComplement.base) (Set.range d.i.base) := by
      rw [d.i.range_closedComplement]
      exact disjoint_compl_left
    refine isIso_of_source_target_iso_zero _
      (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ d.i
        d.i.closedComplement hdisj K).isoZero (IsZero.isoZero ?_)
    let sq := IsPullback.of_hasPullback r.hom d.i.closedComplement
    have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
    let N := D((r.hom)^*[ModuleCat.{u + 1} Λ]).obj (D((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K)
    have hN :
        IsZero (L((pullback.fst r.hom d.i.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj N) := by
      refine IsZero.of_iso ?_
        ((leftDerivedUpperStarIsoMapDerivedCategory _ _).app N ≪≫
          ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp _
            (pullback.fst r.hom d.i.closedComplement) r.hom) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm).app _).symm)
      refine isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _
        d.i _ (hdisj.mono_left ?_) K
      rw [pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp]
      exact Set.range_comp_subset_range _ _
    exact IsZero.of_iso
      ((R((pullback.snd r.hom d.i.closedComplement)_*[ModuleCat.{u + 1} Λ])).map_isZero hN)
      ((leftDerivedUpperStarIsoMapDerivedCategory _ _).symm.app _ ≪≫
        asIso ((derivedBaseChangeMap _ sq.toCommSq).app N))

/-- **The comparison of unbounded derived lower shrieks along a refinement is an
isomorphism** for torsion coefficients: for a refinement `r : c.Refinement d` whose square over
`X` is cartesian, the comparison `Rf_!(d)[Λ] ⟶ Rf_!(c)[Λ]` is an isomorphism. The composition
and base change factors of the comparison are isomorphisms, and so is the unit factor, by
`isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek`, which rests
on proper base change for `r.hom`. This is the unbounded form of `BA43-RHO`. -/
instance isIso_rightDerivedLowerShriekOfCompactificationComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    IsIso (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ) r hcart) := by
  have : IsIso (Functor.whiskerLeft D((d.i)_!open[ModuleCat.{u + 1} Λ])
      (Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).unit) :=
    have : ∀ K, IsIso ((Functor.whiskerLeft D((d.i)_!open[ModuleCat.{u + 1} Λ])
        (Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).unit).app K) :=
      fun K ↦ isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek
        r Λ hcart K
    NatIso.isIso_of_isIso_app _
  unfold rightDerivedLowerShriekOfCompactificationComparison
  infer_instance

end Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [QuasiCompact f]

/-- **The unbounded derived lower shriek does not depend on the compactification**: for two
compactifications `c` and `d` of a quasi-compact morphism `f`, the isomorphism
`Rf_!(c)[A] ≅ Rf_!(d)[A]` obtained by comparing both with the common refinement
`Compactification.inf c d`: the comparison along `Compactification.infFst c d` followed by the
inverse of the comparison along `Compactification.infSnd c d`.
(blueprint: unbounded analogue of `κ_{C,D}` in `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationIso
    (c d : Compactification f) : Rf_!(c)[ModuleCat.{u + 1} Λ] ≅ Rf_!(d)[ModuleCat.{u + 1} Λ] :=
  asIso (rightDerivedLowerShriekOfCompactificationComparison _
      (Compactification.infFst c d) (Compactification.isPullback_infFst c d)) ≪≫
    (asIso (rightDerivedLowerShriekOfCompactificationComparison _
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))).symm

variable [HasCompactification f]

/-- The unbounded derived lower shriek attached to any compactification `c` of a
quasi-compact morphism `f` is isomorphic to `R(f)_![A]`, the one attached to the chosen
compactification `HasCompactification.compactification f`.
(blueprint: unbounded analogue of `κ_{C,D}` in `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekIso (c : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] :=
  rightDerivedLowerShriekOfCompactificationIso Λ c (HasCompactification.compactification f)

end Etale

end AlgebraicGeometry
