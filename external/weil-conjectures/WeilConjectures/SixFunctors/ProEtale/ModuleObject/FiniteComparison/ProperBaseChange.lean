/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.DerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-!
# Proper base change for module objects with finite coefficients

Let `T` be a finite discrete commutative ring, `T̲ = C(-, T)` its condensed ring and
`Φ = ProEtale.finiteCoefficientDerivedEquivalence` the comparison of the derived category of
module objects over `T̲_X` with that of pro-étale sheaves of `T`-modules. Call a complex `C` of
module objects *bounded below of étale origin* if `Φ C` is
(`ProEtale.DerivedCategory.plusEtaleOrigin`).

* Direct images along quasi-compact quasi-separated morphisms preserve complexes bounded below of
  étale origin
  (`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj`).
* **Proper base change**: for a cartesian square with proper `f`, the base change morphism
  `Lg^* Rf_* M ⟶ Rf'_* Lg'^* M` of module objects over `T̲` is invertible at every `M` bounded
  below of étale origin
  (`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_finiteCoefficient`).
  This is the finite-level pro-étale proper base change
  (`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`, blueprint
  `proposition-proper-direct-image-constructible-complexes--5`) read through `Φ`
  (`ProEtale.isIso_baseChangeMap_app_finiteCoefficient_iff`). No hypothesis is made on `g`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Direct images preserve module complexes of étale origin**: for `f` quasi-compact and
quasi-separated, if `Φ C` is bounded below of étale origin, so is `Φ (Rf_* C)`: `Φ` commutes with
the derived direct images (`ProEtale.finiteCoefficientDerivedLowerStarIso`), and the pro-étale
direct image of a complex of étale origin is of étale origin
(`ProEtale.DerivedCategory.plusEtaleOrigin_rightDerivedLowerStar_obj`). -/
lemma plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj C)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y
      ((finiteCoefficientDerivedEquivalence Y T).functor.obj
        (R((f)_*⟦Profinite.continuousMapRingObj T⟧).obj C)) :=
  ObjectProperty.prop_of_iso _ ((finiteCoefficientDerivedLowerStarIso T f).app C)
    (DerivedCategory.plusEtaleOrigin_rightDerivedLowerStar_obj _ f hC)

namespace CondensedRing

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Proper base change for module objects with finite coefficients** (blueprint
`proposition-proper-direct-image-constructible-complexes--5`, read on module objects): for a
cartesian square `g' ≫ f = f' ≫ g` with `f` proper and a complex `M` of module objects over `T̲_X`
bounded below of étale origin, the base change morphism `Lg^* Rf_* M ⟶ Rf'_* Lg'^* M` is an
isomorphism. It is the finite-level pro-étale proper base change
`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper` at `Φ M`, transported along `Φ`
(`ProEtale.isIso_baseChangeMap_app_finiteCoefficient_iff`). -/
theorem isIso_baseChangeMap_app_of_isProper_finiteCoefficient [IsProper f]
    (sq : IsPullback g' f' f g)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)))
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj M)) :
    IsIso ((baseChangeMap (Profinite.continuousMapRingObj T) sq.toCommSq).app M) :=
  (isIso_baseChangeMap_app_finiteCoefficient_iff sq.toCommSq M).2
    (isIso_derivedBaseChangeMap_app_of_isProper _ sq _ hM)

end CondensedRing

end AlgebraicGeometry.ProEtale
