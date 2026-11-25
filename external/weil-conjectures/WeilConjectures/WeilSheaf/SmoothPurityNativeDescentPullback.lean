/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeDescent
public import WeilConjectures.WeilSheaf.CondensedModelBaseChangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Closed

/-!
# Pullback of finite-base native descent

The ordinary pullback comparison is compatible with the descent datum. After
deriving and applying the coefficient equivalence, it identifies native
pullback with descent of finite-base pullback.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale
open scoped ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]

local instance instFactPrimeRingChar_smoothPurityNativeDescentPullback
    : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeDescentPullback
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeDescentPullback
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeDescentPullback
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeDescentPullback_2
    : LocallyOfFiniteType (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeDescentPullback_2
    : QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeDescentPullback_2
    : IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (Y ↘ Spec (CommRingCat.of k₀)))

/-- The finite-base constructible pullback, with the base structures explicit. -/
noncomputable abbrev finiteBaseTracePullback :
    Dᵇc(Y)⟦Profinite.padicAlgClRingObj l⟧ ⥤ Dᵇc(X)⟦Profinite.padicAlgClRingObj l⟧ :=
  CondensedRing.boundedConstructibleUpperStarOfMap l
    (X := Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
    (Y := Over.mk (X ↘ Spec (CommRingCat.of k₀))) f

/-- Pullback of native finite-base descent is finite-base descent of pullback. -/
noncomputable def finiteBaseNativeDescentUpperStarIso
    (P : Dᵇc(Y)⟦Profinite.padicAlgClRingObj l⟧) :
    (upperStar f).obj ((finiteBaseNativeDescent (k₀ := k₀)).obj P) ≅
      (finiteBaseNativeDescent (k₀ := k₀)).obj ((finiteBaseTracePullback (k₀ := k₀) f).obj P) :=
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.preimageIso
      ((ProEtaleWeilSheaf.upperStarMapDerivedCategoryCompIso k₀ l f).app
          ((finiteBaseNativeDescent (k₀ := k₀)).obj P).obj ≪≫
        (CondensedRing.geometricFiberMapWeilUpperStar (Profinite.padicAlgClRingObj l)
          f (comp_over f _)).mapDerivedCategory.mapIso
            ((finiteBaseNativeDescentComparison (k₀ := k₀)).app P) ≪≫
        ((Functor.mapDerivedCategoryCompIsoOfIso
          (CondensedRing.upperStarCompGeometricFiberWeilLowerStarIso
            (CondensedRing.upperStarWeilCompatible (Profinite.padicAlgClRingObj l)
              f (comp_over f _)))).app P.obj).symm ≪≫
        (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.mapIso
            ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
              (Profinite.padicAlgClRingObj l) f).app P.obj).symm ≪≫
        ((finiteBaseNativeDescentComparison (k₀ := k₀)).app
          ((finiteBaseTracePullback (k₀ := k₀) f).obj P)).symm))

end AlgebraicGeometry.WeilComplex
