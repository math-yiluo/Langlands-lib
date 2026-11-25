/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTraceUnit

public import WeilConjectures.WeilSheaf.SmoothPurityNativeShriekTraceCriterion
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedUnitBaseChange

/-! # A native Weil orientation from unit base change and Tate coordinates -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

local instance instFactPrimeRingChar_smoothPurityNativeUnitOrientation
    : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩

variable {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeUnitOrientation_3
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeUnitOrientation_3
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeUnitOrientation_3
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeUnitOrientation_4
    : LocallyOfFiniteType (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeUnitOrientation_4
    : QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeUnitOrientation_4
    : IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (Y ↘ Spec (CommRingCat.of k₀)))


variable (d : ℕ) (T : WeilComplex k₀ l X) (U : WeilComplex k₀ l Y)
  (eT : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj T.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
        (CondensedRing.boundedConstructibleTateTwist l
          (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d (2 * d)).obj)
  (eU : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj U.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (Y ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj (𝟙_ _))


local instance : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
  ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ Fact.out⟩
local instance : Fact (ringChar (AlgebraicClosure k₀) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)⟩
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeUnitOrientation
    : LocallyOfFiniteType
    (Over.mk ((Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeUnitOrientation : QuasiCompact
    (Over.mk ((Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeUnitOrientation : IsSeparated
    (Over.mk ((Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeUnitOrientation_2
    : LocallyOfFiniteType
    (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeUnitOrientation_2 : QuasiCompact
    (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeUnitOrientation_2 : IsSeparated
    (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))

include eT eU in
/-- Unit base change, together with the native Tate and unit coordinates, gives
an isomorphism from the native right adjoint at the unit to the native Tate object. -/
theorem nonempty_shriekRightAdjoint_obj_iso_of_unitBaseChange
    [SmoothOfRelativeDimension d f]
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerShriek k₀ l f ⊣ J)
    (e : (CondensedRing.boundedConstructibleUpperStarOfMap l
      (X := Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
      (Y := Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure))
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).obj
        (CondensedRing.smoothTraceUnit l (Over.mk (Y ↘ Spec (CommRingCat.of k₀)))) ≅
      CondensedRing.smoothTraceUnit l
        (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)))
    [IsIso (CondensedRing.smoothUnitBaseChange l
      (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
        (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _))
      (CondensedRing.traceGeometricFiberOverMap
        (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
          (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)))
      (CondensedRing.descendedShriekGeometricExchange l
        (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
          (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _))) e.hom)] :
    Nonempty (J.obj U ≅ T) := by
  have : SmoothOfRelativeDimension d
      (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
        (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)).left :=
    ‹SmoothOfRelativeDimension d f›
  have ho := isIso_purityMapOfDescendedSmoothTrace_of_universal f d T U eT eU adj
    (fun K ↦ CondensedRing.geometricFiberWeilSmoothTrace_weilUniversal_of_unitBaseChange l
      (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
        (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)) e d
      ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K.obj)
      (boundedConstructible_condensedCarrier K))
  exact ⟨(asIso (purityMapOfDescendedSmoothTrace f d T U eT eU adj)).symm⟩

end AlgebraicGeometry.WeilComplex
