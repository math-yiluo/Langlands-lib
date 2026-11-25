/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeDirectTraceCriterion
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedWeilUniversality
public import WeilConjectures.WeilSheaf.CondensedModelBaseChangeCoherence

/-!
# Native universality of a descended smooth proper trace

Given the source and target identifications with descended finite-base objects,
the trace is constructed by full faithfulness. Its adjunct is invertible by the
geometric universal property and the free Weil resolution.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale
open scoped ProEtale.CondensedRing

attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]

local instance : (objectProperty k₀ l X).ι.Full := (objectProperty k₀ l X).fullyFaithfulι.full
local instance : (objectProperty k₀ l Y).ι.Full := (objectProperty k₀ l Y).fullyFaithfulι.full
local instance : (objectProperty k₀ l X).ι.Faithful :=
  (objectProperty k₀ l X).fullyFaithfulι.faithful
local instance : (objectProperty k₀ l Y).ι.Faithful :=
  (objectProperty k₀ l Y).fullyFaithfulι.faithful

local instance instFactPrimeRingChar_smoothPurityNativeProperTrace
    : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeProperTrace_3
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeProperTrace_3
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeProperTrace_3
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeProperTrace_4
    : LocallyOfFiniteType (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeProperTrace_4
    : QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeProperTrace_4
    : IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (Y ↘ Spec (CommRingCat.of k₀)))

local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeProperTrace : LocallyOfFiniteType
    (Over.mk (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeProperTrace : QuasiCompact
    (Over.mk (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeProperTrace : IsSeparated
    (Over.mk (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeProperTrace_2
    : LocallyOfFiniteType
    (Over.mk (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeProperTrace_2 : QuasiCompact
    (Over.mk (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeProperTrace_2 : IsSeparated
    (Over.mk (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))

/-- The given proper morphism, as a morphism over the finite base field. -/
noncomputable abbrev properTraceBaseMap :
    Over.mk (X ↘ Spec (CommRingCat.of k₀)) ⟶ Over.mk (Y ↘ Spec (CommRingCat.of k₀)) :=
  Over.homMk f (comp_over f (Spec (CommRingCat.of k₀)))

local instance : IsProper (properTraceBaseMap (k₀ := k₀) f).left := ‹IsProper f›
local instance : IsProper
    (CondensedRing.traceGeometricFiberOverMap (properTraceBaseMap (k₀ := k₀) f)).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
    f (comp_over f _) inferInstance

variable {P : Dᵇc(X)⟦Profinite.padicAlgClRingObj l⟧}
  {N : Dᵇc(Y)⟦Profinite.padicAlgClRingObj l⟧}
  (γ : P ⟶
    (CondensedRing.boundedConstructibleUpperShriek l (properTraceBaseMap (k₀ := k₀) f)).obj N)
  (T : WeilComplex k₀ l X) (U : WeilComplex k₀ l Y)
  (eT : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj T.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj P.obj)
  (eU : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj U.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (Y ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj N.obj)

/-- The descended proper trace in the condensed coordinates of the native objects. -/
noncomputable def condensedProperTrace :
    (CondensedRing.geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l)
      f (comp_over f _)).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj T.obj) ⟶
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj U.obj :=
  (CondensedRing.geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l)
    f (comp_over f _)).rightDerivedFunctor.map eT.hom ≫
  CondensedRing.geometricFiberWeilDirectTrace (Profinite.padicAlgClRingObj l)
    (CondensedRing.upperStarWeilCompatible _ f (comp_over f _))
    (((CondensedRing.boundedConstructibleLowerStar l (properTraceBaseMap (k₀ := k₀) f)).map γ ≫
      (CondensedRing.lowerStarUpperShriekAdjunction l
        (properTraceBaseMap (k₀ := k₀) f)).counit.app N).hom) ≫
  eU.inv

/-- Lift the descended proper trace to native Weil complexes. -/
noncomputable def nativeProperTrace :
    (derivedLowerStar (k₀ := k₀) (l := l) f).obj T ⟶ U :=
  ((objectProperty k₀ l Y).ι ⋙
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor).preimage
    ((directTraceCondensedComparison f).hom.app T ≫ condensedProperTrace f γ T U eT eU)

/-- The lifted trace has its prescribed condensed image. -/
lemma nativeProperTrace_map :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.map
      (nativeProperTrace f γ T U eT eU).hom =
    (directTraceCondensedComparison f).hom.app T ≫ condensedProperTrace f γ T U eT eU :=
  ((objectProperty k₀ l Y).ι ⋙
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor).map_preimage _

/-- The descended condensed trace is universal on every native constructible source. -/
theorem bijective_map_comp_condensedProperTrace [IsIso γ]
    [IsIso ((CondensedRing.upperShriekBaseChangeOfMap l (f := properTraceBaseMap (k₀ := k₀) f)
      (f' := CondensedRing.traceGeometricFiberOverMap (properTraceBaseMap (k₀ := k₀) f))
      (Scheme.Hom.isPullback_geometricFiberMap f (comp_over f _)).flip).app N)]
    (K : WeilComplex k₀ l X) :
    (CondensedRing.geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l)
      f (comp_over f _)).rightDerivedFunctor.TraceUniversalAt
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K.obj)
        (condensedProperTrace f γ T U eT eU) := by
  dsimp only [Functor.TraceUniversalAt, condensedProperTrace]
  apply Functor.bijective_map_comp_iso_trace _ eT eU.symm
  exact CondensedRing.geometricFiberWeilDirectTrace_weilUniversal l
    (properTraceBaseMap (k₀ := k₀) f) (CondensedRing.upperStarWeilCompatible _ f (comp_over f _)) γ
    ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K.obj)
    (boundedConstructible_condensedCarrier K)


/-- The adjunct of the native descended trace is invertible when exceptional
base change and the finite-base orientation are invertible. -/
theorem isIso_homEquiv_nativeProperTrace_of_isIso [IsIso γ]
    (hbc : IsIso ((CondensedRing.upperShriekBaseChangeOfMap l (f := properTraceBaseMap (k₀ := k₀) f)
      (f' := CondensedRing.traceGeometricFiberOverMap (properTraceBaseMap (k₀ := k₀) f))
      (Scheme.Hom.isPullback_geometricFiberMap f (comp_over f _)).flip).app N))
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerStar (k₀ := k₀) (l := l) f ⊣ J) :
    IsIso (adj.homEquiv T U (nativeProperTrace f γ T U eT eU)) := by
  have := hbc
  have := (objectProperty k₀ l X).fullyFaithfulι.full
  have := (objectProperty k₀ l Y).fullyFaithfulι.full
  have := (objectProperty k₀ l X).fullyFaithfulι.faithful
  have := (objectProperty k₀ l Y).fullyFaithfulι.faithful
  apply Adjunction.isIso_homEquiv_of_fullyFaithful_trace adj
    ((objectProperty k₀ l X).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor)
    ((objectProperty k₀ l Y).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor)
    _ (directTraceCondensedComparison f) _ (condensedProperTrace f γ T U eT eU)
    (nativeProperTrace_map f γ T U eT eU)
  intro K
  exact bijective_map_comp_condensedProperTrace f γ T U eT eU K

/-- The adjunct of the native descended trace is invertible for a smooth proper
map and an invertible finite-base orientation. -/
theorem isIso_homEquiv_nativeProperTrace [IsIso γ] (d : ℕ)
    [SmoothOfRelativeDimension d f]
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerStar (k₀ := k₀) (l := l) f ⊣ J) :
    IsIso (adj.homEquiv T U (nativeProperTrace f γ T U eT eU)) := by
  have : SmoothOfRelativeDimension d (properTraceBaseMap (k₀ := k₀) f).left := ‹_›
  have := CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale l
    (f := properTraceBaseMap (k₀ := k₀) f)
    (f' := CondensedRing.traceGeometricFiberOverMap (properTraceBaseMap (k₀ := k₀) f)) d
    (Scheme.Hom.isPullback_geometricFiberMap f (comp_over f _)).flip N
  exact isIso_homEquiv_nativeProperTrace_of_isIso f γ T U eT eU inferInstance adj

end AlgebraicGeometry.WeilComplex
