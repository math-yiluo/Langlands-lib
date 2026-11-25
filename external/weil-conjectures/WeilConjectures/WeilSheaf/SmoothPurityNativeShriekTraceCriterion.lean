/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeTrace
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedShriekUniversality

/-! # A universal descended compact-support trace gives a native orientation -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

local instance instFactPrimeRingChar_smoothPurityNativeShriekTraceCriterion
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

local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeShriekTraceCriterion
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeShriekTraceCriterion
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeShriekTraceCriterion
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeShriekTraceCriterion_2
    : LocallyOfFiniteType (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeShriekTraceCriterion_2
    : QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeShriekTraceCriterion_2
    : IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (Y ↘ Spec (CommRingCat.of k₀)))

/-- The condensed compact-support comparison in the coordinates of the descended trace. -/
noncomputable def shriekTraceCondensedComparison :
    derivedLowerShriek k₀ l f ⋙ (objectProperty k₀ l Y).ι ⋙
        (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor ≅
      (objectProperty k₀ l X).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor ⋙
        CondensedRing.weilRightDerivedLowerShriek
          (s := X ↘ Spec (CommRingCat.of k₀)) (t := Y ↘ Spec (CommRingCat.of k₀))
          (Profinite.padicAlgClRingObj l)
          (CondensedRing.compactificationOverField
            (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
              (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)))
          (comp_over f _) :=
  derivedLowerShriekCompToCondensedIso k₀ l f ≪≫
    Functor.isoWhiskerLeft (objectProperty k₀ l X).ι
      (Functor.isoWhiskerLeft (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor
        (eqToIso (condensedShriekForTrace_eq f)))

lemma shriekTraceCondensedComparison_hom_app (T : WeilComplex k₀ l X) :
    (shriekTraceCondensedComparison f).hom.app T = (condensedShriekForTraceIso f T).hom := by
  simp [shriekTraceCondensedComparison, condensedShriekForTraceIso]

variable (d : ℕ) (T : WeilComplex k₀ l X) (U : WeilComplex k₀ l Y)
  (eT : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj T.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
        (CondensedRing.boundedConstructibleTateTwist l
          (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d (2 * d)).obj)
  (eU : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj U.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (Y ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj (𝟙_ _))

/-- Full faithfulness transfers universality of the descended Weil trace to the
adjoint transpose of its native lift. -/
theorem isIso_purityMapOfDescendedSmoothTrace_of_universal
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerShriek k₀ l f ⊣ J)
    (h : ∀ K : WeilComplex k₀ l X,
      (CondensedRing.weilRightDerivedLowerShriek
        (s := X ↘ Spec (CommRingCat.of k₀)) (t := Y ↘ Spec (CommRingCat.of k₀))
        (Profinite.padicAlgClRingObj l)
        (CondensedRing.compactificationOverField
          (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
            (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)))
        (comp_over f _)).TraceUniversalAt
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K.obj)
        (CondensedRing.geometricFiberWeilSmoothTrace l
          (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
            (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)) d)) :
    IsIso (purityMapOfDescendedSmoothTrace f d T U eT eU adj) := by
  have := (objectProperty k₀ l X).fullyFaithfulι.full
  have := (objectProperty k₀ l X).fullyFaithfulι.faithful
  have := (objectProperty k₀ l Y).fullyFaithfulι.full
  have := (objectProperty k₀ l Y).fullyFaithfulι.faithful
  let L := CondensedRing.weilRightDerivedLowerShriek
    (s := X ↘ Spec (CommRingCat.of k₀)) (t := Y ↘ Spec (CommRingCat.of k₀))
    (Profinite.padicAlgClRingObj l)
    (CondensedRing.compactificationOverField
      (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
        (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _))) (comp_over f _)
  have he := Adjunction.isIso_homEquiv_of_fullyFaithful_trace adj
    ((objectProperty k₀ l X).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor)
    ((objectProperty k₀ l Y).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor)
    L (shriekTraceCondensedComparison f) (traceOfDescendedSmoothTrace f d T U eT eU)
    (L.map eT.hom ≫ CondensedRing.geometricFiberWeilSmoothTrace l
      (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
        (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)) d ≫ eU.inv)
    (by
      rw [shriekTraceCondensedComparison_hom_app]
      exact map_traceOfDescendedSmoothTrace f d T U eT eU)
    (fun K ↦ Functor.bijective_map_comp_iso_trace L eT eU.symm _ (h K))
  exact he

end AlgebraicGeometry.WeilComplex
