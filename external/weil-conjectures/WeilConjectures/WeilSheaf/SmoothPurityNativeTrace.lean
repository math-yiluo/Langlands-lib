/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTrace

/-!
# The descended smooth trace in native Weil complexes

Given identifications of native complexes with the descended Tate source and the
descended constant target, the exact equivalence with condensed Weil sheaves lifts
the finite-field smooth trace to a native morphism. Its adjoint transpose is a native
purity morphism. The source and target identifications are explicit inputs here.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

local instance instFactPrimeRingChar_smoothPurityNativeTrace
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
  (d : ℕ) (T : WeilComplex k₀ l X) (U : WeilComplex k₀ l Y)

local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeTrace
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeTrace
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeTrace
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityNativeTrace_2
    : LocallyOfFiniteType (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityNativeTrace_2
    : QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityNativeTrace_2
    : IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (Y ↘ Spec (CommRingCat.of k₀)))

variable
  (eT : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj T.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
        (CondensedRing.boundedConstructibleTateTwist l
          (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d (2 * d)).obj)
  (eU : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj U.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (Y ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj (𝟙_ _))

omit [Fact (ringChar k₀ ≠ l)] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] in
/-- Identify the two spellings of the chosen compact-support functor once, before
composing the trace. The compactification choices use the same proposition. -/
lemma condensedShriekForTrace_eq :
    ProEtaleWeilSheaf.condensedRightDerivedLowerShriek k₀ l f
        (HasCompactification.compactification f
          (hf := hasCompactification_of_over (k₀ := k₀) f)) =
      CondensedRing.weilRightDerivedLowerShriek
      (s := X ↘ Spec (CommRingCat.of k₀)) (t := Y ↘ Spec (CommRingCat.of k₀))
      (Profinite.padicAlgClRingObj l)
        (CondensedRing.compactificationOverField
          (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
          (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
          f (comp_over f (Spec (CommRingCat.of k₀)))))
        (comp_over f (Spec (CommRingCat.of k₀))) := by
  rw [ProEtaleWeilSheaf.condensedRightDerivedLowerShriek_eq]
  rfl

/-- The comparison with condensed compact support, in the spelling used by the
finite-field descended trace. -/
noncomputable def condensedShriekForTraceIso :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj
      ((derivedLowerShriek k₀ l f).obj T).obj ≅
    (CondensedRing.weilRightDerivedLowerShriek
      (s := X ↘ Spec (CommRingCat.of k₀)) (t := Y ↘ Spec (CommRingCat.of k₀))
      (Profinite.padicAlgClRingObj l)
      (CondensedRing.compactificationOverField
        (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
          (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
          f (comp_over f (Spec (CommRingCat.of k₀)))))
      (comp_over f (Spec (CommRingCat.of k₀)))).obj
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj T.obj) :=
  (derivedLowerShriekCompToCondensedIso k₀ l f).app T ≪≫
    eqToIso (congrArg (fun F ↦ F.obj
      ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj T.obj))
        (condensedShriekForTrace_eq f))

/-- The condensed expression of the trace, with the compactification comparison explicit. -/
noncomputable def condensedExpressionOfSmoothTrace :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj
        ((derivedLowerShriek k₀ l f).obj T).obj ⟶
      (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj U.obj :=
  (condensedShriekForTraceIso f T).hom ≫
    (CondensedRing.weilRightDerivedLowerShriek
      (s := X ↘ Spec (CommRingCat.of k₀)) (t := Y ↘ Spec (CommRingCat.of k₀))
      (Profinite.padicAlgClRingObj l)
      (CondensedRing.compactificationOverField
        (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
          (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
          f (comp_over f (Spec (CommRingCat.of k₀)))))
      (comp_over f (Spec (CommRingCat.of k₀)))).map eT.hom ≫
    CondensedRing.geometricFiberWeilSmoothTrace l
      (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
          (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
          f (comp_over f (Spec (CommRingCat.of k₀)))) d ≫ eU.inv

/-- Lift the descended smooth trace through the fully faithful condensed realization. -/
noncomputable def traceOfDescendedSmoothTrace : (derivedLowerShriek k₀ l f).obj T ⟶ U :=
  ((objectProperty k₀ l Y).ι ⋙
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor).preimage
      (condensedExpressionOfSmoothTrace f d T U eT eU)

/-- The condensed realization of the native trace is the prescribed descended trace. -/
theorem map_traceOfDescendedSmoothTrace :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.map
        (traceOfDescendedSmoothTrace f d T U eT eU).hom =
      condensedExpressionOfSmoothTrace f d T U eT eU :=
  ((objectProperty k₀ l Y).ι ⋙
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor).map_preimage _

variable {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
  (adj : derivedLowerShriek k₀ l f ⊣ J)

/-- The purity morphism obtained by transposing the descended native trace. -/
noncomputable def purityMapOfDescendedSmoothTrace : T ⟶ J.obj U :=
  adj.homEquiv T U (traceOfDescendedSmoothTrace f d T U eT eU)

/-- The adjoint transpose has the prescribed native trace as its counit composite. -/
theorem map_purityMapOfDescendedSmoothTrace_comp_counit :
    (derivedLowerShriek k₀ l f).map (purityMapOfDescendedSmoothTrace f d T U eT eU adj) ≫
      adj.counit.app U = traceOfDescendedSmoothTrace f d T U eT eU := by
  exact (adj.homEquiv T U).symm_apply_apply _

end AlgebraicGeometry.WeilComplex
