/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeProperTrace
public import WeilConjectures.WeilSheaf.SmoothPurityProperPointTrace
public import WeilConjectures.WeilSheaf.SmoothPurityNativeDescent

/-!
# Native descent of the proper exceptional unit

The exceptional unit of a proper structural morphism is the native realization
of the finite-base exceptional unit. The comparison is obtained from the actual
descended trace, so it respects the Weil datum.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  (a : X ⟶ Spec (CommRingCat.of k₀))
  [a.IsOver (Spec (CommRingCat.of k₀))] [IsProper a]

local instance instFactPrimeRingChar_smoothPurityNativeProperDualizing
    : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩
local instance : (boundedConstructible (condensedRingObj
    (Profinite.padicAlgClRingObj l) (Spec (CommRingCat.of k₀)))).IsMonoidal :=
  CondensedRing.isMonoidal_boundedConstructible l (CondensedRing.point k₀)
noncomputable local instance : MonoidalCategory (BoundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (CommRingCat.of k₀)))) :=
  ObjectProperty.fullMonoidalSubcategory _
local instance instLocallyOfFiniteType_smoothPurityNativeProperDualizing
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_smoothPurityNativeProperDualizing
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_smoothPurityNativeProperDualizing
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance : IsProper
    (properTraceBaseMap (k₀ := k₀) a).left :=
  ‹IsProper a›
local instance : IsProper
    (CondensedRing.traceGeometricFiberOverMap
      (properTraceBaseMap (k₀ := k₀) a)).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
    a (comp_over a _) inferInstance

/-- A right adjoint to proper direct image sends the descended finite-base unit
to the descended finite-base exceptional unit. -/
theorem nonempty_rightAdjoint_finiteBaseNativeDescent_unit_iso
    {J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerStar (k₀ := k₀) (l := l) a ⊣ J) :
    Nonempty (J.obj ((finiteBaseNativeDescent (k₀ := k₀) (l := l)
      (X := Spec (CommRingCat.of k₀))).obj (𝟙_ _)) ≅
      (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).obj
        ((CondensedRing.boundedConstructibleUpperShriek l
          (properTraceBaseMap (k₀ := k₀) a)).obj (𝟙_ _))) := by
  let P := (CondensedRing.boundedConstructibleUpperShriek l (properTraceBaseMap (k₀ := k₀) a)).obj
    (𝟙_ _)
  let T := (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).obj P
  let U := (finiteBaseNativeDescent (k₀ := k₀) (l := l)
    (X := Spec (CommRingCat.of k₀))).obj (𝟙_ _)
  let eT := (finiteBaseNativeDescentComparison (k₀ := k₀) (l := l) (X := X)).app P
  let eU := (finiteBaseNativeDescentComparison (k₀ := k₀) (l := l)
    (X := Spec (CommRingCat.of k₀))).app (𝟙_ _)
  have hbc := CondensedRing.isIso_upperShriekBaseChange_geometricFiber_unit l
    (properTraceBaseMap (k₀ := k₀) a)
  have hi := isIso_homEquiv_nativeProperTrace_of_isIso a (𝟙 P) T U eT eU hbc adj
  exact ⟨(asIso (adj.homEquiv T U (nativeProperTrace a (𝟙 P) T U eT eU))).symm⟩

/-- The proper exceptional unit is the native descent of the ordinary dualizing
complex over the finite field. -/
theorem nonempty_rightAdjoint_finiteBaseNativeDescent_dualizing_iso
    {J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerStar (k₀ := k₀) (l := l) a ⊣ J) :
    Nonempty (J.obj ((finiteBaseNativeDescent (k₀ := k₀) (l := l)
      (X := Spec (CommRingCat.of k₀))).obj (𝟙_ _)) ≅
      (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).obj
        (CondensedRing.dualizingComplex l (Over.mk (X ↘ Spec (CommRingCat.of k₀))))) := by
  obtain ⟨e⟩ := nonempty_rightAdjoint_finiteBaseNativeDescent_unit_iso a adj
  exact ⟨e ≪≫ (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).mapIso
    ((CondensedRing.boundedConstructibleUpperShriek l (properTraceBaseMap (k₀ := k₀) a)).mapIso
      (CondensedRing.dualizingComplexPointIso l k₀).symm ≪≫
      CondensedRing.upperShriekDualizingComplexIso l (properTraceBaseMap (k₀ := k₀) a))⟩

end AlgebraicGeometry.WeilComplex
