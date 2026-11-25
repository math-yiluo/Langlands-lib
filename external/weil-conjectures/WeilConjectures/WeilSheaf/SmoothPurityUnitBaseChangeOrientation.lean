/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTraceUnit

public import WeilConjectures.WeilSheaf.SmoothPurityNativeUnitOrientation
public import WeilConjectures.WeilSheaf.SmoothPurityDescentSingle
public import WeilConjectures.WeilSheaf.SmoothPurityDescentUnit
public import WeilConjectures.WeilSheaf.UpperShriek

/-! # The cyclotomic Weil orientation from geometric unit base change -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

local instance instFactPrimeRingChar_smoothPurityUnitBaseChangeOrientation
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

local instance instLocallyOfFiniteType_weilSheafSmoothPurityUnitBaseChangeOrientation_3
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityUnitBaseChangeOrientation_3
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityUnitBaseChangeOrientation_3
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityUnitBaseChangeOrientation_4
    : LocallyOfFiniteType (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityUnitBaseChangeOrientation_4
    : QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityUnitBaseChangeOrientation_4
    : IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (Y ↘ Spec (CommRingCat.of k₀)))

local instance : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
  ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ Fact.out⟩
local instance : Fact (ringChar (AlgebraicClosure k₀) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)⟩
local instance instLocallyOfFiniteType_weilSheafSmoothPurityUnitBaseChangeOrientation
    : LocallyOfFiniteType
    (Over.mk ((Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityUnitBaseChangeOrientation
    : QuasiCompact
    (Over.mk ((Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityUnitBaseChangeOrientation : IsSeparated
    (Over.mk ((Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityUnitBaseChangeOrientation_2
    : LocallyOfFiniteType
    (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityUnitBaseChangeOrientation_2
    : QuasiCompact
    (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityUnitBaseChangeOrientation_2
    : IsSeparated
    (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))


variable (d : ℕ) [SmoothOfRelativeDimension d f]
  (α : (ProEtaleWeilSheaf.toCondensed k₀ l X).obj
      (WeilSheaf.tateTwistSheaf k₀ l X d).obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).obj (ProEtale.tateTwist X l d))
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
          (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _))) e.hom)]

include α e

/-- The native Tate encoding turns the shriek universality criterion into the
usual orientation of the constant Weil complex. -/
theorem nonempty_shriekRightAdjoint_adicConstant_iso_of_unitBaseChange
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerShriek k₀ l f ⊣ J) :
    Nonempty (J.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨o⟩ := nonempty_shriekRightAdjoint_obj_iso_of_unitBaseChange f d
    ((finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).obj
      (CondensedRing.boundedConstructibleTateTwist l
        (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d (2 * d)))
    ((finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := Y)).obj
      (CondensedRing.smoothTraceUnit l (Over.mk (Y ↘ Spec (CommRingCat.of k₀)))))
    ((finiteBaseNativeDescentComparison (k₀ := k₀) (l := l) (X := X)).app _)
    ((finiteBaseNativeDescentComparison (k₀ := k₀) (l := l) (X := Y)).app _) adj e
  exact ⟨J.mapIso (finiteBaseNativeDescentUnitIso (k₀ := k₀) (l := l) (X := Y)).symm ≪≫
    o ≪≫ finiteBaseNativeDescentTateIso d (2 * d) α ≪≫
    (shiftFunctor _ (2 * d : ℤ)).mapIso (tateTwistConstantSingleIso d).symm⟩

variable [HasUpperShriek k₀ l f]

/-- The orientation obtained by descent commutes with Frobenius because it is
already an isomorphism of native Weil complexes. -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_unitBaseChange :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  obtain ⟨o⟩ := nonempty_shriekRightAdjoint_adicConstant_iso_of_unitBaseChange f d α e
    (derivedLowerShriekUpperShriekAdjunction f)
  exact ⟨forget.mapIso o, ((Endofunctor.IsoAlgebra.derivedStrIso _).hom.naturality o.hom.hom).symm⟩

end AlgebraicGeometry.WeilComplex
