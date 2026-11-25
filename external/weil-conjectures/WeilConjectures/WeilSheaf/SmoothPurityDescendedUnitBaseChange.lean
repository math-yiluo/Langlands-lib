/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldShriekTraceUniversality
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedShriekUniversality

/-! # Unit base change implies universality of the descended Weil smooth trace -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

local instance instFactPrimeRingCharAlgebraicClosure_smoothPurityDescendedUnitBaseChange
    : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩
local instance instFactNeNatRingCharAlgebraicClosure_smoothPurityDescendedUnitBaseChange
    : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := l)⟩

local instance instLocallyOfFiniteType_weilSheafSmoothPurityDescendedUnitBaseChange
    : LocallyOfFiniteType (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityDescendedUnitBaseChange
    : QuasiCompact (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityDescendedUnitBaseChange
    : IsSeparated (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityDescendedUnitBaseChange_2
    : LocallyOfFiniteType (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityDescendedUnitBaseChange_2
    : QuasiCompact (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityDescendedUnitBaseChange_2
    : IsSeparated (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))

/-- The bounded exchange obtained from the geometric fiber of the chosen compactification. -/
noncomputable def descendedShriekGeometricExchange :
    boundedConstructibleLowerShriek l f ⋙
        boundedConstructibleUpperStarOfMap l Y.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (traceGeometricFiberOverMap f) :=
  purityFieldLowerShriekExchange l f (traceGeometricFiberOverMap f)
    (compactificationOverField f) ((compactificationOverField f).geometricFiber (Over.w f))
    (Scheme.Hom.isPullback_geometricFiberMap (compactificationOverField f).i
      ((compactificationOverField f).i_comp_g_comp (Over.w f)))
    (Scheme.Hom.isPullback_geometricFiberMap (compactificationOverField f).g rfl).flip

/-- The actual descended smooth trace is universal in the Weil category if its
unit base-change component is invertible. This is the non-proper shriek bridge. -/
theorem geometricFiberWeilSmoothTrace_weilUniversal_of_unitBaseChange
    (e : (boundedConstructibleUpperStarOfMap l (X := Y)
      (Y := Over.mk Y.hom.geometricFiberToAlgebraicClosure)
      Y.hom.geometricFiberProj).obj (𝟙_ _) ≅ 𝟙_ _)
    [hbc : IsIso (smoothUnitBaseChange l f (traceGeometricFiberOverMap f)
      (πX := X.hom.geometricFiberProj) (πY := Y.hom.geometricFiberProj)
      (descendedShriekGeometricExchange l f) e.hom)]
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (K : DerivedCategory (Endofunctor.IsoAlgebra
      (lowerStar (Profinite.padicAlgClRingObj l) X.hom.geometricGaloisFrobenius.asIso.inv)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      X.hom.geometricFiber) ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj K)) :
    (weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj l)
      (compactificationOverField f) (Over.w f)).TraceUniversalAt K
        (geometricFiberWeilSmoothTrace l f d) := by
  dsimp only [descendedShriekGeometricExchange] at hbc
  apply geometricFiberWeilSmoothTrace_weilUniversal l f d K hK
  intro Q
  have he := baseChangedSmoothTrace_levelwise_universal l f (traceGeometricFiberOverMap f)
    ((compactificationOverField f).geometricFiber (Over.w f))
    (Scheme.Hom.isPullback_geometricFiberMap (compactificationOverField f).i
      ((compactificationOverField f).i_comp_g_comp (Over.w f)))
    (Scheme.Hom.isPullback_geometricFiberMap (compactificationOverField f).g rfl).flip e d Q
  exact he

end AlgebraicGeometry.ProEtale.CondensedRing
