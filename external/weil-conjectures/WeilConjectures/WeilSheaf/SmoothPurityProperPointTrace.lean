/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedProperUniversality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-!
# Proper dualizing trace over the geometric fibre of a point

The exceptional base-change map at the unit is invertible without smoothness.
This applies to the proper scheme in an arbitrary compactification.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (f : X ⟶ point k) [IsProper f.left]

local instance instFactPrimeRingCharAlgebraicClosure_smoothPurityProperPointTrace
    : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩
local instance instFactNeNatRingCharAlgebraicClosure_smoothPurityProperPointTrace
    : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := l)⟩
local instance instLocallyOfFiniteType_smoothPurityProperPointTrace
    : LocallyOfFiniteType (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance instQuasiCompactHomScheme_smoothPurityProperPointTrace
    : QuasiCompact (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance instIsSeparatedHomScheme_smoothPurityProperPointTrace
    : IsSeparated (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance : LocallyOfFiniteType
    (Over.mk (point k).hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance : QuasiCompact (Over.mk (point k).hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance : IsSeparated (Over.mk (point k).hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance : IsProper (traceGeometricFiberOverMap f).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
    f.left (Over.w f) inferInstance

omit [Finite k] in
/-- Exceptional base change of a proper structural map at the unit is invertible
for the actual geometric-fibre square. -/
theorem isIso_upperShriekBaseChange_geometricFiber_unit :
    IsIso ((upperShriekBaseChangeOfMap l (f := f) (f' := traceGeometricFiberOverMap f)
      (Scheme.Hom.isPullback_geometricFiberMap f.left (Over.w f)).flip).app (𝟙_ _)) := by
  exact isIso_upperShriekBaseChangeOfMap_app_unit_point l
    (K₀ := k) (L := AlgebraicClosure k) (f := f) (f' := traceGeometricFiberOverMap f)
    (IsPullback.of_hasPullback _ _)
    (Scheme.Hom.isPullback_geometricFiberMap f.left (Over.w f)).flip

end AlgebraicGeometry.ProEtale.CondensedRing
