/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityVerdierUnitIso
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedPointUnit

/-!
# Relative A1' for the descended exchange, by Verdier duality

Let `k` be a finite field with algebraic closure `k̄`, and `f : X ⟶ Y` a morphism of separated
`k`-schemes of finite type, with geometric fibre `f̄ : X̄ ⟶ Ȳ`. For the compact-support base change
isomorphism `descendedShriekGeometricExchange` of `f` along `k ⟶ k̄` (built from the chosen
compactification `X --j--> Z --p--> Y` of `f` and its geometric fibre), the exceptional base
change map at the unit `πX^* Rf^! ℚ̄_ℓ ⟶ Rf̄^! ℚ̄_ℓ` (`smoothUnitBaseChange`) is invertible
(`isIso_smoothUnitBaseChange_descendedShriekGeometricExchange`). No smoothness or properness of
`f` is needed, and `Y` is arbitrary: this is the relative form of
`isIso_smoothUnitBaseChange_descendedShriekGeometricExchange_point`.

## Proof

The open factor `j` has an invertible mate in general
(`isIso_smoothUnitBaseChange_fieldCompactification_of_proper`). For the proper factor
`p : Z ⟶ Y`, the base change map `πZ^* Rp^! ℚ̄_ℓ ⟶ Rp̄^! ℚ̄_ℓ` is invertible by the endomorphism
trick (`isIso_upperShriekBaseChangeOfMap_app_unit_of_iso`), fed with the isomorphism
`πZ^* Rp^! ℚ̄_ℓ ≅ Rp̄^! ℚ̄_ℓ` obtained by Verdier duality
(`upperShriekUnitIsoOfDualizingComplexIso`): biduality at the unit, the exceptional internal hom
exchange, the commutation of the weakly étale `πZ^*` with internal homs, and the point case of A1'
for `Z` and `Y` (`geometricFiberDualizingComplexIso`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- `geometricFiberDualizingComplexIso` for any structure morphism of the geometric fibre equal
to the canonical one. -/
def geometricFiberDualizingComplexIsoOfHomEq (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {b : X.hom.geometricFiber ⟶ Spec (.of (AlgebraicClosure k))}
    (h : X.hom.geometricFiberToAlgebraicClosure = b) [LocallyOfFiniteType (Over.mk b).hom]
    [QuasiCompact (Over.mk b).hom] [IsSeparated (Over.mk b).hom] :
    (boundedConstructibleUpperStarOfMap l (X := X) (Y := Over.mk b)
        X.hom.geometricFiberProj).obj (dualizingComplex l X) ≅
      dualizingComplex l (Over.mk b) := by
  subst h
  exact geometricFiberDualizingComplexIso l X

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

local instance instFactPrimeRingCharAlgebraicClosure_smoothPurityDescendedVerdierUnit
    : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩
local instance instFactNeNatRingCharAlgebraicClosure_smoothPurityDescendedVerdierUnit
    : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := l)⟩
local instance instLocallyOfFiniteType_smoothPurityDescendedVerdierUnit
    : LocallyOfFiniteType (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance instQuasiCompactHomScheme_smoothPurityDescendedVerdierUnit
    : QuasiCompact (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance instIsSeparatedHomScheme_smoothPurityDescendedVerdierUnit
    : IsSeparated (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))

omit [Finite k] [Fact (ringChar k).Prime] [LocallyOfFiniteType Y.hom] in
/-- The structure morphism of the geometric fibre of the chosen compactification of `f`. -/
lemma geometricFiberToAlgebraicClosure_compactificationOverField_overObj :
    (compactificationOverField f).overObj.hom.geometricFiberToAlgebraicClosure =
      (((compactificationOverField f).geometricFiber (Over.w f)).overObj
        (f := traceGeometricFiberOverMap f)).hom :=
  (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure (g := Y.hom)
    (compactificationOverField f).g rfl).symm

/-- The dualizing complex of the compactification `Z` of `f` commutes with the change of the base
field `k ⟶ k̄`, `πZ^* ω_Z ≅ ω_Z̄`, for the geometric fibre `Z̄` of the compactification. -/
def compactificationOverFieldDualizingComplexIso :
    (boundedConstructibleUpperStarOfMap l (X := (compactificationOverField f).overObj)
        (Y := ((compactificationOverField f).geometricFiber (Over.w f)).overObj
          (f := traceGeometricFiberOverMap f))
        (compactificationOverField f).overObj.hom.geometricFiberProj).obj
        (dualizingComplex l (compactificationOverField f).overObj) ≅
      dualizingComplex l (((compactificationOverField f).geometricFiber (Over.w f)).overObj
        (f := traceGeometricFiberOverMap f)) :=
  haveI : LocallyOfFiniteType (Over.mk (((compactificationOverField f).geometricFiber
      (Over.w f)).overObj (f := traceGeometricFiberOverMap f)).hom).hom :=
    inferInstanceAs (LocallyOfFiniteType (((compactificationOverField f).geometricFiber
      (Over.w f)).overObj (f := traceGeometricFiberOverMap f)).hom)
  haveI : QuasiCompact (Over.mk (((compactificationOverField f).geometricFiber
      (Over.w f)).overObj (f := traceGeometricFiberOverMap f)).hom).hom :=
    inferInstanceAs (QuasiCompact (((compactificationOverField f).geometricFiber
      (Over.w f)).overObj (f := traceGeometricFiberOverMap f)).hom)
  haveI : IsSeparated (Over.mk (((compactificationOverField f).geometricFiber
      (Over.w f)).overObj (f := traceGeometricFiberOverMap f)).hom).hom :=
    inferInstanceAs (IsSeparated (((compactificationOverField f).geometricFiber
      (Over.w f)).overObj (f := traceGeometricFiberOverMap f)).hom)
  geometricFiberDualizingComplexIsoOfHomEq l (compactificationOverField f).overObj
    (geometricFiberToAlgebraicClosure_compactificationOverField_overObj f)

/-- **The proper factor**: for the proper morphism `p : Z ⟶ Y` of the chosen compactification of
`f` and its geometric fibre `p̄`, the base change map `πZ^* Rp^! ℚ̄_ℓ ⟶ Rp̄^! πY^* ℚ̄_ℓ` at the
unit is invertible, by the endomorphism trick applied to the Verdier duality isomorphism. -/
theorem isIso_upperShriekBaseChangeOfMap_app_unit_compactificationOverField :
    IsIso ((upperShriekBaseChangeOfMap l
      (f := (compactificationOverField f).overG (f := f))
      (f' := ((compactificationOverField f).geometricFiber (Over.w f)).overG
        (f := traceGeometricFiberOverMap f))
      (Scheme.Hom.isPullback_geometricFiberMap (g := Y.hom)
        (compactificationOverField f).g rfl).flip).app (𝟙_ _)) :=
  isIso_upperShriekBaseChangeOfMap_app_unit_of_iso l _
    (upperShriekUnitIsoOfDualizingComplexIso l
      ((compactificationOverField f).overG (f := f))
      (((compactificationOverField f).geometricFiber (Over.w f)).overG
        (f := traceGeometricFiberOverMap f))
      (Scheme.Hom.isPullback_geometricFiberMap (g := Y.hom)
        (compactificationOverField f).g rfl).flip.w
      (compactificationOverFieldDualizingComplexIso l f)
      (geometricFiberDualizingComplexIso l Y))

/-- **Relative A1'.** For a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type (`k`
finite), the exceptional base change map at the unit `πX^* Rf^! ℚ̄_ℓ ⟶ Rf̄^! ℚ̄_ℓ` of the
descended exchange `descendedShriekGeometricExchange` is invertible, for any isomorphism
`e : πY^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`. -/
theorem isIso_smoothUnitBaseChange_descendedShriekGeometricExchange
    (e : (boundedConstructibleUpperStarOfMap l (X := Y)
      (Y := geometricFiberOver Y) Y.hom.geometricFiberProj).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l f (traceGeometricFiberOverMap f)
      (descendedShriekGeometricExchange l f) e) := by
  have := isIso_upperShriekBaseChangeOfMap_app_unit_compactificationOverField l f
  dsimp only [descendedShriekGeometricExchange]
  exact isIso_smoothUnitBaseChange_fieldCompactification_of_proper l f
    (traceGeometricFiberOverMap f)
    (compactificationOverField f) ((compactificationOverField f).geometricFiber (Over.w f))
    (Scheme.Hom.isPullback_geometricFiberMap (compactificationOverField f).i
      ((compactificationOverField f).i_comp_g_comp (Over.w f)))
    (Scheme.Hom.isPullback_geometricFiberMap (g := Y.hom)
      (compactificationOverField f).g rfl).flip e

end AlgebraicGeometry.ProEtale.CondensedRing
