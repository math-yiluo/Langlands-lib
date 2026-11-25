/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeOrientation
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedVerdierUnit

/-!
# The Weil orientation from the Tate encoding alone

`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_unitBaseChange` derives the
Weil orientation `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` of a smooth `f : X ⟶ Y` from the Tate encoding `α`
(A3) and the invertibility of the exceptional base change map at the unit along `k₀ ⟶ k̄₀` (A1').
The latter now holds for every `f`
(`ProEtale.CondensedRing.isIso_smoothUnitBaseChange_descendedShriekGeometricExchange`), so only
`α` remains (`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

local instance instFactPrimeRingChar_smoothPurityOrientationOfTateEncoding
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

local instance instLocallyOfFiniteType_weilSheafSmoothPurityOrientationOfTateEncoding
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityOrientationOfTateEncoding
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityOrientationOfTateEncoding
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityOrientationOfTateEncoding_2
    : LocallyOfFiniteType (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityOrientationOfTateEncoding_2
    : QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityOrientationOfTateEncoding_2
    : IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (Y ↘ Spec (CommRingCat.of k₀)))

variable (d : ℕ) [SmoothOfRelativeDimension d f] [HasUpperShriek k₀ l f]

/-- **The Weil orientation from the Tate encoding**: the statement of
`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`, from the Tate encoding `α` (A3)
alone, A1' being discharged by
`ProEtale.CondensedRing.isIso_smoothUnitBaseChange_descendedShriekGeometricExchange`. -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding
    (α : (ProEtaleWeilSheaf.toCondensed k₀ l X).obj
        (WeilSheaf.tateTwistSheaf k₀ l X d).obj ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj (ProEtale.tateTwist X l d)) :
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
  let e := (Functor.Monoidal.εIso (CondensedRing.boundedConstructibleUpperStarOfMap l
    (X := Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
    (Y := CondensedRing.geometricFiberOver (Over.mk (Y ↘ Spec (CommRingCat.of k₀))))
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)).symm
  have := CondensedRing.isIso_smoothUnitBaseChange_descendedShriekGeometricExchange l
    (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
      (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)) e.hom
  exact exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_unitBaseChange f d α e

end AlgebraicGeometry.WeilComplex
