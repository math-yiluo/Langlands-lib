/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeDescent
public import WeilConjectures.WeilSheaf.CondensedModelCompactSupport
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.SmoothPurity.TateTwistBoundedConstructible

/-!
# Native descent of a shifted sheaf

A comparison of the underived Weil sheaves induces the comparison of their
shifted complexes. In particular, the Tate encoding can be supplied entirely at
the sheaf level.
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
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Twisting the constant complex gives the Tate sheaf placed in degree zero. -/
noncomputable def tateTwistConstantSingleIso (d : ℤ) :
    (tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l X d) :=
  ObjectProperty.isoMk _
    ((tateTwistCompιIso (k₀ := k₀) (l := l) (X := X) d).app _ ≪≫
      ((ProEtaleWeilSheaf.constantTwist k₀ l X
        (WeilSheaf.cyclotomicUnit k₀ l ^ d)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (WeilSheaf.tateTwistSheafObjIso k₀ l X d).symm)

/-- A sheaf-level descent comparison identifies native descent of any specified
shift of that sheaf. -/
noncomputable def finiteBaseNativeDescentShiftedSheafIso
    (P : Dᵇc(X)⟦Profinite.padicAlgClRingObj l⟧) (G : WeilSheaf k₀ l X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (α : (ProEtaleWeilSheaf.toCondensed k₀ l X).obj G.obj ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj M)
    (n : ℤ) (e : P.obj ≅ ((DerivedCategory.singleFunctor _ 0).obj M) ⟦n⟧) :
    (finiteBaseNativeDescent (k₀ := k₀) (X := X)).obj P ≅ (WeilSheaf.toComplex.obj G) ⟦n⟧ :=
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.preimageIso
      ((finiteBaseNativeDescentComparison (k₀ := k₀)).app P ≪≫
        (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.mapIso e ≪≫
        ((CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.commShiftIso n).app _ ≪≫
        (shiftFunctor _ n).mapIso (derivedEquivCondensedSingleIso G M α).symm ≪≫
        (((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.commShiftIso n).app
          (WeilSheaf.toComplex.obj G).obj).symm ≪≫
        (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.mapIso
          (((objectProperty k₀ l X).ι.commShiftIso n).app
            (WeilSheaf.toComplex.obj G)).symm))

local instance instFactPrimeRingChar_smoothPurityDescentSingle
    : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩
local instance instLocallyOfFiniteType_smoothPurityDescentSingle
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_smoothPurityDescentSingle
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_smoothPurityDescentSingle
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))

/-- The sheaf-level cyclotomic comparison gives the shifted Tate comparison
needed by absolute purity. -/
noncomputable def finiteBaseNativeDescentTateIso (d n : ℤ)
    (α : (ProEtaleWeilSheaf.toCondensed k₀ l X).obj
        (WeilSheaf.tateTwistSheaf k₀ l X d).obj ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj (ProEtale.tateTwist X l d)) :
    (finiteBaseNativeDescent (k₀ := k₀) (X := X)).obj
        (CondensedRing.boundedConstructibleTateTwist l
          (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d n) ≅
      (WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l X d)) ⟦n⟧ :=
  finiteBaseNativeDescentShiftedSheafIso (X := X) _ _ _ α n (Iso.refl _)

end AlgebraicGeometry.WeilComplex
