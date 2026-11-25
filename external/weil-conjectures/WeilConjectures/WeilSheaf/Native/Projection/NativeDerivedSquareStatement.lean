/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.WeilSheaf.Native.Projection.SheafSquareTransport
public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

/-! # Localization of the native pullback tensor square -/

@[expose] public noncomputable section

-- Use the coefficient-category instance fixed by the native tensor construction.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The derived pullback tensor square, using the exact-derived tensor comparison. -/
def DerivedPullTensorSquare
    (M N : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) : Prop :=
  let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
  PullTensorSquareWithComparison (nativeOpenPull k₀ l g) (derivedCondensedRealization k₀ l Z)
    (derivedCondensedRealization k₀ l Y) R.mapDerivedCategory
    (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
    (nativePullTensor k₀ l g) (condensedRealizationTensor k₀ l Y)
    (condensedRealizationTensor k₀ l Z)
    (Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g).symm).symm
    (fun A B ↦ (R.mapDerivedCategoryTensorComparison.app A).app B) M N

end AlgebraicGeometry.ProEtaleWeilSheaf
