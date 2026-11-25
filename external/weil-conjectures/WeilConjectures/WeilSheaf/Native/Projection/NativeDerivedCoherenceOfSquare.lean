/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.Functor.CurryComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.TensorSquareCompatibility
public import WeilConjectures.WeilSheaf.Native.Projection.TensorSquareCongr
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

import WeilConjectures.Tactic.ExactModProofs

/-! # Comparison compatibility from the derived tensor square -/

@[expose] public section

set_option Elab.async false

-- Use the coefficient-category instance fixed by the native tensor construction.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- Rotate the exact-derived tensor square and transport it to the left derived functor. -/
theorem projectionComparisonCompatible_of_square
    (htensor : ∀ M N : DerivedCategory (ProEtaleWeilSheaf k₀ l Y),
      DerivedPullTensorSquare k₀ l g M N) :
    Adjunction.ComparisonCompatible
      (T_C := Functor.curry.obj (nativeDerivedTensor k₀ l Z))
      (T_D := Functor.curry.obj (nativeDerivedTensor k₀ l Y))
      (T_C' := curriedTensor _) (T_D' := curriedTensor _)
      (derivedCondensedRealizationUpperStarIso k₀ l g)
      (Functor.curryCompIsoOfIso (nativePullTensor k₀ l g)).hom
      (ProEtale.CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (Functor.curryCompIsoOfIso' (condensedRealizationTensor k₀ l Z))
      (Functor.curryCompIsoOfIso' (condensedRealizationTensor k₀ l Y)) := by
  let R := ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
  have h := Adjunction.comparisonCompatible_of_tensorSquare_transport
    (nativeOpenPull k₀ l g) (derivedCondensedRealization k₀ l Z)
    (derivedCondensedRealization k₀ l Y) R.mapDerivedCategory R.leftDerivedFunctor
    (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
    (nativePullTensor k₀ l g) (condensedRealizationTensor k₀ l Y)
    (condensedRealizationTensor k₀ l Z)
    (Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g))
    R.leftDerivedFunctorIsoMapDerivedCategory
    (fun A B ↦ (R.mapDerivedCategoryTensorComparison.app A).app B)
    R.leftDerivedTensorComparison
    (R.mapDerivedCategoryTensorComparison_app_app)
    (by
      intro M N
      have ht := htensor M N
      dsimp only [DerivedPullTensorSquare] at ht
      have he := Functor.mapDerivedCategorySquareIso_symm
        (condensedRealizationUpperStarIso k₀ l g)
      have ht' := PullTensorSquareWithComparison.of_symm_eq he ht
      dsimp only [R]
      exact_mod_proofs ht')
  rw [ProEtale.CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]
  dsimp only [derivedCondensedRealizationUpperStarIso, Functor.leftDerivedFunctorSquareIso]
  dsimp only [R] at h
  exact_mod_proofs h

end AlgebraicGeometry.ProEtaleWeilSheaf
