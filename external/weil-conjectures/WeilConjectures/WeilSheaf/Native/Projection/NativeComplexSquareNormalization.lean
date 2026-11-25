/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromModels
public import WeilConjectures.WeilSheaf.Native.Projection.TensorSquareCongr
public import WeilConjectures.WeilSheaf.Native.Projection.NativeModelFamilyNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances

/-! # Comparing the native and model total-complex squares -/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing
universe u
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf
open ProEtale
attribute [local instance] projection_hasSmallColimits projection_hasTensor
  projection_nativeHasTotal projection_tensorLeftPreservesInitial
  projection_tensorRightPreservesInitial projection_hasGoodTensor12
  projection_hasGoodTensor23 projection_hasTensor4Ext

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

variable (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))] in
/-- Compare the whole complex square before taking its components. -/
lemma projection_model_complex_square_eq_native :
    projection_model_complex_square (upperStar k₀ l g)
      (condensedRealization k₀ l Z) (condensedRealization k₀ l Y)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (condensedRealizationUpperStarIso k₀ l g).symm =
        condensedRealizationPullComplexIso k₀ l g := by
  rfl

omit [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))] in
/-- Transport the total square at the level of its comparison isomorphism. -/
lemma projection_total_square_in_model_form
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (h : TotalPullTensorSquare k₀ l g P T) :
    PullTensorSquareWithComparison
      ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ))
          ((condensedRealization k₀ l Z).mapHomologicalComplex (.up ℤ))
      ((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ))
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).mapHomologicalComplex (.up ℤ))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) (nativePullTotalTensor k₀ l g)
          (condensedRealizationTotalTensorIso k₀ l Y) (condensedRealizationTotalTensorIso k₀ l Z)
      (projection_model_complex_square (upperStar k₀ l g) (condensedRealization k₀ l Z)
          (condensedRealization k₀ l Y) (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
            (condensedRealizationUpperStarIso k₀ l g).symm).symm
      (fun X Y ↦ ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).mapCochainComplexμIso X Y).inv) P T := by
  exact PullTensorSquareWithComparison.of_symm_eq
    (projection_model_complex_square_eq_native k₀ l g).symm h

end AlgebraicGeometry.ProEtaleWeilSheaf
