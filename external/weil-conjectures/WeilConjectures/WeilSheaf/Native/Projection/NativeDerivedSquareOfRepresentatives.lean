/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.OrdinaryTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.TensorSquare
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
import WeilConjectures.WeilSheaf.Native.Projection.StrictProof
import WeilConjectures.Tactic.ExactModProofs

/-! # Extending the native tensor square from K-flat representatives -/

@[expose] public noncomputable section

set_option Elab.async false
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

variable (hQ : ∀ (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ),
  NativeIsKFlat k₀ l Y P → NativeIsKFlat k₀ l Y T →
    DerivedPullTensorSquare k₀ l g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T))

include hQ in
/-- The native pullback tensor square on arbitrary derived objects, extended from K-flat
representatives by naturality. -/
lemma projection_derived_square_of_representatives
    (M N : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :
    DerivedPullTensorSquare k₀ l g M N := by
  projection_strict
    unfold DerivedPullTensorSquare PullTensorSquareWithComparison
    simp only [Iso.symm_inv]
    let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
    let c : Functor.uncurry.obj (curriedTensor _) ⋙ R.mapDerivedCategory ≅
        R.mapDerivedCategory.prod R.mapDerivedCategory ⋙
          Functor.uncurry.obj (curriedTensor _) :=
      NatIso.ofComponents
        (fun MN ↦ asIso ((R.mapDerivedCategoryTensorComparison.app MN.1).app MN.2))
        (fun fg ↦ by
          simpa only [asIso_hom, Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
            curriedTensor_map_app, curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def] using
            R.projection_mapDerivedCategoryTensorComparison_naturality fg.1 fg.2)
    have h := Adjunction.tensorSquare_of_representatives DerivedCategory.Q.obj
      (NativeIsKFlat k₀ l Y) (native_two_sided_kflat_representatives k₀ l Y)
      (nativeOpenPull k₀ l g) (derivedCondensedRealization k₀ l Z)
      (derivedCondensedRealization k₀ l Y) R.mapDerivedCategory
      (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
      (Functor.uncurry.obj (curriedTensor _)) (Functor.uncurry.obj (curriedTensor _))
      (nativePullTensor k₀ l g) (condensedRealizationTensor k₀ l Z)
      (condensedRealizationTensor k₀ l Y)
      (Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g).symm) c
      (fun P T hP hT ↦ by
        have hQ := hQ P T hP hT
        dsimp only [DerivedPullTensorSquare, PullTensorSquareWithComparison] at hQ
        simp only [Iso.symm_inv] at hQ
        simp only [c, NatIso.ofComponents_hom_app, asIso_hom,
          Functor.uncurry_obj_map, curriedTensor_map_app,
          curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def]
        dsimp only [R]
        exact_mod_proofs hQ) M N
    simp only [c, NatIso.ofComponents_hom_app, asIso_hom,
      Functor.uncurry_obj_map, curriedTensor_map_app,
      curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def] at h
    dsimp only [R] at h
    exact_mod_proofs h

end AlgebraicGeometry.ProEtaleWeilSheaf
