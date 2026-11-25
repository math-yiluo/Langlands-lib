/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.AdicSheafTensorSquare
public import WeilConjectures.WeilSheaf.Native.Projection.NativeSheafSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.SheafSquareTransport
public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
import WeilConjectures.Tactic.ExactModProofs

/-! # The native sheaf tensor square under condensed realization -/

@[expose] public section

set_option Elab.async false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

lemma condensedRealizationSheafTensorIso_inv_eq (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (M N : ProEtaleWeilSheaf k₀ l X) :
    (condensedRealizationSheafTensorIso k₀ l X).inv.app (M, N) =
      (condensedRelativeTensorIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        M.carrier N.carrier).inv := by
  rw [condensedRealizationSheafTensorIso_inv_app]
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
lemma condensedRealizationUpperStarIso_hom_app_eq (M : ProEtaleWeilSheaf k₀ l Y) :
    (condensedRealizationUpperStarIso k₀ l g).hom.app M =
      (adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv.app
          M.carrier := by
  dsimp only [condensedRealizationUpperStarIso]
  exact_mod_proofs Endofunctor.IsoAlgebra.isoHComp_forget_symm_inv_hom_app
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l g
      (comp_over g (Spec (CommRingCat.of k₀))))
    (adicUpperStarCompCondensedModIso l
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))) M

omit [Fact (ringChar k₀ ≠ l)] in
lemma condensedRealizationUpperStarIso_hom_eq :
    (condensedRealizationUpperStarIso k₀ l g).hom =
      Functor.whiskerLeft (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
        (adicUpperStarCompCondensedModIso l
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv := by
  dsimp only [condensedRealizationUpperStarIso]
  exact_mod_proofs Endofunctor.IsoAlgebra.isoHComp_forget_symm_inv_hom
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l g
      (comp_over g (Spec (CommRingCat.of k₀))))
    (adicUpperStarCompCondensedModIso l
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))

/-- The carrier formula with homogeneous source and target. -/
lemma projection_nativePullSheafTensor_carrier_eq (M N : ProEtaleWeilSheaf k₀ l Y) :
    (((nativePullSheafTensor k₀ l g).hom.app (M, N)).hom.f) =
      (adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
          N.carrier).hom.app M.carrier := by
  exact eq_of_heq (nativePullSheafTensor_hom_app_hom_f k₀ l g M N)

/-- The native tensor has the relative tensor as carrier. -/
lemma projection_nativeOpenSheafTensor_obj_carrier (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (M N : ProEtaleWeilSheaf k₀ l X) :
    ((nativeOpenSheafTensor k₀ l X).obj (M, N)).carrier =
      (Mod.tensorLeft N.carrier).obj M.carrier := rfl

/-- Pullback comparison on the carrier of a native tensor. -/
lemma projection_upperStar_tensor_carrier (M N : ProEtaleWeilSheaf k₀ l Y) :
    (condensedRealizationUpperStarIso k₀ l g).hom.app
        ((nativeOpenSheafTensor k₀ l Y).obj (M, N)) =
      (adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv.app
          ((Mod.tensorLeft N.carrier).obj M.carrier) := by
  have h := condensedRealizationUpperStarIso_hom_app_eq k₀ l g
    ((nativeOpenSheafTensor k₀ l Y).obj (M, N))
  simp only [projection_nativeOpenSheafTensor_obj_carrier] at h
  cast_proofs h

/-- Realization of the native pullback tensor map. -/
lemma projection_realization_pull_tensor (M N : ProEtaleWeilSheaf k₀ l Y) :
    (condensedRealization k₀ l Z).map ((nativePullSheafTensor k₀ l g).hom.app (M, N)) =
      (adicSheafEquivCondensedMod l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.map
        ((adicUpperStarTensorLeftIso l
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
            N.carrier).hom.app M.carrier) := by
  dsimp only [condensedRealization, Functor.comp_map, Endofunctor.IsoAlgebra.forget_map]
  cast_proofs (adicSheafEquivCondensedMod l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.congr_map
      (projection_nativePullSheafTensor_carrier_eq k₀ l g M N)

omit [Fact (ringChar k₀ ≠ l)] in
/-- Tensoring the two carrier pullback comparisons. -/
lemma projection_upperStar_tensor_hom (M N : ProEtaleWeilSheaf k₀ l Y) :
    (condensedRealizationUpperStarIso k₀ l g).hom.app M ⊗ₘ
        (condensedRealizationUpperStarIso k₀ l g).hom.app N =
      (adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv.app
          M.carrier ⊗ₘ
      (adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv.app
          N.carrier := by
  cast_proofs congrArg₂ (fun p q ↦ p ⊗ₘ q)
    (condensedRealizationUpperStarIso_hom_app_eq k₀ l g M)
    (condensedRealizationUpperStarIso_hom_app_eq k₀ l g N)

/-- Realization of the tensor of two native pullbacks. -/
lemma projection_realization_pulled_tensor (M N : ProEtaleWeilSheaf k₀ l Y) :
    (condensedRealizationSheafTensorIso k₀ l Z).inv.app
        ((upperStar k₀ l g).obj M, (upperStar k₀ l g).obj N) =
      (condensedRelativeTensorIso l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
        ((adicUpperStar l (Scheme.Hom.geometricFiberMap g
          (comp_over g (Spec (CommRingCat.of k₀))))).obj M.carrier)
        ((adicUpperStar l (Scheme.Hom.geometricFiberMap g
          (comp_over g (Spec (CommRingCat.of k₀))))).obj N.carrier)).inv := by
  have h := condensedRealizationSheafTensorIso_inv_eq k₀ l Z
    ((upperStar k₀ l g).obj M) ((upperStar k₀ l g).obj N)
  simp only [upperStar, Endofunctor.IsoAlgebra.mapOfNatIso_obj_carrier] at h
  cast_proofs h

/-- Transport along an arbitrary Frobenius-compatible functor on the geometric fibres.
The fibre map and the Frobenius comparison remain parameters throughout the calculation. -/
lemma projection_inverse_square_of_frobenius
    (f : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (e : adicUpperStar l f ⋙ WeilSheaf.frobeniusPullback k₀ l Z ≅
      WeilSheaf.frobeniusPullback k₀ l Y ⋙ adicUpperStar l f)
    (mu : nativeOpenSheafTensor k₀ l Y ⋙ Endofunctor.IsoAlgebra.mapOfNatIso e ≅
      (Endofunctor.IsoAlgebra.mapOfNatIso e).prod (Endofunctor.IsoAlgebra.mapOfNatIso e) ⋙
        nativeOpenSheafTensor k₀ l Z)
    (hmu : ∀ M N, ((mu.hom.app (M, N)).hom.f) =
      (adicUpperStarTensorLeftIso l f N.carrier).hom.app M.carrier)
    (M N : ProEtaleWeilSheaf k₀ l Y) :
    PullTensorInverseSquare (Endofunctor.IsoAlgebra.mapOfNatIso e)
      (condensedRealization k₀ l Z) (condensedRealization k₀ l Y)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
      (nativeOpenSheafTensor k₀ l Y) (nativeOpenSheafTensor k₀ l Z) mu
      (condensedRealizationSheafTensorIso k₀ l Y) (condensedRealizationSheafTensorIso k₀ l Z)
      (Functor.isoHComp (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso e).symm
        (adicUpperStarCompCondensedModIso l f).symm) M N := by
  unfold PullTensorInverseSquare
  rw [condensedRealizationSheafTensorIso_inv_eq, condensedRealizationSheafTensorIso_inv_eq]
  simp only [Endofunctor.IsoAlgebra.isoHComp_forget_symm_inv_hom_app,
    condensedRealization, Functor.comp_map, Functor.comp_obj,
    Endofunctor.IsoAlgebra.forget_obj, Endofunctor.IsoAlgebra.forget_map,
    Endofunctor.IsoAlgebra.mapOfNatIso_obj_carrier,
    projection_nativeOpenSheafTensor_obj_carrier]
  rw [hmu]
  cast_proofs adicUpperStar_condensedRelativeTensor_square l f M.carrier N.carrier

end AlgebraicGeometry.ProEtaleWeilSheaf
