/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.SheafTensorUnit
import all WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationSheafTensor

/-! # Pullback and the relative tensor comparison of the condensed model -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The condensed model of the coequalizer tensor. -/
noncomputable def condensedRelativeTensorIso (X : Scheme.{u}) (M N : AdicSheaf l X) :
    (adicSheafEquivCondensedMod l X).functor.obj ((Mod.tensorLeft N).obj M) ≅
      (adicSheafEquivCondensedMod l X).functor.obj M ⊗
        (adicSheafEquivCondensedMod l X).functor.obj N :=
  (adicSheafEquivCondensedMod l X).functor.mapIso ((Mod.relativeTensorRightIso N).app M) ≪≫
    (adicSheafEquivCondensedModTensorIso l X M N).symm

@[reassoc]
lemma tensorObjπ_condensedRelativeTensorIso_inv_hom (X : Scheme.{u}) (M N : AdicSheaf l X) :
    Mod.tensorObjπ ((adicSheafEquivCondensedMod l X).functor.obj M)
        ((adicSheafEquivCondensedMod l X).functor.obj N) ≫
      (condensedRelativeTensorIso l X M N).inv.hom =
    μ (weilCoefficientsForgetAb l X) M.X N.X ≫
      (weilCoefficientsForgetAb l X).map (Mod.tensorπ M N) := by
  have h : Mod.tensorObjπ M N ≫ ((Mod.relativeTensorRightIso N).inv.app M).hom =
      Mod.tensorπ M N := by
    rw [← ProEtaleWeilSheaf.tensorπ_relativeTensorRightIso_hom_app, Category.assoc,
      ← Mod.comp_hom', Iso.hom_inv_id_app, Mod.id_hom', Category.comp_id]
  change Mod.tensorObjπ _ _ ≫
    ((adicSheafEquivCondensedModTensorIso l X M N).hom ≫
      (adicSheafEquivCondensedMod l X).functor.map
        ((Mod.relativeTensorRightIso N).inv.app M)).hom = _
  rw [Mod.comp_hom', tensorObjπ_adicSheafEquivCondensedModTensorIso_hom_hom_assoc]
  rw [← h, Functor.map_comp]
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unit equation for the pullback comparison, on underlying abelian sheaves. -/
@[reassoc]
lemma adicUpperStarCompCondensedModIso_unit_hom (M : AdicSheaf l Y) :
    ((CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f).unit.app
        ((adicSheafEquivCondensedMod l Y).functor.obj M)).hom ≫
      (lowerStar Ab.{u + 1} f).map
        (((adicUpperStarCompCondensedModIso l f).inv.app M).hom) =
    (weilCoefficientsForgetAb l Y).map
      (((adicUpperStarLowerStarAdjunction l f).unit.app M).hom) := by
  have h := unit_mateEquiv (adicUpperStarLowerStarAdjunction l f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
    (adicUpperStarCompCondensedModIso l f).inv M
  have hb := congrArg (fun t ↦ t.app ((adicUpperStar l f).obj M))
    (mateEquiv_adicUpperStarCompCondensedModIso_inv_eq_hom (l := l) f)
  rw [hb] at h
  dsimp only [Functor.id_obj] at h
  have hh := congrArg Mod.Hom.hom h
  rw [Mod.comp_hom', Mod.comp_hom', adicLowerStarCompCondensedModIso_hom_app_hom,
    CondensedRing.lowerStar_map_hom] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

/-- The adjoint of a map transported through the pullback comparison. -/
lemma homEquiv_adicUpperStarCompCondensedModIso_inv_comp
    (M : AdicSheaf l Y) (N : AdicSheaf l X) (t : (adicUpperStar l f).obj M ⟶ N) :
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f).homEquiv _ _
      ((adicUpperStarCompCondensedModIso l f).inv.app M ≫
        (adicSheafEquivCondensedMod l X).functor.map t) =
    (adicSheafEquivCondensedMod l Y).functor.map
        ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _ t) ≫
      (adicLowerStarCompCondensedModIso l f).hom.app N := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_mateEquiv (adicUpperStarLowerStarAdjunction l f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
    (adicUpperStarCompCondensedModIso l f).inv M
  have hb := congrArg (fun s ↦ s.app ((adicUpperStar l f).obj M))
    (mateEquiv_adicUpperStarCompCondensedModIso_inv_eq_hom (l := l) f)
  rw [hb] at hu
  dsimp only [Functor.id_obj] at hu
  have hn := (adicLowerStarCompCondensedModIso l f).hom.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hu, Category.assoc, ← hn]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

/-- Forgetting coefficients commutes with the lax tensor map of pushforward. -/
@[reassoc]
lemma lowerStarForgetAb_tensor (M N : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    μ (weilCoefficientsForgetAb l Y) ((lowerStar (WeilCoefficients.{u} l) f).obj M)
        ((lowerStar (WeilCoefficients.{u} l) f).obj N) ≫
      (weilCoefficientsForgetAb l Y).map (μ (lowerStar (WeilCoefficients.{u} l) f) M N) =
    μ (lowerStar Ab.{u + 1} f) ((weilCoefficientsForgetAb l X).obj M)
        ((weilCoefficientsForgetAb l X).obj N) ≫
      (lowerStar Ab.{u + 1} f).map (μ (weilCoefficientsForgetAb l X) M N) := by
  have h := NatTrans.IsMonoidal.tensor (τ := (lowerStarForgetAbIso l f).hom) M N
  rw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ] at h
  simp only [lowerStarForgetAbIso, Functor.sheafPushforwardContinuousCompSheafComposeIso,
    Iso.refl_hom, NatTrans.id_app] at h
  erw [Category.comp_id, id_tensorHom_id, Category.id_comp] at h
  exact h

/-- The tensor comparisons commute with the pullback comparison of the two coefficient
models. We compare adjoints on the quotient's pure-tensor generators. -/
lemma adicUpperStar_condensedRelativeTensor_square (M N : AdicSheaf l Y) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
        (condensedRelativeTensorIso l Y M N).inv ≫
      (adicUpperStarCompCondensedModIso l f).inv.app ((Mod.tensorLeft N).obj M) ≫
      (adicSheafEquivCondensedMod l X).functor.map
        ((adicUpperStarTensorLeftIso l f N).hom.app M) =
    δ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
        ((adicSheafEquivCondensedMod l Y).functor.obj M)
        ((adicSheafEquivCondensedMod l Y).functor.obj N) ≫
      ((adicUpperStarCompCondensedModIso l f).inv.app M ⊗ₘ
        (adicUpperStarCompCondensedModIso l f).inv.app N) ≫
      (condensedRelativeTensorIso l X ((adicUpperStar l f).obj M)
        ((adicUpperStar l f).obj N)).inv := by
  apply ((CondensedRing.upperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj l) f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, homEquiv_adicUpperStarCompCondensedModIso_inv_comp,
    Adjunction.homEquiv_naturality_right]
  apply Mod.hom_ext
  apply (cancel_epi (Mod.tensorObjπ ((adicSheafEquivCondensedMod l Y).functor.obj M)
    ((adicSheafEquivCondensedMod l Y).functor.obj N))).1
  simp only [Functor.map_comp, Mod.comp_hom',
    adicLowerStarCompCondensedModIso_hom_app_hom,
    CondensedRing.lowerStar_map_hom]
  rw [tensorObjπ_condensedRelativeTensorIso_inv_hom_assoc]
  change μ (weilCoefficientsForgetAb l Y) M.X N.X ≫
    (weilCoefficientsForgetAb l Y).map (Mod.tensorπ M N) ≫
      (weilCoefficientsForgetAb l Y).map
        (((adicUpperStarLowerStarAdjunction l f).homEquiv _ _
          ((adicUpperStarTensorLeftIso l f N).hom.app M)).hom) = _
  rw [← Functor.map_comp, tensorπ_homEquiv_adicUpperStarTensorLeftIso,
    Functor.map_comp, Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc]
  simp only [Functor.comp_obj, adicUpperStar_obj_X]
  rw [lowerStarForgetAb_tensor_assoc]
  rw [CondensedRing.tensorObjπ_homEquiv_δ_assoc]
  conv_rhs =>
    rw [← Functor.map_comp, ← Functor.map_comp, Mod.tensorObjπ_tensorHom_hom_assoc,
      tensorObjπ_condensedRelativeTensorIso_inv_hom, Functor.map_comp, Functor.map_comp,
      ← Functor.LaxMonoidal.μ_natural_assoc, tensorHom_comp_tensorHom_assoc,
      adicUpperStarCompCondensedModIso_unit_hom, adicUpperStarCompCondensedModIso_unit_hom]
  simp only [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_unit_app_hom]
  rfl

end AlgebraicGeometry.ProEtale
