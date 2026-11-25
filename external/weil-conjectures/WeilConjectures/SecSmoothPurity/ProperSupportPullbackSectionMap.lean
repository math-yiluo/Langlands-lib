/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality

/-! # Canonical proper-support pullback map

Source: Stacks Project, More on Étale Cohomology, Tag 0F55 (lemma-base-change-f-shriek-separated).
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry

/-- The projection of the pulled-back étale test scheme to the original test scheme.
Source: Stacks Project, More on Étale Cohomology, Tag 0F55.
(auxiliary; not a blueprint node) -/
noncomputable def properSupportBaseChangeProjection
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
      ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)).left ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U).left := by
  let U' := (MorphismProperty.Over.pullback @Etale ⊤ b).obj U
  have h :
      (pullback.snd U'.hom f' ≫ a) ≫ f =
        (pullback.fst U'.hom f' ≫ pullback.fst U.hom b) ≫ U.hom := by
    simp only [Category.assoc]
    rw [sq.w]
    rw [← Category.assoc, ← (pullback.condition (f := U'.hom) (g := f'))]
    rw [CategoryTheory.MorphismProperty.Over.pullback_obj_hom]
    simp only [Category.assoc]
    rw [← (pullback.condition (f := U.hom) (g := b))]
  let q₀ : pullback U'.hom f' ⟶ pullback U.hom f :=
    pullback.lift (pullback.fst U'.hom f' ≫ pullback.fst U.hom b)
      (pullback.snd U'.hom f' ≫ a) h.symm
  simpa only [CategoryTheory.MorphismProperty.Over.pullback_obj_left, U'] using q₀

/-- The lift of the Cartesian projection to the pulled-back étale test object.
Source: Stacks Project, Tag 0F55, evaluation of the ordinary pullback map.
(auxiliary; not a blueprint node) -/
noncomputable def properSupportBaseChangeEtaleMap
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    (MorphismProperty.Over.pullback @Etale ⊤ f').obj
        ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ a).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (properSupportBaseChangeProjection a f b f' sq U)
      (pullback.snd _ f') (by
        simp [properSupportBaseChangeProjection]))
    (by simp)

/-- Unit pullback on all ambient sections, followed by restriction along the canonical lift.
Source: Stacks Project, Tag 0F55; Étale Cohomology, equation-pullback.
(auxiliary; not a blueprint node) -/
noncomputable def properSupportUnitPullback
    {Λ : Type (u + 1)} [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale) :
    F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ⟶
      ((upperStar (ModuleCat.{u + 1} Λ) a).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
          ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U))) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ≫
    ((upperStar (ModuleCat.{u + 1} Λ) a).obj F).obj.map
      (properSupportBaseChangeEtaleMap a f b f' sq U).op

open Scheme

set_option backward.isDefEq.respectTransparency false

-- The ModuleCat form of the unit/germ calculation in InverseImageStalkGerm.
private theorem pullback_unit_germ
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
    (v : (pointSmallEtale (x ≫ f)).fiber.obj V) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom.app
          (op V) ≫
        (pointSmallEtale x).toPresheafFiber (f.Etale.obj V)
          ((pointSmallEtaleFiberEtaleIso f x).inv.app V v)
          ((upperStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫
        (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f x).hom.app F =
      (pointSmallEtale (x ≫ f)).toPresheafFiber V v F.obj := by
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f x).app F)).1
  simp only [upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (pointSmallEtale x).sheafFiber.map _ =
    (pointSmallEtale x).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (ModuleCat.{u + 1} Λ)
      (Y.smallGrothendieckTopology (P := @Etale))
      (X.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f) F
  have huV := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op V)
  rw [← Category.assoc, ← huV]
  rfl

private theorem germ_zero_change_point
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (s : F.obj.obj (op V)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (p q : Spec (.of Ω) ⟶ X) (hpq : p = q) (v : Spec (.of Ω) ⟶ V.left)
    (hv : v ≫ V.hom = p) (hv' : v ≫ V.hom = q) :
    (pointSmallEtale p).toPresheafFiber V (Over.homMk v hv) F.obj s = 0 ↔
      (pointSmallEtale q).toPresheafFiber V (Over.homMk v hv') F.obj s = 0 := by
  cases hpq
  rfl

private theorem pullback_restrict_germ_zero
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
    (W : X.Etale) (h : W ⟶ f.Etale.obj V) (s : F.obj.obj (op V))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (k : Spec (.of Ω) ⟶ W.left) :
    (pointSmallEtale (k ≫ W.hom)).toPresheafFiber W (Over.homMk k)
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj F).obj
        (((upperStar (ModuleCat.{u + 1} Λ) f).obj F).obj.map h.op
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom.app
            (op V) s)) = 0 ↔
      (pointSmallEtale (((k ≫ h.left) ≫ pullback.fst V.hom f) ≫ V.hom)).toPresheafFiber V
        (Over.homMk ((k ≫ h.left) ≫ pullback.fst V.hom f)) F.obj s = 0 := by
  let x := k ≫ W.hom
  let b := (k ≫ h.left) ≫ pullback.fst V.hom f
  have hb : b ≫ V.hom = x ≫ f := by
    dsimp only [b, x]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun a ↦ (k ≫ a) ≫ f) h.w
  let v : (pointSmallEtale (x ≫ f)).fiber.obj V := Over.homMk b hb
  let w : (pointSmallEtale x).fiber.obj W := Over.homMk k rfl
  have hw : (pointSmallEtale x).fiber.map h w =
      (pointSmallEtaleFiberEtaleIso f x).inv.app V v := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change b = _
      exact (pointSmallEtaleFiberEtaleIso_inv_app_left_fst f x V v).symm
    · change (k ≫ h.left) ≫ pullback.snd V.hom f = _
      have hh : h.left ≫ pullback.snd V.hom f = W.hom := h.w
      exact (Category.assoc k h.left _).trans
        ((congrArg (fun l ↦ k ≫ l) hh).trans
          (Over.Hom.w ((pointSmallEtaleFiberEtaleIso f x).inv.app V v)).symm)
  let H := (upperStar (ModuleCat.{u + 1} Λ) f).obj F
  let a := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom.app
    (op V) s
  have hg := (pointSmallEtale x).toPresheafFiber_w_apply h w H.obj a
  rw [hw] at hg
  have hu := ConcreteCategory.congr_hom (pullback_unit_germ Λ f x F V v) s
  change ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f x).hom.app F)
    ((pointSmallEtale x).toPresheafFiber (f.Etale.obj V)
      ((pointSmallEtaleFiberEtaleIso f x).inv.app V v) H.obj a) =
    (pointSmallEtale (x ≫ f)).toPresheafFiber V v F.obj s at hu
  have hinj := (ConcreteCategory.isIso_iff_bijective
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f x).hom.app F)).1
      (by infer_instance) |>.1
  change (pointSmallEtale x).toPresheafFiber W w H.obj (H.obj.map h.op a) = 0 ↔ _
  rw [hg]
  suffices hh : (pointSmallEtale x).toPresheafFiber (f.Etale.obj V)
      ((pointSmallEtaleFiberEtaleIso f x).inv.app V v) H.obj a = 0 ↔
      (pointSmallEtale (x ≫ f)).toPresheafFiber V v F.obj s = 0 by
    exact hh.trans (germ_zero_change_point Λ F V s (x ≫ f)
      (b ≫ V.hom) hb.symm b hb rfl)
  constructor
  · intro hz
    rw [← hu, hz, map_zero]
  · intro hz
    apply hinj
    rw [map_zero, hu, hz]

@[reassoc]
private theorem baseChangeEtaleMap_fst
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    (properSupportBaseChangeEtaleMap a f b f' sq U).left ≫
        pullback.fst (f.Etale.obj U).hom a =
      properSupportBaseChangeProjection a f b f' sq U := by
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem baseChangeEtaleMap_snd
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    (properSupportBaseChangeEtaleMap a f b f' sq U).left ≫
        pullback.snd (f.Etale.obj U).hom a =
      pullback.snd (b.Etale.obj U).hom f' := by
  exact pullback.lift_snd _ _ _

@[reassoc]
private theorem baseChangeProjection_fst
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    properSupportBaseChangeProjection a f b f' sq U ≫ pullback.fst U.hom f =
      pullback.fst (b.Etale.obj U).hom f' ≫ pullback.fst U.hom b := by
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem baseChangeProjection_snd
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    properSupportBaseChangeProjection a f b f' sq U ≫ pullback.snd U.hom f =
      pullback.snd (b.Etale.obj U).hom f' ≫ a := by
  exact pullback.lift_snd _ _ _

attribute [local irreducible] properSupportBaseChangeProjection properSupportBaseChangeEtaleMap

private theorem germ_zero_lift_congr
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (s : F.obj.obj (op V)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (v w : Spec (.of Ω) ⟶ V.left) (h : v = w) :
    (pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v) F.obj s = 0 ↔
      (pointSmallEtale (w ≫ V.hom)).toPresheafFiber V (Over.homMk w) F.obj s = 0 := by
  subst w
  rfl

private theorem unitPullback_germ
    {Λ : Type (u + 1)} [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (s : F.obj.obj (op (f.Etale.obj U)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (v : Spec (.of Ω) ⟶ (f'.Etale.obj (b.Etale.obj U)).left) :
    (Scheme.pointSmallEtale (v ≫ (f'.Etale.obj (b.Etale.obj U)).hom)).toPresheafFiber
        (f'.Etale.obj (b.Etale.obj U)) (Over.homMk v)
        ((upperStar (ModuleCat.{u + 1} Λ) a).obj F).obj
        (properSupportUnitPullback a f b f' sq F U s) ≠ 0 ↔
      (Scheme.pointSmallEtale ((v ≫ properSupportBaseChangeProjection a f b f' sq U) ≫
        (f.Etale.obj U).hom)).toPresheafFiber (f.Etale.obj U)
        (Over.homMk (v ≫ properSupportBaseChangeProjection a f b f' sq U)) F.obj s ≠ 0 := by
  have h := pullback_restrict_germ_zero Λ a F (f.Etale.obj U)
    (f'.Etale.obj (b.Etale.obj U)) (properSupportBaseChangeEtaleMap a f b f' sq U) s v
  have he : (v ≫ (properSupportBaseChangeEtaleMap a f b f' sq U).left) ≫
      pullback.fst (f.Etale.obj U).hom a =
        v ≫ properSupportBaseChangeProjection a f b f' sq U := by
    rw [Category.assoc, baseChangeEtaleMap_fst]
  exact not_congr (h.trans (germ_zero_lift_congr Λ F (f.Etale.obj U) s _ _ he))

@[reassoc]
private theorem etale_map_fst {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Etale} (r : V ⟶ U) :
    (f.Etale.map r).left ≫ pullback.fst U.hom f = pullback.fst V.hom f ≫ r.left := by
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem etale_map_snd {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Etale} (r : V ⟶ U) :
    (f.Etale.map r).left ≫ pullback.snd U.hom f = pullback.snd V.hom f := by
  exact pullback.lift_snd _ _ _

private theorem baseChangeEtaleMap_naturality
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) {U V : Y.Etale} (r : V ⟶ U) :
    f'.Etale.map (b.Etale.map r) ≫ properSupportBaseChangeEtaleMap a f b f' sq U =
      properSupportBaseChangeEtaleMap a f b f' sq V ≫ a.Etale.map (f.Etale.map r) := by
  apply MorphismProperty.Over.Hom.ext
  change (f'.Etale.map (b.Etale.map r)).left ≫
      (properSupportBaseChangeEtaleMap a f b f' sq U).left =
    (properSupportBaseChangeEtaleMap a f b f' sq V).left ≫
      (a.Etale.map (f.Etale.map r)).left
  apply pullback.hom_ext
  · rw [Category.assoc]
    erw [baseChangeEtaleMap_fst a f b f' sq U]
    rw [Category.assoc]
    erw [etale_map_fst a (f.Etale.map r)]
    rw [← Category.assoc]
    erw [baseChangeEtaleMap_fst a f b f' sq V]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [baseChangeProjection_fst a f b f' sq U]
      erw [etale_map_fst f r]
      erw [baseChangeProjection_fst_assoc a f b f' sq V]
      erw [etale_map_fst_assoc f' (b.Etale.map r)]
      erw [etale_map_fst b r]
    · simp only [Category.assoc]
      erw [baseChangeProjection_snd a f b f' sq U]
      erw [etale_map_snd f r]
      erw [baseChangeProjection_snd a f b f' sq V]
      erw [etale_map_snd_assoc f' (b.Etale.map r)]
  · simp only [Category.assoc]
    erw [baseChangeEtaleMap_snd a f b f' sq U]
    erw [etale_map_snd a (f.Etale.map r)]
    erw [baseChangeEtaleMap_snd a f b f' sq V]
    erw [etale_map_snd f' (b.Etale.map r)]

private theorem unitPullback_naturality
    {Λ : Type (u + 1)} [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {U V : Y.Etale} (r : V ⟶ U) :
    F.obj.map (f.Etale.map r).op ≫ properSupportUnitPullback a f b f' sq F V =
      properSupportUnitPullback a f b f' sq F U ≫
        ((upperStar (ModuleCat.{u + 1} Λ) a).obj F).obj.map
          (f'.Etale.map (b.Etale.map r)).op := by
  unfold properSupportUnitPullback
  rw [← Category.assoc]
  erw [((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app F).hom.naturality]
  have hm : (((upperStar (ModuleCat.{u + 1} Λ) a) ⋙
      lowerStar (ModuleCat.{u + 1} Λ) a).obj F).obj.map (f.Etale.map r).op =
      ((upperStar (ModuleCat.{u + 1} Λ) a).obj F).obj.map
        (a.Etale.map (f.Etale.map r)).op := rfl
  rw [hm]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
  rw [baseChangeEtaleMap_naturality]
  rfl

private theorem unitPullback_coeff
    {Λ : Type (u + 1)} [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    {F F₂ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ F₂)
    (U : Y.Etale) :
    φ.hom.app (op (f.Etale.obj U)) ≫ properSupportUnitPullback a f b f' sq F₂ U =
      properSupportUnitPullback a f b f' sq F U ≫
        ((upperStar (ModuleCat.{u + 1} Λ) a).map φ).hom.app
          (op (f'.Etale.obj (b.Etale.obj U))) := by
  have h := congrArg (fun t ↦ t.hom.app (op (f.Etale.obj U)))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.naturality φ)
  change φ.hom.app _ ≫ _ = _ ≫ _ at h
  unfold properSupportUnitPullback
  erw [← Category.assoc, h, Category.assoc]
  change _ ≫ (((upperStar (ModuleCat.{u + 1} Λ) a).map φ).hom.app
      (op (a.Etale.obj (f.Etale.obj U))) ≫ _) = _
  rw [← ((upperStar (ModuleCat.{u + 1} Λ) a).map φ).hom.naturality]
  rfl

private theorem unitPullback_square
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    IsPullback (properSupportBaseChangeProjection a f b f' sq U)
      (pullback.fst (b.Etale.obj U).hom f') (pullback.fst U.hom f)
      (pullback.fst U.hom b) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd U.hom f) (v₁₃ := f) ?_ ?_
    (IsPullback.of_hasPullback U.hom f).flip
  · simpa [properSupportBaseChangeProjection, Scheme.Hom.Etale,
      MorphismProperty.Over.pullback_obj_hom, ← pullback.condition] using
      ((IsPullback.of_hasPullback (b.Etale.obj U).hom f').flip.paste_horiz sq)
  · exact baseChangeProjection_fst a f b f' sq U

private theorem unitPullback_support
    {Λ : Type (u + 1)} [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    [IsSeparated f] [LocallyOfFiniteType f] (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (s : F.obj.obj (op (f.Etale.obj U)))
    (hs : SectionHasProperSupport Λ F (f.Etale.obj U) (pullback.fst U.hom f) s) :
    have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sq inferInstance
    SectionHasProperSupport Λ ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)
      (f'.Etale.obj (b.Etale.obj U)) (pullback.fst (b.Etale.obj U).hom f')
      (properSupportUnitPullback a f b f' sq F U s) := by
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sq inferInstance
  have : IsSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  obtain ⟨C, hC, hp⟩ := (sectionHasProperSupport_iff Λ F _ _ s).1 hs
  let q := properSupportBaseChangeProjection a f b f' sq U
  let psq := unitPullback_square a f b f' sq U
  apply (sectionHasProperSupport_iff Λ _ _ _ _).2
  refine ⟨C.preimage q.continuous, ?_, ?_⟩
  · intro Ω _ _ v
    change q (v default) ∈ C ↔ _
    have h := hC Ω (v ≫ q)
    rw [Scheme.Hom.comp_apply] at h
    exact h.trans (unitPullback_germ a f b f' sq F U s v).symm
  · have hb := (Scheme.closed_proper_support_locality.{u, u}
        (pullback.fst U.hom f) C).1
        (b.Etale.obj U).left (pullback.fst U.hom b) hp
    have ht := proper_iso_image _ _ psq.isoPullback.symm psq.isoPullback_inv_snd
      (C.preimage (pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom b)).continuous) hb
    have he : (C.preimage
        (pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom b)).continuous).preimage
        psq.isoPullback.hom.continuous = C.preimage q.continuous := by
      apply TopologicalSpace.Closeds.ext
      ext x
      change (psq.isoPullback.hom ≫ _) x ∈ C ↔ _
      rw [psq.isoPullback_hom_fst]
      rfl
    rwa [he] at ht

private theorem lift_moduleSheaf
    {Λ : Type (u + 1)} [CommRing Λ] {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C}
    {G H K : Sheaf J (ModuleCat.{u + 1} Λ)}
    (i : H ⟶ K) [Mono i] (t : G ⟶ K)
    (ht : ∀ U s, ∃ z, i.hom.app U z = t.hom.app U s) :
    ∃ l : G ⟶ H, l ≫ i = t := by
  classical
  have hi (U : Cᵒᵖ) : Function.Injective (i.hom.app U) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  let l (U : Cᵒᵖ) (s : G.obj.obj U) := (ht U s).choose
  have hl (U : Cᵒᵖ) (s : G.obj.obj U) : i.hom.app U (l U s) = t.hom.app U s :=
    (ht U s).choose_spec
  let lm (U : Cᵒᵖ) : G.obj.obj U ⟶ H.obj.obj U := ModuleCat.ofHom
    { toFun := l U
      map_add' := by
        intro x y
        apply hi U
        simp only [hl, map_add]
      map_smul' := by
        intro r x
        apply hi U
        simp only [hl, map_smul, RingHom.id_apply] }
  have hcomp (U : Cᵒᵖ) : lm U ≫ i.hom.app U = t.hom.app U := by
    ext s
    exact hl U s
  refine ⟨⟨{ app := lm, naturality := ?_ }⟩, ?_⟩
  · intro U V r
    apply (cancel_mono (i.hom.app V)).1
    rw [Category.assoc, hcomp, Category.assoc, i.hom.naturality,
      ← Category.assoc, hcomp]
    exact t.hom.naturality r
  · apply Sheaf.hom_ext
    exact NatTrans.ext (funext fun U ↦ hcomp U)

/-- The unit of constant-coefficient inverse image induces the canonical pullback map on
sections with proper geometric support in a Cartesian square.
Source: Stacks Project, More on Étale Cohomology, Tag 0F55 (lemma-base-change-f-shriek-separated).
(auxiliary; not a blueprint node)

Proof:
1. Evaluate the constant-coefficient inverse-image/direct-image unit on each étale
object (situation-conventions). Restrict along
`properSupportBaseChangeEtaleMap`, the lift of `properSupportBaseChangeProjection`.
This gives `properSupportUnitPullback` on every ambient section before imposing support.
2. The inverse-image stalk-and-germ comparison (lem-weil-pbc-inverse-image-stalk-germ)
identifies nonzero germs with those over the original point. The zero-open criterion
(lem-sc-etale-section-zero-open) makes this exactly equality of the support loci.
3. Local finite type is stable under base change (lem-weil-pbc-lft-base-change).
Closed proper supports pull back to closed proper supports
(lem-cbc-closed-proper-support-locality). The section descriptions therefore put the
unit image in H. The monomorphism ιH makes this lift unique and hence linear.
4. Naturality of the unit on test objects makes the lifts commute with restriction;
monicity of ιH detects these equalities. Thus the lifts form the sheaf morphism α.
The displayed component equation determines α uniquely, proving canonicity.
5. A coefficient morphism decreases support, and properness passes to closed subsets
(lem-weil-pbc-closed-subset-proper-over-base-properties). Thus it induces the maps γ
and δ between proper-support subsheaves. Naturality of the unit, followed by restriction,
identifies the two ambient composites. Monicity of the target inclusion ιH₂ yields
γ ≫ α₂ = α ≫ b_*δ, the stated coefficient-naturality square. -/
theorem properSupportPullbackSectionMap
    {Λ : Type (u + 1)} [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    [IsSeparated f] [LocallyOfFiniteType f]
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ιG : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F)
    (ιH : H ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) f').obj
        ((upperStar (ModuleCat.{u + 1} Λ) a).obj F))
    [Mono ιG] [Mono ιH]
    (hG : ∀ (U : Y.Etale)
      (s : ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj.obj (op U)),
      (∃ t, (ιG.hom.app (op U)) t = s) ↔
        SectionHasProperSupport Λ F
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)
          (pullback.fst U.hom f) s)
    (hH : ∀ (V : Y'.Etale)
      (s : ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
        ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).obj.obj (op V)),
      (∃ t, (ιH.hom.app (op V)) t = s) ↔
        @SectionHasProperSupport Λ _ X' V.left
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)
          ((MorphismProperty.Over.pullback @Etale ⊤ f').obj V)
          (pullback.fst V.hom f')
          (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
            (IsPullback.of_hasPullback V.hom f').flip
            (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance)) s) :
    ∃ α : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) b).obj H,
      (∀ (U : Y.Etale) (s : G.obj.obj (op U)),
        (ιH.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)))
            ((α.hom.app (op U)) s) =
          (properSupportUnitPullback a f b f' sq F U)
            ((ιG.hom.app (op U)) s)) ∧
      (∀ (U : Y.Etale) (s : G.obj.obj (op U)) (t : H.obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U))),
        t = (α.hom.app (op U)) s →
        ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
          (v : Spec (.of Ω) ⟶
            ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
              ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)).left),
          ((Scheme.pointSmallEtale
            (v ≫ ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
              ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)).hom)).toPresheafFiber
                ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
                  ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U))
                (Over.homMk v) ((upperStar (ModuleCat.{u + 1} Λ) a).obj F).obj
                  ((ιH.hom.app
                    (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U))).hom t) ≠ 0) ↔
          ((Scheme.pointSmallEtale
            ((v ≫ properSupportBaseChangeProjection a f b f' sq U) ≫
              ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U).hom)).toPresheafFiber
                ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)
                (Over.homMk (v ≫ properSupportBaseChangeProjection a f b f' sq U))
                F.obj ((ιG.hom.app (op U)) s) ≠ 0)) ∧
      (∀ (F₂ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (G₂ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (H₂ : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (ιG₂ : G₂ ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F₂)
        (ιH₂ : H₂ ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F₂)) [Mono ιH₂]
        (φ : F ⟶ F₂) (γ : G ⟶ G₂) (δ : H ⟶ H₂)
        (α₂ : G₂ ⟶ (lowerStar (ModuleCat.{u + 1} Λ) b).obj H₂),
        γ ≫ ιG₂ = ιG ≫ (lowerStar (ModuleCat.{u + 1} Λ) f).map φ →
        δ ≫ ιH₂ = ιH ≫ (lowerStar (ModuleCat.{u + 1} Λ) f').map
          ((upperStar (ModuleCat.{u + 1} Λ) a).map φ) →
        (∀ (U : Y.Etale) (s : G₂.obj.obj (op U)),
          (ιH₂.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)))
              ((α₂.hom.app (op U)) s) =
            (properSupportUnitPullback a f b f' sq F₂ U)
              ((ιG₂.hom.app (op U)) s)) →
        γ ≫ α₂ = α ≫ (lowerStar (ModuleCat.{u + 1} Λ) b).map δ) := by
  classical
  let A := ModuleCat.{u + 1} Λ
  let K := (lowerStar A b).obj ((lowerStar A f').obj ((upperStar A a).obj F))
  let t : G ⟶ K := ⟨{
    app := fun U ↦ ιG.hom.app U ≫ properSupportUnitPullback a f b f' sq F U.unop
    naturality := by
      intro U V r
      obtain ⟨U⟩ := U
      obtain ⟨V⟩ := V
      rw [← Category.assoc, ιG.hom.naturality]
      change (_ ≫ F.obj.map (f.Etale.map r.unop).op) ≫ _ = _
      rw [Category.assoc, unitPullback_naturality]
      rfl }⟩
  obtain ⟨α, hα⟩ := lift_moduleSheaf ((lowerStar A b).map ιH) t (by
    intro U s
    obtain ⟨U⟩ := U
    apply (hH (b.Etale.obj U) _).2
    apply unitPullback_support a f b f' sq F U _
    exact (hG U _).1 ⟨s, rfl⟩)
  have hαapp (U : Y.Etale) (s : G.obj.obj (op U)) :
      ιH.hom.app (op (b.Etale.obj U)) (α.hom.app (op U) s) =
        properSupportUnitPullback a f b f' sq F U (ιG.hom.app (op U) s) :=
    ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app (op U)) hα) s
  refine ⟨α, hαapp, ?_, ?_⟩
  · intro U s z hz Ω _ _ v
    subst z
    erw [hαapp]
    exact unitPullback_germ a f b f' sq F U _ v
  · intro F₂ G₂ H₂ ιG₂ ιH₂ _ φ γ δ α₂ hγ hδ hα₂
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    obtain ⟨U⟩ := U
    apply (cancel_mono (ιH₂.hom.app (op (b.Etale.obj U)))).1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    have hγs := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app (op U)) hγ) s
    have hδs := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app (op (b.Etale.obj U))) hδ)
      (α.hom.app (op U) s)
    change ιH₂.hom.app _ (α₂.hom.app _ (γ.hom.app _ s)) =
      ιH₂.hom.app _ (δ.hom.app _ (α.hom.app _ s))
    erw [hα₂, hδs]
    change properSupportUnitPullback a f b f' sq F₂ U
        (ιG₂.hom.app (op U) (γ.hom.app (op U) s)) =
      ((upperStar (ModuleCat.{u + 1} Λ) a).map φ).hom.app
        (op (f'.Etale.obj (b.Etale.obj U)))
        (ιH.hom.app (op (b.Etale.obj U)) (α.hom.app (op U) s))
    rw [hαapp]
    change ιG₂.hom.app (op U) (γ.hom.app (op U) s) =
      φ.hom.app (op (f.Etale.obj U)) (ιG.hom.app (op U) s) at hγs
    rw [hγs]
    exact ConcreteCategory.congr_hom (unitPullback_coeff a f b f' sq φ U) _

end AlgebraicGeometry.Etale
