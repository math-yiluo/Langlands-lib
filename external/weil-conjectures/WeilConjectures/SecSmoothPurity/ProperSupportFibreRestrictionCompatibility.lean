/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
public import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality

/-! # Fibre restriction compatibility for proper-support pullback

Source: Stacks Project, More on Étale Cohomology, Tag 0F55 (lemma-base-change-f-shriek-separated),
construction and geometric-stalk verification.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme
set_option autoImplicit false

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

-- Use composition coherence directly with module coefficients.
private theorem section_composition_unit
    (Λ : Type (u + 1)) [CommRing Λ] {T Z X : Scheme.{u}}
    (a : T ⟶ Z) (b : Z ⟶ X) (c : T ⟶ X) (hc : c = a ≫ b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : X.Etale) (W : T.Etale) (h : W ⟶ c.Etale.obj V) :
    let A := ModuleCat.{u + 1} Λ
    ((upperStarLowerStarAdjunction A c).unit.app F).hom.app (op V) ≫
        ((c)^*[A].obj F).obj.map h.op ≫
        ((upperStarComp A a b c hc).hom.app F).hom.app (op W) =
      ((upperStarLowerStarAdjunction A b).unit.app F).hom.app (op V) ≫
        ((upperStarLowerStarAdjunction A a).unit.app ((b)^*[A].obj F)).hom.app
          (op (b.Etale.obj V)) ≫
        ((a)^*[A].obj ((b)^*[A].obj F)).obj.map
          (h ≫ (MorphismProperty.Over.pullbackComp
            (P := @Etale) (Q := ⊤) a b c hc).hom.app V).op := by
  dsimp only
  let A := ModuleCat.{u + 1} Λ
  have hh := congrArg (fun α ↦ α.hom.app (op V))
    (upperStarComp_hom_app_unit_app A a b F c hc)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at hh
  rw [((upperStarComp A a b c hc).hom.app F).hom.naturality, ← Category.assoc]
  erw [hh]
  simp only [Functor.comp_obj, Iso.symm_inv, lowerStar_map_hom_app, Category.assoc,
    ← Functor.map_comp, ← op_comp]
  rfl

private theorem section_pullback_comp
    (Λ : Type (u + 1)) [CommRing Λ] {T Z X : Scheme.{u}}
    (a : T ⟶ Z) (b : Z ⟶ X) (c : T ⟶ X) (hc : c = a ≫ b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : X.Etale) (D : Z.Etale) (W : T.Etale)
    (h : D ⟶ b.Etale.obj V) (k : W ⟶ a.Etale.obj D) :
    let A := ModuleCat.{u + 1} Λ
    ((upperStarLowerStarAdjunction A b).unit.app F).hom.app (op V) ≫
      ((b)^*[A].obj F).obj.map h.op ≫
      ((upperStarLowerStarAdjunction A a).unit.app ((b)^*[A].obj F)).hom.app (op D) ≫
      ((a)^*[A].obj ((b)^*[A].obj F)).obj.map k.op =
    ((upperStarLowerStarAdjunction A c).unit.app F).hom.app (op V) ≫
      ((c)^*[A].obj F).obj.map
        (k ≫ a.Etale.map h ≫ (MorphismProperty.Over.pullbackComp
          (P := @Etale) (Q := ⊤) a b c hc).inv.app V).op ≫
      ((upperStarComp A a b c hc).hom.app F).hom.app (op W) := by
  dsimp only
  rw [section_composition_unit]
  simp only [Category.assoc]
  erw [reassoc_of% ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app
      ((b)^*[ModuleCat.{u + 1} Λ].obj F)).hom.naturality h.op]
  have hn : ((a)_*[ModuleCat.{u + 1} Λ].obj
        ((a)^*[ModuleCat.{u + 1} Λ].obj ((b)^*[ModuleCat.{u + 1} Λ].obj F))).obj.map h.op =
      ((a)^*[ModuleCat.{u + 1} Λ].obj ((b)^*[ModuleCat.{u + 1} Λ].obj F)).obj.map
        (a.Etale.map h).op := rfl
  rw [hn]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Functor.map_comp, op_comp]
  have hid := ((a)^*[ModuleCat.{u + 1} Λ].obj
    ((b)^*[ModuleCat.{u + 1} Λ].obj F)).obj.map_id
      (op (a.Etale.obj (b.Etale.obj V)))
  erw [hid]
  erw [Category.id_comp]

private noncomputable def sectionPullbackLift {T Z : Scheme.{u}} (a : T ⟶ Z) :
    Scheme.Etale.mk (𝟙 T) ⟶ a.Etale.obj (Scheme.Etale.mk (𝟙 Z)) :=
  MorphismProperty.Over.homMk
    (pullback.lift a (𝟙 T) (by
      change a ≫ 𝟙 Z = 𝟙 T ≫ a
      exact (Category.comp_id a).trans (Category.id_comp a).symm))
    (by
      change pullback.lift a (𝟙 T) _ ≫ pullback.snd (𝟙 Z) a = 𝟙 T
      exact pullback.lift_snd _ _ _)

attribute [local irreducible] upperStar upperStarLowerStarAdjunction upperStarComp

private noncomputable def sectionPullbackIso
    (Λ : Type (u + 1)) [CommRing Λ] {T Z : Scheme.{u}}
    (a : T ⟶ Z) [IsIso a]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 Z))) ≅
      ((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T))) := by
  let A := ModuleCat.{u + 1} Λ
  have : ((a)^*[A]).IsEquivalence := isEquivalence_upperStar_of_isIso A a
  have : IsIso (sectionPullbackLift a) := by
    let ht := (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z).isTerminalObj
      a.Etale
    let e := (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).uniqueUpToIso ht
    have he : sectionPullbackLift a = e.hom := ht.hom_ext _ _
    rw [he]
    infer_instance
  exact asIso (((upperStarLowerStarAdjunction A a).unit.app F).hom.app
    (op (Scheme.Etale.mk (𝟙 Z))) ≫
    ((a)^*[A].obj F).obj.map (sectionPullbackLift a).op)

private theorem sectionPullbackIso_hom
    (Λ : Type (u + 1)) [CommRing Λ] {T Z : Scheme.{u}}
    (a : T ⟶ Z) [IsIso a]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sectionPullbackIso Λ a F).hom =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 Z))) ≫
      ((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.map (sectionPullbackLift a).op := rfl

attribute [local irreducible] sectionPullbackIso

-- Support is detected by nonzero geometric germs, including after coefficient transport.
private theorem sheaf_iso_support
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    {F H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ≅ H)
    (V : X.Etale) (p : V.left ⟶ S) [LocallyOfFiniteType p]
    (s : F.obj.obj (op V)) :
    SectionHasProperSupport Λ H V p (e.hom.hom.app (op V) s) ↔
      SectionHasProperSupport Λ F V p s := by
  have hg (K : Type u) [Field K] [IsSepClosed K] (k : Spec (.of K) ⟶ V.left) :
      (pointSmallEtale (k ≫ V.hom)).toPresheafFiber V (Over.homMk k) H.obj
          (e.hom.hom.app (op V) s) = 0 ↔
        (pointSmallEtale (k ≫ V.hom)).toPresheafFiber V (Over.homMk k) F.obj s = 0 := by
    let P := pointSmallEtale (k ≫ V.hom)
    have he := P.toPresheafFiber_naturality_apply e.hom.hom V (Over.homMk k) s
    change P.sheafFiber.map e.hom (P.toPresheafFiber V (Over.homMk k) F.obj s) = _ at he
    rw [← he]
    have hi := ((ConcreteCategory.isIso_iff_bijective
      (P.sheafFiber.map e.hom)).1 inferInstance).1
    exact ⟨fun hz ↦ hi (hz.trans (map_zero _).symm), fun hz ↦ by rw [hz, map_zero]⟩
  rw [sectionHasProperSupport_iff, sectionHasProperSupport_iff]
  constructor <;> rintro ⟨C, hC, hp⟩ <;> refine ⟨C, ?_, hp⟩ <;>
    intro K _ _ k
  · exact (hC K k).trans (not_congr (hg K k))
  · exact (hC K k).trans (not_congr (hg K k)).symm

private theorem germ_zero_lift_congr
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (s : F.obj.obj (op V)) {K : Type u} [Field K] [IsSepClosed K]
    (k l : Spec (.of K) ⟶ V.left) (h : k = l) :
    (pointSmallEtale (k ≫ V.hom)).toPresheafFiber V (Over.homMk k) F.obj s = 0 ↔
      (pointSmallEtale (l ≫ V.hom)).toPresheafFiber V (Over.homMk l) F.obj s = 0 := by
  subst l
  rfl

private theorem sectionPullbackIso_support
    (Λ : Type (u + 1)) [CommRing Λ] {T Z S : Scheme.{u}}
    (a : T ⟶ Z) [IsIso a]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (p : Z ⟶ S) (q : T ⟶ S) [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    [IsSeparated p] [IsSeparated q] (hq : a ≫ p = q)
    (s : F.obj.obj (op (Scheme.Etale.mk (𝟙 Z)))) :
    SectionHasProperSupport Λ ((a)^*[ModuleCat.{u + 1} Λ].obj F)
        (Scheme.Etale.mk (𝟙 T)) q ((sectionPullbackIso Λ a F).hom s) ↔
      SectionHasProperSupport Λ F (Scheme.Etale.mk (𝟙 Z)) p s := by
  let V := Scheme.Etale.mk (𝟙 Z)
  let W := Scheme.Etale.mk (𝟙 T)
  let E := (a)^*[ModuleCat.{u + 1} Λ].obj F
  let t := (sectionPullbackIso Λ a F).hom s
  have hg (K : Type u) [Field K] [IsSepClosed K] (k : Spec (.of K) ⟶ T) :
      (pointSmallEtale (k ≫ W.hom)).toPresheafFiber W (Over.homMk k) E.obj t = 0 ↔
        (pointSmallEtale ((k ≫ a) ≫ V.hom)).toPresheafFiber V
          (Over.homMk (k ≫ a)) F.obj s = 0 := by
    have h := pullback_restrict_germ_zero Λ a F V W (sectionPullbackLift a) s k
    change _ = 0 ↔ _ at h
    have he : (k ≫ (sectionPullbackLift a).left) ≫ pullback.fst V.hom a = k ≫ a := by
      change (k ≫ pullback.lift a (𝟙 T) _) ≫ pullback.fst (𝟙 Z) a = k ≫ a
      rw [Category.assoc, pullback.lift_fst]
    change (pointSmallEtale (k ≫ W.hom)).toPresheafFiber W (Over.homMk k) E.obj
      ((sectionPullbackIso Λ a F).hom s) = 0 ↔ _
    rw [sectionPullbackIso_hom]
    exact h.trans (germ_zero_lift_congr Λ F V s _ _ he)
  rw [sectionHasProperSupport_iff, sectionHasProperSupport_iff]
  constructor
  · rintro ⟨C, hC, hp⟩
    refine ⟨C.preimage (inv a).continuous, ?_,
      proper_iso_image q p (asIso a) hq C hp⟩
    intro K _ _ k
    change inv a (k default) ∈ C ↔ _
    have hh := (hC K (k ≫ inv a)).trans (not_congr (hg K (k ≫ inv a)))
    have hh' := hh.trans (not_congr (germ_zero_lift_congr Λ F V s _ k (by simp)))
    change inv a (k default) ∈ C ↔ _ at hh'
    exact hh'
  · rintro ⟨C, hC, hp⟩
    have hqa : inv a ≫ q = p := by rw [← hq, IsIso.inv_hom_id_assoc]
    refine ⟨C.preimage a.continuous, ?_,
      proper_iso_image p q (asIso a).symm hqa C hp⟩
    intro K _ _ k
    change a (k default) ∈ C ↔ _
    exact (hC K (k ≫ a)).trans (not_congr (hg K k)).symm

-- The pasted Cartesian square fixes both the fibre isomorphism and its projections.
private noncomputable def fibreSquareIso
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y') :
    pullback f' y' ≅ pullback f (y' ≫ b) :=
  ((IsPullback.of_hasPullback f' y').paste_horiz sq).isoPullback

private theorem fibreSquareIso_fst
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y') :
    (fibreSquareIso a f b f' sq y').hom ≫ pullback.fst f (y' ≫ b) =
      pullback.fst f' y' ≫ a :=
  ((IsPullback.of_hasPullback f' y').paste_horiz sq).isoPullback_hom_fst

private theorem fibreSquareIso_snd
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y') :
    (fibreSquareIso a f b f' sq y').hom ≫ pullback.snd f (y' ≫ b) =
      pullback.snd f' y' :=
  ((IsPullback.of_hasPullback f' y').paste_horiz sq).isoPullback_hom_snd

attribute [local irreducible] fibreSquareIso

private noncomputable def fibreTransportIso
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y') :
    (((pullback.fst f' y')^*[ModuleCat.{u + 1} Λ].obj
      ((a)^*[ModuleCat.{u + 1} Λ].obj F)).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback f' y'))))) ≅
    (((pullback.fst f (y' ≫ b))^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b)))))) := by
  let A := ModuleCat.{u + 1} Λ
  let d := fibreSquareIso a f b f' sq y'
  have hd : d.hom ≫ pullback.fst f (y' ≫ b) = pullback.fst f' y' ≫ a :=
    (fibreSquareIso_fst a f b f' sq y')
  let E := (pullback.fst f (y' ≫ b))^*[A].obj F
  let e : (pullback.fst f' y')^*[A].obj ((a)^*[A].obj F) ≅ (d.hom)^*[A].obj E :=
    ((upperStarComp A (pullback.fst f' y') a).app F).symm ≪≫
      (upperStarComp A d.hom (pullback.fst f (y' ≫ b))
        (pullback.fst f' y' ≫ a) hd.symm).app F
  exact ((sheafSections _ A).obj (op (Scheme.Etale.mk (𝟙 (pullback f' y'))))).mapIso e ≪≫
    (sectionPullbackIso Λ d.hom E).symm

private theorem fibreTransportIso_support
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    [IsSeparated f] [LocallyOfFiniteType f]
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y')
    (s : (((pullback.fst f' y')^*[ModuleCat.{u + 1} Λ].obj
      ((a)^*[ModuleCat.{u + 1} Λ].obj F)).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback f' y')))))) :
    letI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sq inferInstance
    SectionHasProperSupport Λ ((pullback.fst f (y' ≫ b))^*[ModuleCat.{u + 1} Λ].obj F)
        (Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b)))) (pullback.snd f (y' ≫ b))
        ((fibreTransportIso Λ a f b f' sq F y').hom s) ↔
      SectionHasProperSupport Λ ((pullback.fst f' y')^*[ModuleCat.{u + 1} Λ].obj
          ((a)^*[ModuleCat.{u + 1} Λ].obj F))
        (Scheme.Etale.mk (𝟙 (pullback f' y'))) (pullback.snd f' y') s := by
  dsimp only
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sq inferInstance
  have : IsSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  let A := ModuleCat.{u + 1} Λ
  let d := fibreSquareIso a f b f' sq y'
  let E := (pullback.fst f (y' ≫ b))^*[A].obj F
  have hd : d.hom ≫ pullback.fst f (y' ≫ b) = pullback.fst f' y' ≫ a :=
    (fibreSquareIso_fst a f b f' sq y')
  let e : (pullback.fst f' y')^*[A].obj ((a)^*[A].obj F) ≅ (d.hom)^*[A].obj E :=
    ((upperStarComp A (pullback.fst f' y') a).app F).symm ≪≫
      (upperStarComp A d.hom (pullback.fst f (y' ≫ b))
        (pullback.fst f' y' ≫ a) hd.symm).app F
  let T := Scheme.Etale.mk (𝟙 (pullback f' y'))
  have he := sheaf_iso_support Λ e T (pullback.snd f' y') s
  have hdq : d.hom ≫ pullback.snd f (y' ≫ b) = pullback.snd f' y' :=
    (fibreSquareIso_snd a f b f' sq y')
  have hs := sectionPullbackIso_support Λ d.hom E
    (pullback.snd f (y' ≫ b)) (pullback.snd f' y') hdq
    ((fibreTransportIso Λ a f b f' sq F y').hom s)
  have hi : (sectionPullbackIso Λ d.hom E).hom
      ((fibreTransportIso Λ a f b f' sq F y').hom s) = e.hom.hom.app (op T) s := by
    change (sectionPullbackIso Λ d.hom E).hom
      ((sectionPullbackIso Λ d.hom E).inv (e.hom.hom.app (op T) s)) = _
    exact ConcreteCategory.congr_hom (sectionPullbackIso Λ d.hom E).inv_hom_id
      (e.hom.hom.app (op T) s)
  rw [hi] at hs
  exact hs.symm.trans he

private theorem etale_comp_fst
    {C : Type*} [Category* C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    {T Z X : C} (a : T ⟶ Z) (b : Z ⟶ X) (c : T ⟶ X) (hc : c = a ≫ b)
    (V : P.Over ⊤ X) (D : P.Over ⊤ Z) (W : P.Over ⊤ T)
    (h : D ⟶ (MorphismProperty.Over.pullback P ⊤ b).obj V)
    (k : W ⟶ (MorphismProperty.Over.pullback P ⊤ a).obj D) :
    (k ≫ (MorphismProperty.Over.pullback P ⊤ a).map h ≫
      (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) a b c hc).inv.app V).left ≫
        pullback.fst V.hom c =
    k.left ≫ pullback.fst D.hom a ≫ h.left ≫ pullback.fst V.hom b := by
  change (k.left ≫ _ ≫ _) ≫ _ = _
  rw [MorphismProperty.Over.pullbackComp_inv_app_left a b c hc V,
    MorphismProperty.Over.pullback_map_left]
  simp only [Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]
  erw [pullback.lift_fst_assoc]
  simp only [Category.assoc]

private theorem scheme_etale_comp_fst {T Z X : Scheme.{u}}
    (a : T ⟶ Z) (b : Z ⟶ X) (c : T ⟶ X) (hc : c = a ≫ b)
    (V : X.Etale) (D : Z.Etale) (W : T.Etale)
    (h : D ⟶ b.Etale.obj V) (k : W ⟶ a.Etale.obj D) :
    (k ≫ a.Etale.map h ≫ (MorphismProperty.Over.pullbackComp
      (P := @Etale) (Q := ⊤) a b c hc).inv.app V).left ≫ pullback.fst V.hom c =
      k.left ≫ pullback.fst D.hom a ≫ h.left ≫ pullback.fst V.hom b :=
  etale_comp_fst (@Etale) a b c hc V D W h k

private theorem etale_over_projection {Z : Scheme.{u}} {D V : Z.Etale} (l r : D ⟶ V) :
    l.left ≫ V.hom = r.left ≫ V.hom := l.w.trans r.w.symm

private theorem geometricLift_fst
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    (geometricFibreSectionLift sq V v).left ≫ pullback.fst (f.Etale.obj V).hom g' =
      pullback.lift (f' ≫ v.left) g'
        (by
          have hv : v.left ≫ V.hom = s := v.w
          rw [Category.assoc, hv]
          exact sq.w.symm) := by
  exact pullback.lift_fst _ _ _

private theorem sectionPullbackLift_fst {T Z : Scheme.{u}} (a : T ⟶ Z) :
    (sectionPullbackLift a).left ≫ pullback.fst (Scheme.Etale.mk (𝟙 Z)).hom a = a := by
  exact pullback.lift_fst _ _ _

private theorem baseChangeEtaleMap_fst
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    (properSupportBaseChangeEtaleMap a f b f' sq U).left ≫
      pullback.fst (f.Etale.obj U).hom a = properSupportBaseChangeProjection a f b f' sq U := by
  exact pullback.lift_fst _ _ _

private theorem baseChangeProjection_fst
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    properSupportBaseChangeProjection a f b f' sq U ≫ pullback.fst U.hom f =
      pullback.fst (b.Etale.obj U).hom f' ≫ pullback.fst U.hom b := by
  exact pullback.lift_fst _ _ _

private theorem baseChangeProjection_snd
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    properSupportBaseChangeProjection a f b f' sq U ≫ pullback.snd U.hom f =
      pullback.snd (b.Etale.obj U).hom f' ≫ a := by
  exact pullback.lift_snd _ _ _

attribute [local irreducible] sectionPullbackLift geometricFibreSectionLift
  properSupportBaseChangeEtaleMap properSupportBaseChangeProjection

private theorem fibre_lift_composition
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y')
    (U : Y.Etale) (v : (pointSmallEtale (y' ≫ b)).fiber.obj U) :
    let d := fibreSquareIso a f b f' sq y'
    let c := pullback.fst f' y' ≫ a
    let hd : c = d.hom ≫ pullback.fst f (y' ≫ b) :=
      (fibreSquareIso_fst a f b f' sq y').symm
    geometricFibreSectionLift (IsPullback.of_hasPullback f' y').toCommSq
        (b.Etale.obj U) ((pointSmallEtaleFiberEtaleIso b y').inv.app U v) ≫
      (pullback.fst f' y').Etale.map (properSupportBaseChangeEtaleMap a f b f' sq U) ≫
      (MorphismProperty.Over.pullbackComp
        (P := @Etale) (Q := ⊤) (pullback.fst f' y') a).inv.app (f.Etale.obj U) =
    sectionPullbackLift d.hom ≫ d.hom.Etale.map
      (geometricFibreSectionLift (IsPullback.of_hasPullback f (y' ≫ b)).toCommSq U v) ≫
      (MorphismProperty.Over.pullbackComp
        (P := @Etale) (Q := ⊤) d.hom (pullback.fst f (y' ≫ b)) c hd).inv.app
        (f.Etale.obj U) := by
  dsimp only
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · rw [scheme_etale_comp_fst (pullback.fst f' y') a
      (pullback.fst f' y' ≫ a) rfl (f.Etale.obj U) (f'.Etale.obj (b.Etale.obj U))
      (Scheme.Etale.mk (𝟙 (pullback f' y')))
      (properSupportBaseChangeEtaleMap a f b f' sq U)
      (geometricFibreSectionLift (IsPullback.of_hasPullback f' y').toCommSq
        (b.Etale.obj U) ((pointSmallEtaleFiberEtaleIso b y').inv.app U v))]
    rw [scheme_etale_comp_fst (fibreSquareIso a f b f' sq y').hom
      (pullback.fst f (y' ≫ b)) (pullback.fst f' y' ≫ a)
      (fibreSquareIso_fst a f b f' sq y').symm
      (f.Etale.obj U) (Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b))))
      (Scheme.Etale.mk (𝟙 (pullback f' y')))
      (geometricFibreSectionLift (IsPullback.of_hasPullback f (y' ≫ b)).toCommSq U v)
      (sectionPullbackLift (fibreSquareIso a f b f' sq y').hom)]
    simp only [← Category.assoc]
    rw [geometricLift_fst]
    rw [sectionPullbackLift_fst]
    simp only [Category.assoc]
    rw [baseChangeEtaleMap_fst a f b f' sq U]
    rw [geometricLift_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeProjection_fst]
      simp only [← Category.assoc, pullback.lift_fst]
      simp only [Category.assoc, pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
      simp only [pullback.lift_fst]
      exact (congrArg (fun z ↦ z ≫ v.left)
        (fibreSquareIso_snd a f b f' sq y')).symm.trans
          (Category.assoc _ _ _)
    · rw [Category.assoc, baseChangeProjection_snd]
      simp only [← Category.assoc, pullback.lift_snd]
      simp only [Category.assoc, pullback.lift_snd]
      exact (fibreSquareIso_fst a f b f' sq y').symm
  · exact etale_over_projection _ _

private theorem fibreTransportIso_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y')
    (U : Y.Etale) (v : (pointSmallEtale (y' ≫ b)).fiber.obj U) :
    properSupportUnitPullback a f b f' sq F U ≫
      geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f' y').toCommSq
        ((a)^*[ModuleCat.{u + 1} Λ].obj F) (b.Etale.obj U)
        ((pointSmallEtaleFiberEtaleIso b y').inv.app U v) ≫
      (fibreTransportIso Λ a f b f' sq F y').hom =
    geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f (y' ≫ b)).toCommSq
      F U v := by
  let A := ModuleCat.{u + 1} Λ
  let d := fibreSquareIso a f b f' sq y'
  let c := pullback.fst f' y' ≫ a
  have hd : c = d.hom ≫ pullback.fst f (y' ≫ b) :=
    (fibreSquareIso_fst a f b f' sq y').symm
  let W := f.Etale.obj U
  let T := Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b)))
  let T' := Scheme.Etale.mk (𝟙 (pullback f' y'))
  let r := geometricFibreSectionLift (IsPullback.of_hasPullback f (y' ≫ b)).toCommSq U v
  let r' := geometricFibreSectionLift (IsPullback.of_hasPullback f' y').toCommSq
    (b.Etale.obj U) ((pointSmallEtaleFiberEtaleIso b y').inv.app U v)
  let L := r' ≫ (pullback.fst f' y').Etale.map
    (properSupportBaseChangeEtaleMap a f b f' sq U) ≫
    (MorphismProperty.Over.pullbackComp
      (P := @Etale) (Q := ⊤) (pullback.fst f' y') a).inv.app W
  let R := sectionPullbackLift d.hom ≫ d.hom.Etale.map r ≫
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      d.hom (pullback.fst f (y' ≫ b)) c hd).inv.app W
  have hLR : L = R := fibre_lift_composition a f b f' sq y' U v
  let C1 := ((sheafSections (pullback f' y').smallEtaleTopology A).obj (op T')).mapIso
    ((upperStarComp A (pullback.fst f' y') a).app F)
  let C2 := ((sheafSections (pullback f' y').smallEtaleTopology A).obj (op T')).mapIso
    ((upperStarComp A d.hom (pullback.fst f (y' ≫ b)) c hd).app F)
  let j := sectionPullbackIso Λ d.hom ((pullback.fst f (y' ≫ b))^*[A].obj F)
  let t := ((upperStarLowerStarAdjunction A c).unit.app F).hom.app (op W) ≫
    ((c)^*[A].obj F).obj.map R.op
  have h1 : properSupportUnitPullback a f b f' sq F U ≫
      geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f' y').toCommSq
        ((a)^*[A].obj F) (b.Etale.obj U)
        ((pointSmallEtaleFiberEtaleIso b y').inv.app U v) = t ≫ C1.hom := by
    have h := section_pullback_comp Λ (pullback.fst f' y') a c rfl F W
      (f'.Etale.obj (b.Etale.obj U)) T'
      (properSupportBaseChangeEtaleMap a f b f' sq U) r'
    change _ = (_ ≫ ((c)^*[A].obj F).obj.map L.op) ≫ C1.hom at h
    rw [hLR] at h
    exact h
  have h2 : geometricFibreSectionRestriction Λ
      (IsPullback.of_hasPullback f (y' ≫ b)).toCommSq F U v ≫ j.hom = t ≫ C2.hom := by
    dsimp only [j]
    rw [sectionPullbackIso_hom]
    exact section_pullback_comp Λ d.hom (pullback.fst f (y' ≫ b)) c hd F W T T'
      r (sectionPullbackLift d.hom)
  apply (cancel_mono j.hom).1
  change (_ ≫ _ ≫ (C1.inv ≫ C2.hom ≫ j.inv)) ≫ j.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, h1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact h2.symm

attribute [local irreducible] fibreTransportIso

-- The adjunct unit equation on a pointed representative, before imposing support.
private theorem adjunct_stalk_germ
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' : Scheme.{u}} (b : Y' ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (α : G ⟶ (b)_*[ModuleCat.{u + 1} Λ].obj H)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y')
    (U : Y.Etale) (v : (pointSmallEtale (y' ≫ b)).fiber.obj U) :
    let β := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) b).homEquiv G H).symm α
    (pointSmallEtale (y' ≫ b)).toPresheafFiber U v G.obj ≫
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) b y').app G).inv ≫
      (pointSmallEtale y').sheafFiber.map β =
    α.hom.app (op U) ≫ (pointSmallEtale y').toPresheafFiber (b.Etale.obj U)
      ((pointSmallEtaleFiberEtaleIso b y').inv.app U v) H.obj := by
  dsimp only
  let β := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) b).homEquiv G H).symm α
  let cG := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) b y').app G
  have hsrc := pullback_unit_germ Λ b y' G U v
  rw [← Category.assoc] at hsrc
  have hsrc' := (Iso.eq_comp_inv cG).2 hsrc
  rw [← Category.assoc, ← hsrc', Category.assoc]
  change _ ≫ (pointSmallEtale y').toPresheafFiber _ _ _ ≫
    (pointSmallEtale y').presheafFiber.map β.hom = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) b).unit.app G ≫
      (b)_*[ModuleCat.{u + 1} Λ].map β = α :=
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) b).homEquiv G H).apply_symm_apply α
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  change ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) b).unit.app G).hom.app
    (op U) ≫ β.hom.app (op (b.Etale.obj U)) = α.hom.app (op U) at huU
  change _ ≫ β.hom.app (op (b.Etale.obj U)) ≫ _ = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ (pointSmallEtale y').toPresheafFiber (b.Etale.obj U)
      ((pointSmallEtaleFiberEtaleIso b y').inv.app U v) H.obj) huU)

private noncomputable def restrictModuleIso
    {Λ : Type (u + 1)} [CommRing Λ] {M N : ModuleCat.{u + 1} Λ}
    (k : M ≅ N) (S : Submodule Λ M) (T : Submodule Λ N)
    (h : ∀ s, k.hom s ∈ T ↔ s ∈ S) : ModuleCat.of Λ S ≅ ModuleCat.of Λ T :=
  LinearEquiv.toModuleIso
    { toFun := fun s ↦ ⟨k.hom s.val, (h _).2 s.property⟩
      invFun := fun s ↦ ⟨k.inv s.val, (h _).1 (by
        simpa only [← ConcreteCategory.comp_apply, Iso.inv_hom_id,
          ModuleCat.id_apply] using s.property)⟩
      left_inv := fun s ↦ Subtype.ext (ConcreteCategory.congr_hom k.hom_inv_id s.val)
      right_inv := fun s ↦ Subtype.ext (ConcreteCategory.congr_hom k.inv_hom_id s.val)
      map_add' := fun s t ↦ Subtype.ext (map_add k.hom.hom s.val t.val)
      map_smul' := fun r s ↦ Subtype.ext (map_smul k.hom.hom r s.val) }

private theorem restrictModuleIso_subtype
    {Λ : Type (u + 1)} [CommRing Λ] {M N : ModuleCat.{u + 1} Λ}
    (k : M ≅ N) (S : Submodule Λ M) (T : Submodule Λ N)
    (h : ∀ s, k.hom s ∈ T ↔ s ∈ S) :
    (restrictModuleIso k S T h).hom ≫ ModuleCat.ofHom T.subtype =
      ModuleCat.ofHom S.subtype ≫ k.hom := rfl

attribute [local irreducible] restrictModuleIso

/-- The canonical proper-support pullback map and its inverse-image/direct-image adjunct agree
on geometric stalks with restriction to the identified geometric fibre.

The maps `qG` and `qH` are the restriction maps supplied by `properSupport_geometricStalk`,
normalized by `geometricFibreSectionRestriction`; `eG` and `eH` have submodule codomains and
are characterized by the proper-support inclusion equations.  The coefficient/fibre transport
`κ₀` is characterized on every pulled-back representative by the two geometric-fibre
restriction maps and the inverse-image composition unit, and `κ` is its induced isomorphism on
proper-support submodules.  Thus no arbitrary stalk or fibre isomorphism occurs.

Proof (the four source computations).  (1) Represent a stalk germ by a pointed étale
neighbourhood.  The germ equation for `c` identifies the unit pullback germ with the original
germ, and the normalization of `qG` gives restriction to the geometric fibre.  (2) The adjunct
unit equation `b_*β ⋙ η = α` identifies the germ of `β` with the section-pullback map.  (3) The
Cartesian fibre isomorphism, the coefficient transport `κ₀`, and the inverse-image composition
unit identify the restriction of that pulled-back section with the restriction of the original
section.  (4) The explicit germ equality for every pointed neighbourhood implies equality of the
stalk maps by the colimit description of geometric stalks; the submodule inclusion equations
then give the displayed equality.
Source: Stacks Project, More on Étale Cohomology, Tags 0F55 and 0F76.
(auxiliary; not a blueprint node). -/
theorem properSupport_fibre_restriction_compatibility
    {Λ : Type (u + 1)} [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    [IsSeparated f] [LocallyOfFiniteType f]
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ιG : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F)
    (ιH : H ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f').obj
      ((upperStar (ModuleCat.{u + 1} Λ) a).obj F))
    [Mono ιG] [Mono ιH]
    (hG : ∀ (U : Y.Etale)
      (s : ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj.obj (op U)),
      (∃ t, (ιG.hom.app (op U)) t = s) ↔
        SectionHasProperSupport Λ F (f.Etale.obj U) (pullback.fst U.hom f) s)
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
            (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance)) s)
    (α : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) b).obj H)
    (hα : ∀ (U : Y.Etale) (s : G.obj.obj (op U)),
      (ιH.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)))
          ((α.hom.app (op U)) s) =
        (properSupportUnitPullback a f b f' sq F U)
          ((ιG.hom.app (op U)) s))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y' : Spec (.of Ω) ⟶ Y') :
    ∃ (qG : lowerStar (ModuleCat.{u + 1} Λ) f ⋙
        (Scheme.pointSmallEtale (y' ≫ b)).sheafFiber ⟶
          upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f (y' ≫ b)) ⋙
            (sheafSections (pullback f (y' ≫ b)).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj
              (op (Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b))))))
      (qH : lowerStar (ModuleCat.{u + 1} Λ) f' ⋙
        (Scheme.pointSmallEtale y').sheafFiber ⟶
          upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f' y') ⋙
            (sheafSections (pullback f' y').smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj
              (op (Scheme.Etale.mk (𝟙 (pullback f' y')))))
      (S_G : Submodule Λ
        (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f (y' ≫ b))).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b)))))))
      (S_H : Submodule Λ
        (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f' y')).obj
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).obj.obj
          (op (Scheme.Etale.mk (𝟙 (pullback f' y'))))))
      (eG : (Scheme.pointSmallEtale (y' ≫ b)).sheafFiber.obj G ≅ ModuleCat.of Λ S_G)
      (eH : (Scheme.pointSmallEtale y').sheafFiber.obj H ≅ ModuleCat.of Λ S_H)
      (κ₀ :
        (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f' y')).obj
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).obj.obj
          (op (Scheme.Etale.mk (𝟙 (pullback f' y'))))) ⟶
        (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f (y' ≫ b))).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b)))))))
      (κ : ModuleCat.of Λ S_H ≅ ModuleCat.of Λ S_G),
      (∀ (V : Y.Etale) (v : (Scheme.pointSmallEtale (y' ≫ b)).fiber.obj V),
        (Scheme.pointSmallEtale (y' ≫ b)).toPresheafFiber V v
            ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ qG.app F =
          geometricFibreSectionRestriction Λ
            (IsPullback.of_hasPullback f (y' ≫ b)).toCommSq F V v) ∧
      (∀ (V : Y'.Etale) (v : (Scheme.pointSmallEtale y').fiber.obj V),
        (Scheme.pointSmallEtale y').toPresheafFiber V v
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).obj ≫
              qH.app ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) =
          geometricFibreSectionRestriction Λ
            (IsPullback.of_hasPullback f' y').toCommSq
            ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) V v) ∧
      eG.hom ≫ ModuleCat.ofHom S_G.subtype =
        (Scheme.pointSmallEtale (y' ≫ b)).sheafFiber.map ιG ≫ qG.app F ∧
      eH.hom ≫ ModuleCat.ofHom S_H.subtype =
        (Scheme.pointSmallEtale y').sheafFiber.map ιH ≫
          qH.app ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) ∧
      κ.hom ≫ ModuleCat.ofHom S_G.subtype =
        ModuleCat.ofHom S_H.subtype ≫ κ₀ ∧
      (∀ (U : Y.Etale) (v : (Scheme.pointSmallEtale (y' ≫ b)).fiber.obj U)
        (s : F.obj.obj (op (f.Etale.obj U))),
        κ₀ ((geometricFibreSectionRestriction Λ
          (IsPullback.of_hasPullback f' y').toCommSq
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)
          ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)
          ((Scheme.pointSmallEtaleFiberEtaleIso b y').inv.app U v)).hom
          ((properSupportUnitPullback a f b f' sq F U) s)) =
          (geometricFibreSectionRestriction Λ
            (IsPullback.of_hasPullback f (y' ≫ b)).toCommSq F U v).hom s) ∧
      (let β :=
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) b).homEquiv G H).symm α
       ((Scheme.pointSmallEtale y').sheafFiber.map β) ≫ eH.hom ≫ κ.hom =
          ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) b y').app G).hom ≫ eG.hom)
     := by
  classical
  obtain ⟨qG, hqG, hqGrest⟩ := properSupport_geometricStalk Λ f (y' ≫ b)
  have : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  obtain ⟨qH, hqH, hqHrest⟩ := properSupport_geometricStalk Λ f' y'
  obtain ⟨S_G, hSG, eG, heG⟩ := hqGrest F G ιG (by infer_instance) hG
  obtain ⟨S_H, hSH, eH, heH⟩ :=
    hqHrest ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) H ιH (by infer_instance) hH
  let k := fibreTransportIso Λ a f b f' sq F y'
  have hk (s) := fibreTransportIso_support Λ a f b f' sq F y' s
  have hmem (s) : k.hom s ∈ S_G ↔ s ∈ S_H :=
    (hSG _).trans ((hk s).trans (hSH s).symm)
  let κ := restrictModuleIso k S_H S_G hmem
  have hκ : κ.hom ≫ ModuleCat.ofHom S_G.subtype =
      ModuleCat.ofHom S_H.subtype ≫ k.hom :=
    restrictModuleIso_subtype k S_H S_G hmem
  refine ⟨qG, qH, S_G, S_H, eG, eH, k.hom, κ, hqG F,
    hqH ((a)^*[ModuleCat.{u + 1} Λ].obj F), heG, heH, hκ, ?_, ?_⟩
  · intro U v s
    exact ConcreteCategory.congr_hom
      (fibreTransportIso_restriction Λ a f b f' sq F y' U v) s
  · dsimp only
    let β := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) b).homEquiv G H).symm α
    apply (cancel_mono (ModuleCat.ofHom S_G.subtype)).1
    simp only [Category.assoc, hκ, heG]
    rw [reassoc_of% heH]
    let cG := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) b y').app G
    apply (Iso.inv_comp_eq cG).1
    apply (pointSmallEtale (y' ≫ b)).presheafFiber_hom_ext
    intro U v
    change (pointSmallEtale (y' ≫ b)).toPresheafFiber U v G.obj ≫
      (cG.inv ≫ _ ≫ _ ≫ _ ≫ k.hom) =
      (pointSmallEtale (y' ≫ b)).toPresheafFiber U v G.obj ≫ _ ≫ qG.app F
    have hA := adjunct_stalk_germ Λ b G H α y' U v
    have hA' := reassoc_of% hA
    simp only [cG]
    rw [hA']
    change α.hom.app (op U) ≫
      (pointSmallEtale y').toPresheafFiber (b.Etale.obj U)
        ((pointSmallEtaleFiberEtaleIso b y').inv.app U v) H.obj ≫
      (pointSmallEtale y').presheafFiber.map ιH.hom ≫ _ ≫ k.hom =
      _ ≫ (pointSmallEtale (y' ≫ b)).presheafFiber.map ιG.hom ≫ qG.app F
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc,
      GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
    apply ModuleCat.hom_ext
    ext s
    have hHnorm := ConcreteCategory.congr_hom
      (hqH ((a)^*[ModuleCat.{u + 1} Λ].obj F) (b.Etale.obj U)
        ((pointSmallEtaleFiberEtaleIso b y').inv.app U v))
      ((ιH.hom.app (op (b.Etale.obj U))) ((α.hom.app (op U)) s))
    have hGnorm := ConcreteCategory.congr_hom (hqG F U v) ((ιG.hom.app (op U)) s)
    simp only [ConcreteCategory.comp_apply] at hHnorm hGnorm ⊢
    exact (congrArg (fun t ↦ k.hom t) hHnorm).trans
      ((congrArg (fun t ↦ k.hom
        ((geometricFibreSectionRestriction Λ
          (IsPullback.of_hasPullback f' y').toCommSq
          ((a)^*[ModuleCat.{u + 1} Λ].obj F) (b.Etale.obj U)
          ((pointSmallEtaleFiberEtaleIso b y').inv.app U v)) t)) (hα U s)).trans
        ((ConcreteCategory.congr_hom
          (fibreTransportIso_restriction Λ a f b f' sq F y' U v)
          ((ιG.hom.app (op U)) s)).trans hGnorm.symm))

end AlgebraicGeometry.Etale
