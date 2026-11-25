/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfFiniteOpenRestrictionPresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence

/-! # Intrinsic unit generators on an open immersion

The realization unit on underlying abelian sheaves is invertible. It and the
realization counit identify intrinsic open-restriction sections with ambient
sections. Evaluate the intrinsic extension adjunction unit using this identification.
The resulting generator is natural in its input module and commutes with coefficient
restriction, by the published normalized coefficient-square equation.

Source: Stacks 03DI, 03DJ and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Canonical section-transport construction.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
abbrev sfOpenGeneratorFixedUnderlying (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) AddCommGrpCat.{u + 1})

/-- Canonical section-transport construction.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
abbrev sfOpenGeneratorIntrinsicUnderlying (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A))

/-- Canonical section-transport construction.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
def sfOpenGeneratorRealizeMap (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    sfOpenGeneratorFixedUnderlying T A ⟶ (sfIntrinsicModuleEquivalence T A).functor ⋙
      sfOpenGeneratorIntrinsicUnderlying T A where
  app F := ⟨toSheafify (ProEt.topology T) ((sfOpenGeneratorFixedUnderlying T A).obj F).obj⟩
  naturality {F G} f := by
    ext V x
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality (ProEt.topology T)
        ((sfOpenGeneratorFixedUnderlying T A).map f).hom) V) x

/-- Canonical section-transport identity, proved from units and counits.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
theorem sfOpenGeneratorRealizeMap_isIso (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] : IsIso (sfOpenGeneratorRealizeMap T A) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  have : IsIso ((sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).map
      ((sfOpenGeneratorRealizeMap T A).app F)) :=
    isIso_toSheafify (ProEt.topology T) ((sfOpenGeneratorFixedUnderlying T A).obj F).property
  exact isIso_of_reflects_iso _ (sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1})

/-- Canonical section-transport construction.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
def sfOpenGeneratorRealize (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    sfOpenGeneratorFixedUnderlying T A ≅ (sfIntrinsicModuleEquivalence T A).functor ⋙
      sfOpenGeneratorIntrinsicUnderlying T A :=
  have := sfOpenGeneratorRealizeMap_isIso T A
  asIso (sfOpenGeneratorRealizeMap T A)

/-- Canonical section-transport construction.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
def sfOpenGeneratorInverse (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicModuleEquivalence T A).inverse ⋙ sfOpenGeneratorFixedUnderlying T A ≅
      sfOpenGeneratorIntrinsicUnderlying T A :=
  Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T A).inverse (sfOpenGeneratorRealize T A) ≪≫
    Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence T A).counitIso
      (sfOpenGeneratorIntrinsicUnderlying T A)

/-- Canonical section-transport identity, proved from units and counits.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
theorem sfOpenGeneratorInverse_hom (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (N : proEtaleRingModules T (proEtaleConstantRing T A))
    (V : T.ProEtᵒᵖ)
    (x : ((sfIntrinsicModuleEquivalence T A).inverse.obj N).obj.obj V) :
    ((sfOpenGeneratorInverse T A).hom.app N).hom.app V x =
      sfFixedToIntrinsicSection T A N V x := by
  unfold sfFixedToIntrinsicSection
  rfl

private theorem realization_restriction (T : Scheme.{u}) {A B : Type u}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B))) :
    (sfOpenGeneratorRealize T B).hom.app F ≫
        (sfOpenGeneratorIntrinsicUnderlying T A).map ((sfRealizationRestriction T φ).hom.app F) =
      (sfOpenGeneratorRealize T A).hom.app ((sfFixedRestriction T φ).obj F) := by
  ext V x
  exact (sfRealizationRestriction_existsUnique T φ).exists.choose_spec F V
    (((sfOpenGeneratorRealize T B).hom.app F).hom.app V x)

private theorem inverseUnderlying_realize (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (sfOpenGeneratorFixedUnderlying T A).map
        ((sfIntrinsicModuleEquivalence T A).unitIso.inv.app F) ≫
        (sfOpenGeneratorRealize T A).hom.app F =
      (sfOpenGeneratorInverse T A).hom.app ((sfIntrinsicModuleEquivalence T A).functor.obj F) := by
  have h := (sfOpenGeneratorRealize T A).hom.naturality
    ((sfIntrinsicModuleEquivalence T A).unitIso.inv.app F)
  simpa only [Functor.comp_map, ← Equivalence.counit_app_functor,
    sfOpenGeneratorInverse, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.comp_obj, Functor.id_obj] using h

private theorem inverseUnderlying_restriction (T : Scheme.{u}) {A B : Type u}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (N : proEtaleRingModules T (proEtaleConstantRing T B)) :
    (sfOpenGeneratorFixedUnderlying T A).map ((sfInverseRealizationRestriction T φ).hom.app N) ≫
        (sfOpenGeneratorInverse T B).hom.app N =
      (sfOpenGeneratorInverse T A).hom.app ((proEtaleCoefficientRestrictScalars T φ).obj N) := by
  let ea := sfIntrinsicModuleEquivalence T A
  let eb := sfIntrinsicModuleEquivalence T B
  let q := sfFixedRestriction T φ
  let Q := proEtaleCoefficientRestrictScalars T φ
  let κ := sfRealizationRestriction T φ
  let F := eb.inverse.obj N
  let f := Q.map (eb.counitIso.inv.app N) ≫ κ.hom.app F
  have hb : (sfOpenGeneratorInverse T B).hom.app N =
      (sfOpenGeneratorRealize T A).hom.app (q.obj F) ≫
        (sfOpenGeneratorIntrinsicUnderlying T A).map (κ.inv.app F) ≫
        (sfOpenGeneratorIntrinsicUnderlying T B).map (eb.counitIso.hom.app N) := by
    dsimp only [sfOpenGeneratorInverse, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [← realization_restriction T φ F]
    simp only [κ, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have hLambda : (sfInverseRealizationRestriction T φ).hom.app N =
      ea.inverse.map f ≫ ea.unitIso.inv.app (q.obj F) := by
    dsimp only [sfInverseRealizationRestriction, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [f, Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl
  rw [hLambda, Functor.map_comp, hb]
  simp only [← Category.assoc]
  rw [Category.assoc ((sfOpenGeneratorFixedUnderlying T A).map (ea.inverse.map f)),
    inverseUnderlying_realize T A (q.obj F)]
  have hn : (sfOpenGeneratorFixedUnderlying T A).map (ea.inverse.map f) ≫
      (sfOpenGeneratorInverse T A).hom.app (ea.functor.obj (q.obj F)) =
      (sfOpenGeneratorInverse T A).hom.app (Q.obj N) ≫
        (sfOpenGeneratorIntrinsicUnderlying T A).map f :=
    (sfOpenGeneratorInverse T A).hom.naturality f
  erw [hn]
  simp only [f, Functor.map_comp, Category.assoc]
  rw [← (sfOpenGeneratorIntrinsicUnderlying T A).map_comp_assoc (κ.hom.app F) (κ.inv.app F),
    Iso.hom_inv_id_app, (sfOpenGeneratorIntrinsicUnderlying T A).map_id, Category.id_comp]
  change (sfOpenGeneratorInverse T A).hom.app (Q.obj N) ≫
    (sfOpenGeneratorIntrinsicUnderlying T B).map (eb.counitIso.inv.app N) ≫
      (sfOpenGeneratorIntrinsicUnderlying T B).map (eb.counitIso.hom.app N) = _
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(sfOpenGeneratorIntrinsicUnderlying T B).map_id, Category.comp_id]

private theorem transported_left_unit
    {C D B : Type*} [Category C] [Category D] [Category B]
    (e : C ≌ D) {L : D ⥤ B} {R : B ⥤ D} (a : L ⊣ R)
    {L' : C ⥤ B} {R' : B ⥤ C} (b : L' ⊣ R') (r : R ⋙ e.inverse ≅ R') (M : C) :
    a.unit.app (e.functor.obj M) ≫
        R.map ((((e.toAdjunction.comp a).ofNatIsoRight r).leftAdjointUniq b).hom.app M) ≫
        e.counitIso.inv.app (R.obj (L'.obj M)) ≫ e.functor.map (r.hom.app (L'.obj M)) =
      e.functor.map (b.unit.app M) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((e.toAdjunction.comp a).ofNatIsoRight r) b M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  rw [Adjunction.comp_homEquiv] at h
  dsimp only [Equiv.trans] at h
  change (e.unitIso.hom.app M ≫ e.inverse.map
    (a.unit.app (e.functor.obj M) ≫ R.map
      ((((e.toAdjunction.comp a).ofNatIsoRight r).leftAdjointUniq b).hom.app M))) ≫
      r.hom.app (L'.obj M) = b.unit.app M at h
  have hf := congrArg (fun f ↦ e.functor.map f) h
  simp only [e.functor.map_comp, Category.assoc] at hf
  rw [← e.counitInv_app_functor] at hf
  change e.counitIso.inv.app (e.functor.obj M) ≫
    (e.inverse ⋙ e.functor).map (a.unit.app (e.functor.obj M) ≫ R.map
      ((((e.toAdjunction.comp a).ofNatIsoRight r).leftAdjointUniq b).hom.app M)) ≫
        e.functor.map (r.hom.app (L'.obj M)) = _ at hf
  rw [← e.counitIso.inv.naturality_assoc] at hf
  simpa only [Functor.id_map, Category.assoc] using hf

/-- Canonical section-transport identity, proved from units and counits.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
theorem sfOpenGeneratorTransportedUnit
    {C D B : Type*} [Category C] [Category D] [Category B]
    (e : C ≌ D) {L : D ⥤ B} {R : B ⥤ D} (a : L ⊣ R)
    {L' : C ⥤ B} {R' : B ⥤ C} (b : L' ⊣ R') (r : R ⋙ e.inverse ≅ R')
    {P : C ⥤ D} (t : e.functor ≅ P) (M : C) :
    a.unit.app (e.functor.obj M) ≫
        R.map ((((e.toAdjunction.comp a).ofNatIsoRight r).leftAdjointUniq b).hom.app M) ≫
        (e.counitIso.inv.app (R.obj (L'.obj M)) ≫
          e.functor.map (r.hom.app (L'.obj M)) ≫ t.hom.app (R'.obj (L'.obj M))) =
      t.hom.app M ≫ P.map (b.unit.app M) := by
  calc
    _ = (a.unit.app (e.functor.obj M) ≫
        R.map ((((e.toAdjunction.comp a).ofNatIsoRight r).leftAdjointUniq b).hom.app M) ≫
        e.counitIso.inv.app (R.obj (L'.obj M)) ≫ e.functor.map (r.hom.app (L'.obj M))) ≫
        t.hom.app (R'.obj (L'.obj M)) := by simp only [Category.assoc]
    _ = e.functor.map (b.unit.app M) ≫ t.hom.app (R'.obj (L'.obj M)) :=
      congrArg (fun f ↦ f ≫ t.hom.app _) (transported_left_unit e a b r M)
    _ = _ := t.hom.naturality _

/-- Canonical section-transport construction.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
def sfOpenGeneratorUnderlying {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A] :
    sfIntrinsicOpenRestriction j A ⋙ sfOpenGeneratorIntrinsicUnderlying X A ≅
      sfOpenGeneratorIntrinsicUnderlying Z A ⋙
        ProEtale.openImmersionRestriction AddCommGrpCat.{u + 1} j :=
  Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence Z A).inverse ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
      (sfOpenGeneratorRealize X A).symm ≪≫
    Functor.isoWhiskerRight (sfOpenGeneratorInverse Z A)
      (ProEtale.openImmersionRestriction AddCommGrpCat.{u + 1} j)

private theorem openUnderlying_restriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : proEtaleRingModules Z (proEtaleConstantRing Z B)) :
    (sfOpenGeneratorIntrinsicUnderlying X A).map
        ((sfOpenRestrictionCoefficientSquare j φ).hom.app N) ≫
        (sfOpenGeneratorUnderlying j B).hom.app N =
      (sfOpenGeneratorUnderlying j A).hom.app ((proEtaleCoefficientRestrictScalars Z φ).obj N) := by
  let F := (ProEtale.openImmersionRestriction
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).obj
      ((sfIntrinsicModuleEquivalence Z B).inverse.obj N)
  have hi : (sfOpenGeneratorIntrinsicUnderlying X A).map
        ((sfRealizationRestriction X φ).inv.app F) ≫
      (sfOpenGeneratorRealize X B).inv.app F =
      (sfOpenGeneratorRealize X A).inv.app ((sfFixedRestriction X φ).obj F) := by
    have h : (sfOpenGeneratorRealize X B).app F ≪≫
        (sfOpenGeneratorIntrinsicUnderlying X A).mapIso ((sfRealizationRestriction X φ).app F) =
        (sfOpenGeneratorRealize X A).app ((sfFixedRestriction X φ).obj F) :=
      Iso.ext (realization_restriction X φ F)
    exact congrArg Iso.inv h
  dsimp only [sfOpenRestrictionCoefficientSquare, sfOpenGeneratorUnderlying, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.refl_hom, NatTrans.id_app]
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    (sfIntrinsicModuleEquivalence X A).functor.map_id,
    Category.id_comp, Category.assoc]
  rw [← Category.assoc ((sfOpenGeneratorIntrinsicUnderlying X A).map
    ((sfRealizationRestriction X φ).inv.app F)), hi]
  rw [← Category.assoc]
  erw [(sfOpenGeneratorRealize X A).inv.naturality]
  simp only [Category.assoc]
  congr 1
  change (ProEtale.openImmersionRestriction AddCommGrpCat.{u + 1} j).map
      ((sfOpenGeneratorFixedUnderlying Z A).map ((sfInverseRealizationRestriction Z φ).hom.app N)) ≫
    (ProEtale.openImmersionRestriction AddCommGrpCat.{u + 1} j).map
      ((sfOpenGeneratorInverse Z B).hom.app N) = _
  rw [← Functor.map_comp, inverseUnderlying_restriction Z φ N]

/-- Canonical section-transport construction.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
def sfOpenGeneratorEvaluate {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A]
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) (W : Z.ProEt)
    (a : W ⟶ IntegralOpenReduction.openObject j)
    (x : ((sfIntrinsicOpenRestriction j A).obj N).val.obj
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) : N.val.obj (op W) :=
  N.val.map (sfFiniteOpenSliceObjectIso j (Over.mk a)).inv.op
    ((((sfOpenGeneratorUnderlying j A).hom.app N).hom.app
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) x)

private theorem openEvaluate_map {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A]
    {N N' : proEtaleRingModules Z (proEtaleConstantRing Z A)} (f : N ⟶ N')
    (W : Z.ProEt) (a : W ⟶ IntegralOpenReduction.openObject j)
    (x : ((sfIntrinsicOpenRestriction j A).obj N).val.obj
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    f.val.app (op W) (sfOpenGeneratorEvaluate j A N W a x) =
      sfOpenGeneratorEvaluate j A N' W a
        (((sfIntrinsicOpenRestriction j A).map f).val.app
          (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x) := by
  unfold sfOpenGeneratorEvaluate
  trans N'.val.map (sfFiniteOpenSliceObjectIso j (Over.mk a)).inv.op
    (f.val.app _ ((((sfOpenGeneratorUnderlying j A).hom.app N).hom.app
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) x))
  · exact PresheafOfModules.naturality_apply f.val
      (sfFiniteOpenSliceObjectIso j (Over.mk a)).inv.op _
  apply congrArg (N'.val.map (sfFiniteOpenSliceObjectIso j (Over.mk a)).inv.op)
  exact (congrArg (fun f ↦ f.hom.app
    (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)
      ((sfOpenGeneratorUnderlying j A).hom.naturality f)).symm

private theorem openEvaluate_restriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : proEtaleRingModules Z (proEtaleConstantRing Z B))
    (W : Z.ProEt) (a : W ⟶ IntegralOpenReduction.openObject j)
    (x : ((sfIntrinsicOpenRestriction j A).obj
      ((proEtaleCoefficientRestrictScalars Z φ).obj N)).val.obj
        (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    sfOpenGeneratorEvaluate j A ((proEtaleCoefficientRestrictScalars Z φ).obj N) W a x =
      sfOpenGeneratorEvaluate j B N W a
        (((sfOpenRestrictionCoefficientSquare j φ).hom.app N).val.app
          (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x) := by
  unfold sfOpenGeneratorEvaluate
  apply congrArg (N.val.map (sfFiniteOpenSliceObjectIso j (Over.mk a)).inv.op)
  exact (congrArg (fun f ↦ f.hom.app
    (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)
      (openUnderlying_restriction j φ N)).symm

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]

/-- Canonical section-transport construction.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
def sfOpenUnitGenerator (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : Z.ProEt)
    (a : W ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((sfIntrinsicExtensionByZero j A).obj M).val.obj (op W) :=
  sfOpenGeneratorEvaluate j A ((sfIntrinsicExtensionByZero j A).obj M) W a
    (((sfIntrinsicExtensionByZeroAdjunction j A).unit.app M).val.app
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)

/-- Canonical section-transport identity, proved from units and counits.
Source: Stacks 03DI and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators). -/
theorem sfOpenUnitGenerator_map (A : Type u) [CommRing A] [Finite A]
    {M M' : proEtaleRingModules X (proEtaleConstantRing X A)} (f : M ⟶ M')
    (W : Z.ProEt) (a : W ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((sfIntrinsicExtensionByZero j A).map f).val.app (op W)
        (sfOpenUnitGenerator j A M W a x) =
      sfOpenUnitGenerator j A M' W a
        (f.val.app (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x) := by
  unfold sfOpenUnitGenerator
  rw [openEvaluate_map]
  apply congrArg (sfOpenGeneratorEvaluate j A ((sfIntrinsicExtensionByZero j A).obj M') W a)
  exact (congrArg (fun f ↦ f.val.app
    (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)
      ((sfIntrinsicExtensionByZeroAdjunction j A).unit.naturality f)).symm

/-- Coefficient restriction preserves the intrinsic adjunction-unit generator.
Source: Stacks 03DI, 03DJ and 00YV.
(blueprint: lem-sf-intrinsic-open-unit-generators).

Proof: the sectionwise identity normalization of realization under scalar restriction
and the equivalence triangles show that inverse realization commutes with scalars.
Whisker through open restriction to identify the coefficient square on underlying
abelian sheaves. Evaluation therefore commutes with that square. Naturality of
evaluation and the published sfOpenRestriction_normalized_unique unit equation
then give the displayed identity on the evaluated intrinsic adjunction unit. -/
theorem sfOpenUnitGenerator_restriction {A B : Type u}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) (W : Z.ProEt)
    (a : W ⟶ IntegralOpenReduction.openObject j)
    (x : ((proEtaleCoefficientRestrictScalars X φ).obj M).val.obj
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((sfOpenRestriction j φ).hom.app M).val.app (op W)
        (sfOpenUnitGenerator j A ((proEtaleCoefficientRestrictScalars X φ).obj M) W a x) =
      sfOpenUnitGenerator j B M W a x := by
  unfold sfOpenUnitGenerator
  let v := op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))
  let z := ((sfIntrinsicExtensionByZeroAdjunction j A).unit.app
    ((proEtaleCoefficientRestrictScalars X φ).obj M)).val.app v x
  calc
    _ = sfOpenGeneratorEvaluate j A
        ((proEtaleCoefficientRestrictScalars Z φ).obj ((sfIntrinsicExtensionByZero j B).obj M))
        W a (((sfIntrinsicOpenRestriction j A).map
          ((sfOpenRestriction j φ).hom.app M)).val.app v z) :=
      openEvaluate_map j A ((sfOpenRestriction j φ).hom.app M) W a z
    _ = sfOpenGeneratorEvaluate j B ((sfIntrinsicExtensionByZero j B).obj M) W a
        (((sfOpenRestrictionCoefficientSquare j φ).hom.app
          ((sfIntrinsicExtensionByZero j B).obj M)).val.app v
            (((sfIntrinsicOpenRestriction j A).map
              ((sfOpenRestriction j φ).hom.app M)).val.app v z)) :=
      openEvaluate_restriction j φ _ W a _
    _ = _ := by
      apply congrArg (sfOpenGeneratorEvaluate j B ((sfIntrinsicExtensionByZero j B).obj M) W a)
      have h := (sfOpenRestriction_normalized_unique j φ).1 M
      exact congrArg (fun f ↦ f.val.app v x) h

end WeilConjectures
