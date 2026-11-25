/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction

/-! # Generator-normalized consecutive open scalar restriction

Source: Stacks 03DI, 03DA and 0E8I; Steps 1 and 2 of the open tensor quotient-model proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian

universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local instance 3000] SheafOfModules.instCategory SheafOfModules.instPreadditive

attribute [local irreducible] constantSheaf normalizedDVRQuotient
  integralCoefficientSheafTransition coefficientFiniteQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X V : Scheme.{t}} (j : X ⟶ V) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

private instance localSliceContinuous : (IntegralOpenReduction.sliceSite j).IsContinuous
    ((ProEt.topology V).over (IntegralOpenReduction.openObject j)) (ProEt.topology X) :=
  cbcSliceFunctor_continuous V (IntegralOpenReduction.openObject j)

private theorem horizontal_map {C : Type c} [Category.{v} C]
    (F : ℕᵒᵖ ⥤ Cᵒᵖ ⥤ CommRingCat.{r})
    {m n : ℕ} (h : n ≤ m) (W : Cᵒᵖ) :
    ((prodOpEquiv (C := ℕ) (D := C)).functor ⋙ Functor.uncurry.obj F).map
      (Prod.mkHom (homOfLE h) (𝟙 W.unop)).op = (F.map (homOfLE h).op).app W := by
  dsimp
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem finiteTransportSquare (n : ℕ) :
    o.finiteMap (n + 1) ≫
        ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)}
          ((ProEt.topology V).over (IntegralOpenReduction.openObject j))
          (ProEt.topology X)).map (IntegralOpenReduction.transitions l E X n) =
      ((ProEt.topology V).overPullback CommRingCat.{max u (t + 1)}
        (IntegralOpenReduction.openObject j)).map
          (IntegralOpenReduction.transitions l E V n) ≫ o.finiteMap n := by
  let := o.systemContinuous
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  have h := o.systemMap.hom.naturality
    (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 W.unop)).op
  rw [o.systemComponents n W.unop, o.systemComponents (n + 1) W.unop] at h
  change _ ≫ (o.finiteMap n).hom.app W =
    (o.finiteMap (n + 1)).hom.app W ≫ _ at h
  have hV : (IntegralOpenReduction.sliceRing l E j).obj.map
        (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 W.unop)).op =
      (((ProEt.topology V).overPullback CommRingCat.{max u (t + 1)}
        (IntegralOpenReduction.openObject j)).map
          (IntegralOpenReduction.transitions l E V n)).hom.app W := by
    change ((prodOpEquiv (C := ℕ) (D := Over (IntegralOpenReduction.openObject j))).functor ⋙
      Functor.uncurry.obj
        (Functor.ofOpSequence
          (X := fun k ↦ (IntegralOpenReduction.rings l E V k).over
            (IntegralOpenReduction.openObject j)) (fun k ↦
          ((ProEt.topology V).overPullback CommRingCat.{max u (t + 1)}
            (IntegralOpenReduction.openObject j)).map
              (IntegralOpenReduction.transitions l E V k)) ⋙
          sheafToPresheaf _ CommRingCat.{max u (t + 1)})).map
            (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 W.unop)).op = _
    rw [horizontal_map]
    change ((Functor.ofOpSequence
      (X := fun k ↦ (IntegralOpenReduction.rings l E V k).over
        (IntegralOpenReduction.openObject j))
      (fun k ↦ ((ProEt.topology V).overPullback CommRingCat.{max u (t + 1)}
        (IntegralOpenReduction.openObject j)).map
          (IntegralOpenReduction.transitions l E V k))).map
            (homOfLE (Nat.le_succ n)).op).hom.app W = _
    rw [Functor.ofOpSequence_map_homOfLE_succ]
  have hX : ((((𝟭 ℕ).prod (IntegralOpenReduction.sliceSite j)).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)}
        (coefficientSequenceTopology ((ProEt.topology V).over
          (IntegralOpenReduction.openObject j)))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X)).obj.map
        (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 W.unop)).op =
      (IntegralOpenReduction.transitions l E X n).hom.app
        (op ((IntegralOpenReduction.sliceSite j).obj W.unop)) := by
    change (coefficientSequenceCommRingPresheaf l E X).map
      (Prod.mkHom (homOfLE (Nat.le_succ n))
        (𝟙 ((IntegralOpenReduction.sliceSite j).obj W.unop))).op = _
    unfold coefficientSequenceCommRingPresheaf
    erw [horizontal_map]
    change ((Functor.ofOpSequence
      (X := fun k ↦ integralCoefficientCommRingSheaf l E X k)
      (coefficientSequenceCommRingTransition l E X)).map
        (homOfLE (Nat.le_succ n)).op).hom.app _ = _
    rw [Functor.ofOpSequence_map_homOfLE_succ]
  rw [hV, hX] at h
  exact h.symm

section PushforwardScalar

universe c₁ c₂ v₁ v₂ r₁

variable {C : Type c₁} [Category.{v₁} C] {D : Type c₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {R R' : Sheaf K RingCat.{r₁}} {S S' : Sheaf J RingCat.{r₁}}
  (f : S ⟶ (F.sheafPushforwardContinuous RingCat.{r₁} J K).obj R)
  (g : S' ⟶ (F.sheafPushforwardContinuous RingCat.{r₁} J K).obj R')
  (a : R ⟶ R') (b : S ⟶ S')
  (h : f ≫ (F.sheafPushforwardContinuous RingCat.{r₁} J K).map a = b ≫ g)

@[irreducible] private def pushforwardScalarIso :
    SheafOfModules.restrictScalars.{r₁} a ⋙ SheafOfModules.pushforward f ≅
      SheafOfModules.pushforward g ⋙ SheafOfModules.restrictScalars b :=
  SheafOfModules.pushforwardComp (F := F) (G := 𝟭 D) f a ≪≫
    SheafOfModules.pushforwardCongr (F := F) h ≪≫
    (SheafOfModules.pushforwardComp (F := 𝟭 C) (G := F) b g).symm

private theorem pushforwardScalarIso_apply (M : SheafOfModules.{r₁} R') (W : Cᵒᵖ)
    (x : M.val.obj (op (F.obj W.unop))) :
    ((pushforwardScalarIso F f g a b h).hom.app M).val.app W x = x := by
  unfold pushforwardScalarIso
  rfl

end PushforwardScalar

section OpenScalar

universe c₁ c₂ v₁ v₂ r₁

variable {C : Type c₁} [Category.{v₁} C] {D : Type c₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{max c₁ v₁ r₁}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c₁ v₁ r₁}]
  (U : C) (F : Over U ⥤ D) [F.IsContinuous (J.over U) K]
  {Bm Bn : Sheaf J CommRingCat.{max c₁ v₁ r₁}} (a : Bm ⟶ Bn)
  {Am An : Sheaf K RingCat.{max c₁ v₁ r₁}} (q : Am ⟶ An)
  (fm : ((sheafCompose J
      (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bm).over U ⟶
    (F.sheafPushforwardContinuous RingCat.{max c₁ v₁ r₁} (J.over U) K).obj Am)
  (fn : ((sheafCompose J
      (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bn).over U ⟶
    (F.sheafPushforwardContinuous RingCat.{max c₁ v₁ r₁} (J.over U) K).obj An)
  (h : fm ≫ (F.sheafPushforwardContinuous RingCat.{max c₁ v₁ r₁} (J.over U) K).map q =
    (J.overPullback RingCat.{max c₁ v₁ r₁} U).map
      ((sheafCompose J (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).map a) ≫ fn)
  (Fm : SheafOfModules.{max c₁ v₁ r₁} Am ⥤
    SheafOfModules.{max c₁ v₁ r₁} (((sheafCompose J
      (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bm).over U))
  (Fn : SheafOfModules.{max c₁ v₁ r₁} An ⥤
    SheafOfModules.{max c₁ v₁ r₁} (((sheafCompose J
      (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bn).over U))
  (αm : Fm ≅ SheafOfModules.pushforward.{max c₁ v₁ r₁} fm)
  (αn : Fn ≅ SheafOfModules.pushforward.{max c₁ v₁ r₁} fn)

private def openModuleGenerator
    (B : Sheaf J CommRingCat.{max c₁ v₁ r₁})
    (N : SheafOfModules.{max c₁ v₁ r₁}
      (((sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj B).over U))
    (W : Cᵒᵖ) (phi : W.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    ((SheafOfModules.localizedSystemExtension.{c₁, v₁, r₁} B U).obj N).val.obj W := by
  classical
  letI : ∀ psi : W.unop ⟶ U,
      Module (((sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj B).obj.obj W)
        (N.val.obj (op (Over.mk psi))) := fun psi ↦
    inferInstanceAs (Module
      ((((sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj B).over U).obj.obj
          (op (Over.mk psi))) (N.val.obj (op (Over.mk psi))))
  exact ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj B).obj)).unit.app
    ((SheafOfModules.extensionByZeroPresheaf.{max c₁ v₁ r₁}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj B) U).obj N)).app W
    (DirectSum.lof
      (((sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj B).obj.obj W)
      (W.unop ⟶ U) (fun psi ↦ N.val.obj (op (Over.mk psi))) phi x)

private theorem openModuleGenerator_eq
    (B : Sheaf J CommRingCat.{max c₁ v₁ r₁})
    (N : SheafOfModules.{max c₁ v₁ r₁}
      (((sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj B).over U))
    (W : Cᵒᵖ) (phi : W.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    openModuleGenerator.{c₁, v₁, r₁} U B N W phi x =
      SheafOfModules.RingedOpenScalar.generator.{c₁, v₁, r₁} U B N W phi x := by
  rfl

private theorem openGenerator_map
    (B : Sheaf J CommRingCat.{max c₁ v₁ r₁})
    {N N' : SheafOfModules.{max c₁ v₁ r₁}
      (((sheafCompose J
      (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj B).over U)}
    (f : N ⟶ N') (W : Cᵒᵖ) (phi : W.unop ⟶ U)
    (x : N.val.obj (op (Over.mk phi))) :
    ((SheafOfModules.localizedSystemExtension.{c₁, v₁, r₁} B U).map f).val.app W
      (SheafOfModules.RingedOpenScalar.generator.{c₁, v₁, r₁} U B N W phi x) =
    SheafOfModules.RingedOpenScalar.generator.{c₁, v₁, r₁} U B N' W phi
      (f.val.app (op (Over.mk phi)) x) := by
  have hx := congrArg (fun g ↦ g.val.app (op (Over.mk phi)) x)
    ((SheafOfModules.localizedSystemAdjunction.{c₁, v₁, r₁} B U).unit.naturality f)
  change ((SheafOfModules.localizedSystemAdjunction.{c₁, v₁, r₁} B U).unit.app N').val.app
      (op (Over.mk phi)) (f.val.app (op (Over.mk phi)) x) =
    ((SheafOfModules.localizedSystemExtension.{c₁, v₁, r₁} B U).map f).val.app W
      (((SheafOfModules.localizedSystemAdjunction.{c₁, v₁, r₁} B U).unit.app N).val.app
        (op (Over.mk phi)) x) at hx
  rw [(SheafOfModules.RingedOpenScalar.adjunctionGenerators.{c₁, v₁, r₁} U B).1,
    (SheafOfModules.RingedOpenScalar.adjunctionGenerators.{c₁, v₁, r₁} U B).1] at hx
  exact hx.symm

private def openTransport : SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q ⋙ Fm ≅
    Fn ⋙ SheafOfModules.RingedOpenScalar.sliceScalars.{c₁, v₁, r₁} U a :=
  Functor.isoWhiskerLeft (SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q) αm ≪≫
    pushforwardScalarIso F fm fn q
      ((J.overPullback RingCat.{max c₁ v₁ r₁} U).map
        ((sheafCompose J (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).map a)) h ≪≫
    Functor.isoWhiskerRight αn.symm (SheafOfModules.RingedOpenScalar.sliceScalars.{c₁, v₁, r₁} U a)

omit [HasSheafify J AddCommGrpCat.{max c₁ v₁ r₁}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c₁ v₁ r₁}] in
private theorem openTransport_apply (M : SheafOfModules.{max c₁ v₁ r₁} An)
    (W : (Over U)ᵒᵖ) (x : M.val.obj (op (F.obj W.unop))) :
    ((openTransport.{c₁, c₂, v₁, v₂, r₁} U F a q fm fn h Fm Fn αm αn).hom.app M).val.app W
        ((αm.inv.app ((SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q).obj M)).val.app W x) =
      (αn.inv.app M).val.app W x := by
  change (αn.inv.app M).val.app W
    (((pushforwardScalarIso F fm fn q _ h).hom.app M).val.app W
      ((αm.hom.app ((SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q).obj M)).val.app W
        ((αm.inv.app ((SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q).obj M)).val.app W x))) = _
  have hx := congrArg (fun f ↦ f.val.app W x)
    (Iso.inv_hom_id_app αm ((SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q).obj M))
  change (αm.hom.app ((SheafOfModules.restrictScalars q).obj M)).val.app W
    ((αm.inv.app ((SheafOfModules.restrictScalars q).obj M)).val.app W x) = x at hx
  rw [hx, pushforwardScalarIso_apply]

private def openGeneratorSpec
    (b : (sheafCompose J
      (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bm ⟶
      (sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bn)
    (ordinary : SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q ⋙
          (Fm ⋙ SheafOfModules.localizedSystemExtension.{c₁, v₁, r₁} Bm U) ≅
        (Fn ⋙ SheafOfModules.localizedSystemExtension.{c₁, v₁, r₁} Bn U) ⋙
          SheafOfModules.restrictScalars.{max c₁ v₁ r₁} b) : Prop :=
  ∀ (M : SheafOfModules.{max c₁ v₁ r₁} An) (W : Cᵒᵖ) (phi : W.unop ⟶ U),
    HEq (fun x : ((SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q).obj M).val.obj
        (op (F.obj (Over.mk phi))) ↦
      (ordinary.hom.app M).val.app W
        (openModuleGenerator.{c₁, v₁, r₁} U Bm _ W phi
          ((αm.inv.app ((SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q).obj M)).val.app
            (op (Over.mk phi)) x)))
      (fun x : M.val.obj (op (F.obj (Over.mk phi))) ↦
        openModuleGenerator.{c₁, v₁, r₁} U Bn _ W phi
          ((αn.inv.app M).val.app (op (Over.mk phi)) x))

private structure OpenScalarResult
    (b : (sheafCompose J
      (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bm ⟶
      (sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bn) where
  ordinary : SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q ⋙
          (Fm ⋙ SheafOfModules.localizedSystemExtension.{c₁, v₁, r₁} Bm U) ≅
        (Fn ⋙ SheafOfModules.localizedSystemExtension.{c₁, v₁, r₁} Bn U) ⋙
          SheafOfModules.restrictScalars.{max c₁ v₁ r₁} b
  generators : openGeneratorSpec.{c₁, c₂, v₁, v₂, r₁}
    (U := U) (F := F) (q := q) (fm := fm) (fn := fn)
    (Fm := Fm) (Fn := Fn) (αm := αm) (αn := αn) b ordinary

private theorem openScalarComparison
    (b : (sheafCompose J
      (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bm ⟶
      (sheafCompose J
        (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).obj Bn)
    (hb : (sheafCompose J
      (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).map a = b)
    (h' : fm ≫ (F.sheafPushforwardContinuous RingCat.{max c₁ v₁ r₁} (J.over U) K).map q =
      (J.overPullback RingCat.{max c₁ v₁ r₁} U).map b ≫ fn) :
    Nonempty (OpenScalarResult.{c₁, c₂, v₁, v₂, r₁}
      (U := U) (F := F) (q := q) (fm := fm) (fn := fn)
      (Fm := Fm) (Fn := Fn) (αm := αm) (αn := αn) b) := by
  have h : fm ≫ (F.sheafPushforwardContinuous RingCat.{max c₁ v₁ r₁} (J.over U) K).map q =
      (J.overPullback RingCat.{max c₁ v₁ r₁} U).map
        ((sheafCompose J
          (forget₂ CommRingCat.{max c₁ v₁ r₁} RingCat.{max c₁ v₁ r₁})).map a) ≫ fn := by
    rw [hb]
    exact h'
  obtain ⟨p, hp, e, he, _heq, _ht⟩ :=
    SheafOfModules.RingedOpenScalar.comparison.{c₁, v₁, r₁, max (c₁ + 1) (v₁ + 1) (r₁ + 1)} U a
  let ordinary := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openTransport.{c₁, c₂, v₁, v₂, r₁} U F a q fm fn h Fm Fn αm αn) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Fn e.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (Fn ⋙ SheafOfModules.localizedSystemExtension.{c₁, v₁, r₁} Bn U)
      (SheafOfModules.pushforwardCongr (F := 𝟭 C) hb)
  refine ⟨⟨ordinary, ?_⟩⟩
  intro M W phi
  apply heq_of_eq
  funext x
  simp only [openModuleGenerator_eq]
  change (e.inv.app (Fn.obj M)).val.app W
    (((SheafOfModules.localizedSystemExtension.{c₁, v₁, r₁} Bm U).map
      ((openTransport.{c₁, c₂, v₁, v₂, r₁} U F a q fm fn h Fm Fn αm αn).hom.app M)).val.app W
      (SheafOfModules.RingedOpenScalar.generator.{c₁, v₁, r₁} U Bm _ W phi
        ((αm.inv.app ((SheafOfModules.restrictScalars.{max c₁ v₁ r₁} q).obj M)).val.app
          (op (Over.mk phi)) x))) = _
  rw [openGenerator_map.{c₁, v₁, r₁}]
  erw [openTransport_apply.{c₁, c₂, v₁, v₂, r₁}]
  have hh := he (Fn.obj M) W phi ((αn.inv.app M).val.app (op (Over.mk phi)) x)
  have hc := congrArg (fun f ↦ f.val.app W
    (SheafOfModules.RingedOpenScalar.generator.{c₁, v₁, r₁} U Bn _ W phi
      ((αn.inv.app M).val.app (op (Over.mk phi)) x)))
    (Iso.hom_inv_id_app e (Fn.obj M))
  change (e.inv.app (Fn.obj M)).val.app W
    ((e.hom.app (Fn.obj M)).val.app W
      (SheafOfModules.RingedOpenScalar.generator.{c₁, v₁, r₁} U Bn _ W phi
        ((αn.inv.app M).val.app (op (Over.mk phi)) x))) = _ at hc
  exact (congrArg (fun y ↦ (e.inv.app (Fn.obj M)).val.app W y) hh).symm.trans hc

end OpenScalar

private def finiteRingMap (n : ℕ) :
    (integralCoefficientSheaf l E V n).over (IntegralOpenReduction.openObject j) ⟶
      ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        ((ProEt.topology V).over (IntegralOpenReduction.openObject j))
        (ProEt.topology X)).obj (integralCoefficientSheaf l E X n) :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    (o.finiteMap n)

private theorem finiteRingSquare (n : ℕ) : finiteRingMap l E j o (n + 1) ≫
    ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
      ((ProEt.topology V).over (IntegralOpenReduction.openObject j))
      (ProEt.topology X)).map (normalizedDVRQuotient l E X (Nat.le_succ n)) =
    (((ProEt.topology V).overPullback RingCat.{max u (t + 1)}
      (IntegralOpenReduction.openObject j)).map
        (normalizedDVRQuotient l E V (Nat.le_succ n))) ≫ finiteRingMap l E j o n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  have hq (T : Scheme.{t}) : normalizedDVRQuotient l E T (Nat.le_succ n) =
      integralCoefficientSheafTransition l E T n := by
    unfold normalizedDVRQuotient integralCoefficientSheafSystem
    exact Functor.ofOpSequence_map_homOfLE_succ _ n
  change (finiteRingMap l E j o (n + 1)).hom.app W ≫
      (normalizedDVRQuotient l E X (Nat.le_succ n)).hom.app _ =
    (normalizedDVRQuotient l E V (Nat.le_succ n)).hom.app (op W.unop.left) ≫
      (finiteRingMap l E j o n).hom.app W
  rw [hq X, hq V]
  exact congrArg ((forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map)
    (congrArg (fun k ↦ k.hom.app W) (finiteTransportSquare l E j o n))

private theorem finiteQuotient_forget (T : Scheme.{t}) (n : ℕ) :
    (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (coefficientFiniteQuotient l E T (Nat.le_succ n)) =
      normalizedDVRQuotient l E T (Nat.le_succ n) := by
  unfold coefficientFiniteQuotient
  rfl

private def finiteGenericRingMap (n : ℕ) :
    ((sheafCompose (ProEt.topology V)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (IntegralOpenReduction.rings l E V n)).over (IntegralOpenReduction.openObject j) ⟶
      ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        ((ProEt.topology V).over (IntegralOpenReduction.openObject j))
        (ProEt.topology X)).obj (integralCoefficientSheaf l E X n) :=
  finiteRingMap l E j o n

private def finiteGenericFunctor (n : ℕ) :
    SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E X n) ⥤
      SheafOfModules.{max u (t + 1)}
        (((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            (IntegralOpenReduction.rings l E V n)).over (IntegralOpenReduction.openObject j)) :=
  (o.finite n).functor

private def finiteGenericIso (n : ℕ) : finiteGenericFunctor l E j o n ≅
    SheafOfModules.pushforward.{max u (t + 1)}
      (F := IntegralOpenReduction.sliceSite j) (finiteGenericRingMap l E j o n) :=
  eqToIso (o.finiteFunctor n)

private theorem finiteGenericSquare (n : ℕ) : finiteGenericRingMap l E j o (n + 1) ≫
    ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
      ((ProEt.topology V).over (IntegralOpenReduction.openObject j))
      (ProEt.topology X)).map (normalizedDVRQuotient l E X (Nat.le_succ n)) =
      ((ProEt.topology V).overPullback RingCat.{max u (t + 1)}
        (IntegralOpenReduction.openObject j)).map
          (normalizedDVRQuotient l E V (Nat.le_succ n)) ≫ finiteGenericRingMap l E j o n :=
  finiteRingSquare l E j o n

set_option linter.defProp false in
@[instance_reducible] private def nativeRings (n : ℕ) :=
    @openScalarComparison.{t + 1, t + 1, t, t, max u (t + 1)}
      V.ProEt inferInstance X.ProEt inferInstance (ProEt.topology V) (ProEt.topology X)
      (IntegralOpenReduction.openAbSheafify.{t, u} (X := V))
      (IntegralOpenReduction.openAbLocallyBijective.{t, u} (X := V))
      (IntegralOpenReduction.openObject j)
      (IntegralOpenReduction.sliceSite j)
      (cbcSliceFunctor_continuous V (IntegralOpenReduction.openObject j))
      (IntegralOpenReduction.rings l E V (n + 1)) (IntegralOpenReduction.rings l E V n)
      (coefficientFiniteQuotient l E V (Nat.le_succ n))
      (integralCoefficientSheaf l E X (n + 1)) (integralCoefficientSheaf l E X n)
      (normalizedDVRQuotient l E X (Nat.le_succ n))

set_option linter.defProp false in
@[instance_reducible] private def nativeMaps (n : ℕ) :=
  nativeRings l E j n
    (finiteGenericRingMap l E j o (n + 1)) (finiteGenericRingMap l E j o n)

set_option linter.defProp false in
@[instance_reducible] private def nativeFunctors (n : ℕ) :=
  nativeMaps l E j o n
    (finiteGenericFunctor l E j o (n + 1)) (finiteGenericFunctor l E j o n)

set_option linter.defProp false in
@[instance_reducible] private def nativeIsos (n : ℕ) :=
  nativeFunctors l E j o n (finiteGenericIso l E j o (n + 1)) (finiteGenericIso l E j o n)

set_option linter.defProp false in
@[instance_reducible] private def nativeQuotient (n : ℕ) :=
  nativeIsos l E j o n
    (normalizedDVRQuotient l E V (Nat.le_succ n)) (finiteQuotient_forget l E V n)

set_option linter.defProp false in
@[instance_reducible] private def nativeComparison (n : ℕ) :=
  nativeQuotient l E j o n (finiteGenericSquare l E j o n)

private def genericResult (n : ℕ) :=
  Classical.choice (nativeComparison l E j o n)

private def genericOrdinary (n : ℕ) :=
  @OpenScalarResult.ordinary.{t + 1, t + 1, t, t, max u (t + 1)}
    V.ProEt inferInstance X.ProEt inferInstance (ProEt.topology V) (ProEt.topology X)
    (IntegralOpenReduction.openAbSheafify.{t, u} (X := V))
    (IntegralOpenReduction.openAbLocallyBijective.{t, u} (X := V))
    (IntegralOpenReduction.openObject j) (IntegralOpenReduction.sliceSite j)
    (cbcSliceFunctor_continuous V (IntegralOpenReduction.openObject j))
    (IntegralOpenReduction.rings l E V (n + 1)) (IntegralOpenReduction.rings l E V n)
    (integralCoefficientSheaf l E X (n + 1)) (integralCoefficientSheaf l E X n)
    (normalizedDVRQuotient l E X (Nat.le_succ n))
    (finiteGenericRingMap l E j o (n + 1)) (finiteGenericRingMap l E j o n)
    (finiteGenericFunctor l E j o (n + 1)) (finiteGenericFunctor l E j o n)
    (finiteGenericIso l E j o (n + 1)) (finiteGenericIso l E j o n)
    (normalizedDVRQuotient l E V (Nat.le_succ n)) (genericResult l E j o n)

set_option linter.defProp false in
private def genericGenerators (n : ℕ) :=
  @OpenScalarResult.generators.{t + 1, t + 1, t, t, max u (t + 1)}
    V.ProEt inferInstance X.ProEt inferInstance (ProEt.topology V) (ProEt.topology X)
    (IntegralOpenReduction.openAbSheafify.{t, u} (X := V))
    (IntegralOpenReduction.openAbLocallyBijective.{t, u} (X := V))
    (IntegralOpenReduction.openObject j) (IntegralOpenReduction.sliceSite j)
    (cbcSliceFunctor_continuous V (IntegralOpenReduction.openObject j))
    (IntegralOpenReduction.rings l E V (n + 1)) (IntegralOpenReduction.rings l E V n)
    (integralCoefficientSheaf l E X (n + 1)) (integralCoefficientSheaf l E X n)
    (normalizedDVRQuotient l E X (Nat.le_succ n))
    (finiteGenericRingMap l E j o (n + 1)) (finiteGenericRingMap l E j o n)
    (finiteGenericFunctor l E j o (n + 1)) (finiteGenericFunctor l E j o n)
    (finiteGenericIso l E j o (n + 1)) (finiteGenericIso l E j o n)
    (normalizedDVRQuotient l E V (Nat.le_succ n)) (genericResult l E j o n)

private def genericPointIso (n : ℕ) (M : normalizedDVRModules l E X n) :=
  (genericOrdinary l E j o n).app M

set_option linter.defProp false in
private def genericNaturality (n : ℕ) {M N : normalizedDVRModules l E X n} (f : M ⟶ N) :=
  (genericOrdinary l E j o n).hom.naturality f

private def nativePointIso (n : ℕ) (M : normalizedDVRModules l E X n) :
    (SheafOfModules.localizedSystemExtension.{t + 1, t, max u (t + 1)}
        (IntegralOpenReduction.rings l E V (n + 1)) (IntegralOpenReduction.openObject j)).obj
      ((o.finite (n + 1)).functor.obj
        ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M)) ≅
    (normalizedDVRModuleRes l E V (Nat.le_succ n)).obj
      ((SheafOfModules.localizedSystemExtension.{t + 1, t, max u (t + 1)}
        (IntegralOpenReduction.rings l E V n) (IntegralOpenReduction.openObject j)).obj
          ((o.finite n).functor.obj M)) :=
  genericPointIso l E j o n M

private theorem nativePointNaturality (n : ℕ)
    {M N : normalizedDVRModules l E X n} (f : M ⟶ N) :
    (SheafOfModules.localizedSystemExtension.{t + 1, t, max u (t + 1)}
        (IntegralOpenReduction.rings l E V (n + 1)) (IntegralOpenReduction.openObject j)).map
      ((o.finite (n + 1)).functor.map
        ((normalizedDVRModuleRes l E X (Nat.le_succ n)).map f)) ≫
          (nativePointIso l E j o n N).hom =
    (nativePointIso l E j o n M).hom ≫
      (normalizedDVRModuleRes l E V (Nat.le_succ n)).map
        ((SheafOfModules.localizedSystemExtension.{t + 1, t, max u (t + 1)}
          (IntegralOpenReduction.rings l E V n) (IntegralOpenReduction.openObject j)).map
            ((o.finite n).functor.map f)) :=
  genericNaturality l E j o n f

private def nativeOrdinary (n : ℕ) :
    normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        IntegralOpenReduction.finiteExtension l E j o (n + 1) ≅
      IntegralOpenReduction.finiteExtension l E j o n ⋙
        normalizedDVRModuleRes l E V (Nat.le_succ n) :=
  NatIso.ofComponents (nativePointIso l E j o n) (nativePointNaturality l E j o n)

/-- The consecutive open scalar comparison, constructed from the coefficient-system map.
Source: Stacks 03DI, 03DA and 0E8I; parent Steps 1 and 2.
(blueprint: lem-sf-integral-open-scalar-restriction-comparison).

The horizontal naturality square of the system ring map gives the finite transport
square. Continuous pushforward composition and congruence carry sections identically.
Compose this transport with the inverse scalar/open comparison and the explicit
forgetful coefficient identifications. Their generator formulas prove the asserted
normalization, including for n=0, zero modules and the empty open. -/
theorem integralOpenScalarRestrictionComparison (n : ℕ) :
    ∃ ordinary : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
          IntegralOpenReduction.finiteExtension l E j o (n + 1) ≅
        IntegralOpenReduction.finiteExtension l E j o n ⋙
          normalizedDVRModuleRes l E V (Nat.le_succ n),
      ∀ (M : normalizedDVRModules l E X n) (W : V.ProEt)
        (a : W ⟶ IntegralOpenReduction.openObject j),
        HEq (fun x : ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M).val.obj
            (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
          (ordinary.hom.app M).val.app (op W)
            (IntegralOpenReduction.finiteExtensionSection l E j o (n + 1)
              ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) W a x))
          (fun x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
            IntegralOpenReduction.finiteExtensionSection l E j o n M W a x) := by
  refine ⟨nativeOrdinary l E j o n, ?_⟩
  intro M W a
  exact (genericGenerators l E j o n) M (op W) a

end WeilConjectures
