/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemCompositorAssociativity
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.CategoryTheory.AdjunctionSquareComposition
/-! Identity normalization data for the system pullback compositor.
Source: Stacks 07A7, 0F7C; blueprint fix-prop-coherence.
(blueprint: lem-sf-system-push-identity-pair-pull-unit).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem identity_bridge {C : Type*} [Category C]
    {F₁ F₂ G₁ G₂ : C ⥤ C} (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂)
    (b : G₁ ≅ G₂) (e : G₂ ≅ 𝟭 C) :
    Adjunction.leftAdjointIdIso a₁ (b ≪≫ e) =
      (a₁.ofNatIsoRight b).leftAdjointUniq a₂ ≪≫ Adjunction.leftAdjointIdIso a₂ e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (a₁.homEquiv X X).injective
  simp [Adjunction.leftAdjointIdIso, Adjunction.leftAdjointUniq,
    conjugateIsoEquiv_symm_apply_inv, conjugateEquiv_symm_apply_app,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private def ordinaryId {o : Operations l E} (b : CanonicalBridge l E o) (X : Scheme.{u}) :
    pullbackTensorSequenceDirect l E (𝟙 X) ≅ 𝟭 (coefficientSequenceModules l E X) :=
  b.ordinary (𝟙 X) ≪≫
    (ProEtale.SemilinearProperOpen.pushId_existsUnique
      (scalarRings l E) (scalarTransitions l E) X).choose

private theorem ordinaryId_sections {o : Operations l E} (b : CanonicalBridge l E o)
    (X : Scheme.{u}) (M : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEt)
    (x : ((pullbackTensorSequenceDirect l E (𝟙 X)).obj M).val.obj (op (n, U))) :
    ((ordinaryId l E b X).hom.app M).val.app (op (n, U)) x =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ X).inv.app U)).op x := by
  change (((ProEtale.SemilinearProperOpen.pushId_existsUnique
    (scalarRings l E) (scalarTransitions l E) X).choose).hom.app M).val.app (op (n, U))
      (((b.ordinary (𝟙 X)).hom.app M).val.app (op (n, U)) x) = _
  erw [b.sections]
  exact (ProEtale.SemilinearProperOpen.pushId_existsUnique
    (scalarRings l E) (scalarTransitions l E) X).choose_spec.1 M n U x

private theorem ordinary_direct_left_unit {o : Operations l E}
    (c : Compositors l E o) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    c.ordinaryDirect (𝟙 X) f ≪≫
        eqToIso (congrArg (pullbackTensorSequenceDirect l E) (Category.id_comp f)) =
      Functor.isoWhiskerRight (ordinaryId l E b X) (pullbackTensorSequenceDirect l E f) ≪≫
        Functor.leftUnitor (pullbackTensorSequenceDirect l E f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [direct_map_apply l E f ((ordinaryId l E b X).hom.app M) n U]
  erw [ordinaryId_sections l E b X M n ((proEtaleBaseChange f).obj U)]
  erw [direct_transport l E (Category.id_comp f) M n U]
  erw [c.sections (𝟙 X) f M n U]
  erw [← PresheafOfModules.map_comp_apply, ← op_comp]
  apply ProEtale.StrictTower.restriction_eq M.val
  apply Prod.hom_ext
  · simp
  · exact ProEtale.StrictTower.site_left_unit (P := @WeaklyEtale) (Q := ⊤) f U

private theorem ordinary_pull_left_unit {o : Operations l E}
    (c : Compositors l E o) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    eqToIso (congrArg (pullbackTensorSequenceInverse l E) (Category.id_comp f).symm) ≪≫
      c.ordinaryPull (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (pullbackTensorSequenceInverse l E f)
        (Adjunction.leftAdjointIdIso (pullbackTensorSequenceAdjunction l E (𝟙 X))
          (ordinaryId l E b X)) ≪≫
      Functor.rightUnitor (pullbackTensorSequenceInverse l E f) = Iso.refl _ := by
  have h := Adjunction.leftAdjointCompIso_comp_id (pullbackTensorSequenceAdjunction l E f)
    (pullbackTensorSequenceAdjunction l E (𝟙 X))
    (c.ordinaryDirect (𝟙 X) f ≪≫
      eqToIso (congrArg (pullbackTensorSequenceDirect l E) (Category.id_comp f)))
    (ordinaryId l E b X) (ordinary_direct_left_unit l E c b f)
  rw [ProEtale.StrictTower.mate_transport (pullbackTensorSequenceInverse l E)
    (pullbackTensorSequenceDirect l E) (fun t ↦ pullbackTensorSequenceAdjunction l E t)
    (pullbackTensorSequenceAdjunction l E f) (pullbackTensorSequenceAdjunction l E (𝟙 X))
    (Category.id_comp f) (c.ordinaryDirect (𝟙 X) f)] at h
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hi := congr_app (congrArg Iso.inv h) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at hi
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Iso.refl_hom, NatTrans.id_app]
  rw [← Category.assoc]
  rw [ordinaryPull_eq l E c]
  change _ ≫ ((Adjunction.leftAdjointCompIso _ _ _ _).symm).hom.app M = _ at hi
  simp only [Iso.symm_hom, eqToIso.inv, eqToIso.hom] at hi ⊢
  rw [hi]
  erw [Category.comp_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

/-- The normalized pullback identity and its bridge mate. This is the inverse-image
part of the identity-pair calculation; direct-image components are not asserted.
Source: Stacks 07A7, 0F7C; blueprint fix-prop-coherence.
(blueprint: lem-sf-system-push-identity-pair-pull-unit).

Proof: sectionwise identity normalization determines the ordinary direct-image identity;
localization and adjoint conjugation produce the displayed pullback unit and bridge mate.
-/
theorem systemPushIdentityPullUnit (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) (X : Scheme.{u}) :
    ∃ e : pull l E (𝟙 X) ≅ 𝟭 (System l E X),
      eqToIso (congrArg (pull l E) (Category.id_comp (𝟙 X)).symm) ≪≫
          c.pullComp (𝟙 X) (𝟙 X) ≪≫
          Functor.isoWhiskerLeft (pull l E (𝟙 X)) e ≪≫
          Functor.rightUnitor (pull l E (𝟙 X)) = Iso.refl _ ∧
      conjugateIsoEquiv (o.direct (𝟙 X)).adj Adjunction.id e.symm =
        b.push l E (𝟙 X) ≪≫
          ProEtale.SemilinearProperOpen.sId (scalarRings l E)
            (scalarTransitions l E) X := by
  let e₀ := Adjunction.leftAdjointIdIso (pullbackTensorSequenceAdjunction l E (𝟙 X))
    (ordinaryId l E b X)
  let e : pull l E (𝟙 X) ≅ 𝟭 (System l E X) :=
    Functor.mapDerivedCategoryNatIso e₀ ≪≫ Functor.mapDerivedCategoryIdIso _
  refine ⟨e, ?_, ?_⟩
  · have hh := ProEtale.StrictTower.descend_left_unit
      (pullbackTensorSequenceInverse l E (𝟙 X))
      (pullbackTensorSequenceInverse l E (𝟙 X ≫ 𝟙 X))
      (pullbackTensorSequenceInverse l E (𝟙 X))
      (eqToIso (congrArg (pullbackTensorSequenceInverse l E) (Category.id_comp (𝟙 X)).symm))
      (c.ordinaryPull (𝟙 X) (𝟙 X)) e₀ (ordinary_pull_left_unit l E c b (𝟙 X))
    rw [derived_transport l E (Category.id_comp (𝟙 X)).symm] at hh
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hm := congr_app hh M
    simp only [pullComp_eq, e, pull, pullbackTensorSequenceDerived, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Iso.refl_hom, NatTrans.id_app, Category.assoc]
    dsimp only [Functor.comp_obj, Functor.id_obj, NatTrans.id_app] at hm ⊢
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
      Category.comp_id, Functor.map_comp, Iso.symm_hom] using hm
  · have he : e = b.pull l E (𝟙 X) ≪≫
        ProEtale.SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) X := by
      have := ProEtale.SemilinearProperOpen.pull_additive
        (scalarRings l E) (scalarTransitions l E) (𝟙 X)
      have := ProEtale.SemilinearProperOpen.pull_limits
        (scalarRings l E) (scalarTransitions l E) (𝟙 X)
      have := ProEtale.SemilinearProperOpen.pull_colimits
        (scalarRings l E) (scalarTransitions l E) (𝟙 X)
      dsimp only [e, e₀, ordinaryId]
      rw [identity_bridge (pullbackTensorSequenceAdjunction l E (𝟙 X))
        (ProEtale.SemilinearProperOpen.ordinaryAdj
          (scalarRings l E) (scalarTransitions l E) (𝟙 X))]
      apply Iso.ext
      simp only [CanonicalBridge.pull, ProEtale.SemilinearProperOpen.pId, Iso.trans_hom]
      erw [Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
      rfl
    rw [he, Iso.trans_symm, CategoryTheory.conjugateIso_trans]
    rfl
end WeilConjectures.IntegralSystemRealization
