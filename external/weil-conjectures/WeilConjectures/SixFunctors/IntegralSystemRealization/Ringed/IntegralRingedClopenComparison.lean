/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import WeilConjectures.AlgebraicGeometry.Clopen.ClopenScalarRestrictionReverseAdjunction
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement

/-! # The canonical clopen comparison

Source: Stacks 03DI, 09AE; fix-prop-coherence, clopen comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  SheafOfModules.localizedSystemExtensionAdditive SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
/-- The actual open unit is invertible on every ambient derived object.
Source: Stacks 03DI (blueprint: lem-sf-integral-ringed-clopen-comparison). -/
theorem integralRingedOpenUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (ringedOpenAdj l E j).unit := by
  let R := PurCompactSupport.completed l E
  obtain ⟨e, ⟨he⟩⟩ := PurCompactSupport.openExtension_derivedSlicePresentation R j
  let L := (SheafOfModules.localizedModuleExtension.{u} (R.ring X)
    (ProEt.mk j)).mapDerivedCategory
  let adjL := SheafOfModules.localizedModuleDerivedAdjunction.{u} (R.ring X) (ProEt.mk j)
  let : IsIso adjL.unit := SheafOfModules.localizedDerivedUnit_isIso j (R.ring X)
  let : L.Full := adjL.fullyFaithfulLOfIsIsoUnit.full
  let : L.Faithful := adjL.fullyFaithfulLOfIsIsoUnit.faithful
  let : (ringedOpen l E j).Full := Functor.Full.of_iso he.symm
  let : (ringedOpen l E j).Faithful := Functor.Faithful.of_iso he.symm
  exact (ringedOpenAdj l E j).unit_isIso_of_L_fully_faithful

/-- Transpose of the inverse actual open unit under geometric direct image.
Source: Stacks 03DI (blueprint: lem-sf-integral-ringed-clopen-comparison). -/
def integralRingedClopenMap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ringedOpen l E j ⟶ ringedPush l E j := by
  letI := integralRingedOpenUnit_isIso l E j
  let v := (asIso (ringedOpenAdj l E j).unit).inv
  exact
    { app M := (ringedAdj l E j).homEquiv _ _ (v.app M)
      naturality {M N} f := by
        rw [← Adjunction.homEquiv_naturality_left,
          ← Adjunction.homEquiv_naturality_right]
        exact congrArg ((ringedAdj l E j).homEquiv _ _) (v.naturality f) }

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  SheafOfModules.localizedSystemExtensionAdditive SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem ordinaryClopenReverse {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S) :
    Nonempty (proEtaleRingModulePullback j R S c ⊣ proEtaleRingOpenExtension j R S c) := by
  let G := proEtaleOpenComposition j
  let F := proEtaleBaseChange j
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U) (ProEt.topology X)
  let e := ((proEtaleSheafAdjunction j CommRingCat.{u + 1}).leftAdjointUniq b).app R
  let d := c.symm ≪≫ e
  let ψ := proEtaleRingDirectImageMap j R S c
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ F.op.whiskerLeft d.hom.hom := by
    have h : (proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _
        (c.hom ≫ d.hom) = b.unit.app R := by
      simp only [d, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
      exact Adjunction.homEquiv_leftAdjointUniq_hom_app
        (proEtaleSheafAdjunction j CommRingCat.{u + 1}) b R
    rw [Adjunction.homEquiv_naturality_right] at h
    exact (congrArg (fun z ↦ z.hom) h).symm
  have H₂ : d.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (d.hom.hom.app V)).mp
    dsimp
    rw [Category.id_comp]
    have hn := d.hom.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun z ↦ z.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (d.hom.hom.app (F.op.obj (G.op.obj V)))
      (R.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change d.hom.hom.app V ≫ R.obj.map (𝟙 (G.op.obj V)) = d.hom.hom.app V
    exact (congrArg (fun f ↦ d.hom.hom.app V ≫ f)
      (R.obj.map_id (G.op.obj V))).trans (Category.comp_id _)
  let Rr := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let Sr := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let φr : Sr ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X)).obj Rr :=
    (sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map d.hom
  let ψr : Rr ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology X) (ProEt.topology U)).obj Sr :=
    ⟨Functor.whiskerRight ψ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁r : Functor.whiskerRight (NatTrans.op a.counit) Rr.obj =
      ψr.hom ≫ F.op.whiskerLeft φr.hom := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (z.app V)) H₁
  have H₂r : φr.hom ≫ G.op.whiskerLeft ψr.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) Sr.obj = 𝟙 Sr.obj := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (z.app V)) H₂
  let ar := SheafOfModules.pushforwardPushforwardAdj a φr ψr H₁r H₂r
  let p := (proEtaleRingModuleAdjunction j R S c).leftAdjointUniq ar
  let ao := (Adjunction.ofIsRightAdjoint
    (proEtaleRingModulePullback j R S c)).ofNatIsoRight p
  obtain ⟨rev⟩ := clopenScalarRestrictionReverseAdjunction j R S d
    (proEtaleRingOpenExtension j R S c) ao
  exact ⟨rev.ofNatIsoLeft p.symm⟩

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  SheafOfModules.localizedSystemExtensionAdditive SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
/-- On a clopen immersion the inverse-unit transpose is invertible.
Source: Stacks 03DI, 09AE; fix-prop-coherence, clopen step
(blueprint: lem-sf-integral-ringed-clopen-comparison).

Proof: a clopen immersion partitions every pro-etale test object into its inverse
image in the open and its complementary clopen piece. Modules supported on the
open vanish on the complement, so extension by zero and direct image have the
same sections, coefficient action and restriction maps. The section identity is
an exact natural isomorphism. Its pullback composite is the inverse open unit;
transpose under pullback/direct-image adjunction therefore identifies it with
the displayed map. Exact localization identifies direct image with its right
derived functor, preserving that adjunction and transpose. Consequently this
isomorphism is integralRingedClopenMap. For the empty open both functors are zero;
for the identity open the formula is the inverse-unit transpose as well. -/
theorem integralRingedClopenMap_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] :
    IsIso (integralRingedClopenMap l E j) := by
  let R := PurCompactSupport.completed l E
  obtain ⟨ar⟩ := ordinaryClopenReverse j (R.ring X) (R.ring U) (R.pull j)
  let rev : ringedPull l E j ⊣ ringedOpen l E j := ar.mapExactDerivedCategory
  let e := rev.rightAdjointUniq (ringedAdj l E j)
  have := integralRingedOpenUnit_isIso l E j
  let ff := (ringedOpenAdj l E j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (ringedPush l E j).Full := Functor.Full.of_iso e
  have : (ringedPush l E j).Faithful := Functor.Faithful.of_iso e
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : IsIso ((ringedAdj l E j).unit.app ((ringedOpen l E j).obj M)) :=
    (ringedAdj l E j).isIso_unit_app_of_iso (e.app M)
  change IsIso ((ringedAdj l E j).homEquiv _ _
    ((asIso (ringedOpenAdj l E j).unit).inv.app M))
  rw [Adjunction.homEquiv_unit]
  infer_instance

end WeilConjectures.IntegralSystemRealization
