/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions

import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantOpenRestrictionModelComparison
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Ordinary coefficient transport for the open factor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
open AlgebraicGeometry.ProEtale.VaryingRing
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] openMapContinuous

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private local instance sliceContinuous : (IntegralOpenReduction.sliceSite j).IsContinuous
    ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U) :=
  IntegralOpenReduction.sliceContinuous j

private def completedTranspose :=
  (((openAdj j).sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U) (ProEt.topology X)).homEquiv _ _).symm
      (sfCompletedCoefficientMap l E j)

private instance completedTransposeIso : IsIso (completedTranspose l E j) := by
  have : IsIso (((proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _).symm
      (sfCompletedCoefficientMap l E j)) := completedPullMap_isIso l E j
  exact iso_inverse_transpose _ (proEtaleSheafAdjunction j CommRingCat.{u + 1}) _

private theorem completedTranspose_projection (n : ℕ) :
    completedTranspose l E j ≫ completedIntegralCommRingProjectionUnrestricted l E U n =
      ((openMap j).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology X)).map
          (completedIntegralCommRingProjectionUnrestricted l E X n) ≫
        openConstantTranspose j
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let a := (openAdj j).sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U) (ProEt.topology X)
  refine (a.homEquiv_naturality_right_symm (sfCompletedCoefficientMap l E j)
    (completedIntegralCommRingProjectionUnrestricted l E U n)).symm.trans ?_
  exact (congrArg (a.homEquiv _ _).symm
    ((sfCompletedCoefficientMap_existsUnique l E j).exists.choose_spec n)).trans
      (a.homEquiv_naturality_left_symm
        (completedIntegralCommRingProjectionUnrestricted l E X n) _)

private theorem finiteMap_eq (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    o.finiteMap n = sfCbcConstantSliceMap X (IntegralOpenReduction.openObject j)
      (Padic.coefficientExtensionRing l E (n + 1)) := by
  apply (sfCbcConstantSliceMap_existsUnique X (IntegralOpenReduction.openObject j)
    (Padic.coefficientExtensionRing l E (n + 1))).unique
  · exact o.finiteConstants n
  · exact (sfCbcConstantSliceMap_existsUnique X (IntegralOpenReduction.openObject j)
      (Padic.coefficientExtensionRing l E (n + 1))).exists.choose_spec

private theorem completedMap_eq (o : IntegralOpenReduction.Operations l E j) :
    o.completedMap =
      (Functor.sheafPushforwardContinuousNatTrans (openSliceForgetIso j).inv
        CommRingCat.{u + 1} ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
          (ProEt.topology X)).app (completedIntegralCommRingSheafUnrestricted l E X) ≫
      ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U)).map
          (completedTranspose l E j) := by
  let F := (IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{u + 1}
    ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U)
  let H := sheafCompose ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have hpSource : PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology U) RingCat.{u + 1}) := inferInstance
  have hpWhisker : PreservesLimitsOfShape ℕᵒᵖ
      ((Functor.whiskeringLeft _ _ RingCat.{u + 1}).obj
        (IntegralOpenReduction.sliceSite j).op) :=
    CategoryTheory.whiskeringLeft_preservesLimitsOfShape ℕᵒᵖ _
  have hpComposite : PreservesLimitsOfShape ℕᵒᵖ (F ⋙ sheafToPresheaf
      ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) RingCat.{u + 1}) := by
    change PreservesLimitsOfShape ℕᵒᵖ (sheafToPresheaf (ProEt.topology U) RingCat.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ RingCat.{u + 1}).obj (IntegralOpenReduction.sliceSite j).op)
    exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ hpSource hpWhisker
  have hpF : PreservesLimitsOfShape ℕᵒᵖ F :=
    @preservesLimitsOfShape_of_reflects_of_preserves _ _ _ _ _ _ _ _ F
      (sheafToPresheaf _ _) hpComposite inferInstance
  apply H.map_injective
  apply (@isLimitOfPreserves _ _ _ _ _ _ _ F _
    (limit.isLimit (integralCoefficientSheafSystem l E U)) hpF.preservesLimit).hom_ext
  intro n
  let Q := completedIntegralCommRingProjectionUnrestricted l E U n.unop
  let FC := (IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous
    CommRingCat.{u + 1} ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
      (ProEt.topology U)
  have hproj : F.map (limit.π (integralCoefficientSheafSystem l E U) n) =
      H.map (FC.map Q) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    rfl
  let ψ := (Functor.sheafPushforwardContinuousNatTrans (openSliceForgetIso j).inv
    CommRingCat.{u + 1} ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
      (ProEt.topology X)).app (completedIntegralCommRingSheafUnrestricted l E X) ≫
        FC.map (completedTranspose l E j)
  change H.map o.completedMap ≫ F.map (limit.π (integralCoefficientSheafSystem l E U) n) =
    H.map ψ ≫ F.map (limit.π (integralCoefficientSheafSystem l E U) n)
  have hcomm : o.completedMap ≫ FC.map Q = ψ ≫ FC.map Q := by
    have h := o.projections n.unop
    erw [finiteMap_eq l E j o n.unop, ← openSliceCoefficient j
      (Padic.coefficientExtensionRing l E (n.unop + 1))] at h
    erw [h]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have hc := congrArg (fun f ↦ f.hom.app
      (op ((IntegralOpenReduction.sliceSite j).obj V.unop)))
        (completedTranspose_projection l E j n.unop)
    have hn := (completedIntegralCommRingProjectionUnrestricted l E X n.unop).hom.naturality
      ((openSliceForgetIso j).inv.app V.unop).op
    change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
    let b := (openConstantTranspose j
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n.unop + 1))))).hom.app
        (op ((IntegralOpenReduction.sliceSite j).obj V.unop))
    let a := (completedIntegralCommRingSheafUnrestricted l E X).obj.map
      ((openSliceForgetIso j).inv.app V.unop).op
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ b) hn.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f ↦ a ≫ f) hc.symm).trans (Category.assoc _ _ _).symm)))
  exact (congrArg (fun t ↦ H.map o.completedMap ≫ t) hproj).trans
    ((H.map_comp o.completedMap (FC.map Q)).symm.trans
      ((congrArg H.map hcomm).trans
        ((H.map_comp ψ (FC.map Q)).trans (congrArg (fun t ↦ H.map ψ ≫ t) hproj.symm))))

private def restrictionToSlice (o : IntegralOpenReduction.Operations l E j) :
    proEtaleRingModulePullback j ((completed l E).ring X) ((completed l E).ring U)
      ((completed l E).pull j) ⋙ o.integral.functor ≅
        SheafOfModules.localizedSystemRestriction.{u+1, u, u+1}
          (completedIntegralCommRingSheafUnrestricted l E X)
          (IntegralOpenReduction.openObject j) := by
  let S := IntegralOpenReduction.sliceSite j
  let G := openMap j
  let W := IntegralOpenReduction.openObject j
  let RX := completedIntegralCoefficientSheafUnrestricted l E X
  let RU := completedIntegralCoefficientSheafUnrestricted l E U
  let sliceCont : (S).IsContinuous
      ((ProEt.topology X).over W) (ProEt.topology U) :=
    IntegralOpenReduction.sliceContinuous j
  let compCont : (S ⋙ G).IsContinuous
      ((ProEt.topology X).over W) (ProEt.topology X) := openSliceCompContinuous j
  let c := completedTranspose l E j
  have hc : IsIso c := completedTransposeIso l E j
  let cR : ((openMap j).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X)).obj RX ≅ RU :=
    (sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (asIso c)
  have hcR : IsIso cR.hom := cR.isIso_hom
  let rho : RX ⟶ ((proEtaleBaseChange j).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology X) (ProEt.topology U)).obj RU :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (sfCompletedCoefficientMap l E j)
  have hd : cR.hom = (((openAdj j).sheafPushforwardContinuous
      (E := RingCat.{u + 1}) (ProEt.topology U) (ProEt.topology X)).homEquiv _ _).symm
        rho := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext Z
    rfl
  have hrho : proEtaleRingDirectImageMap j ((completed l E).ring X)
      ((completed l E).ring U) ((completed l E).pull j) =
        sfCompletedCoefficientMap l E j := by
    exact ((proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  let adj : SheafOfModules.pushforward.{u + 1} cR.inv ⊣
      proEtaleRingModuleDirectImage j ((completed l E).ring X) ((completed l E).ring U)
        ((completed l E).pull j) := by
    have a := moduleAdjOfSiteAdj' (ProEt.topology U) (ProEt.topology X)
      (openAdj j) rho cR.hom hd
    have a' := a.ofNatIsoLeft (SheafOfModules.pushforwardCongr
      (IsIso.inv_eq_of_hom_inv_id cR.hom_inv_id))
    apply a'.ofNatIsoRight
    apply SheafOfModules.pushforwardCongr
    exact congrArg (fun f ↦ (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f) hrho.symm
  let e := (proEtaleRingModulePullbackAdjunction j ((completed l E).ring X)
    ((completed l E).ring U) ((completed l E).pull j)).leftAdjointUniq adj
  let phi : RX.over W ⟶ ((S).sheafPushforwardContinuous
      RingCat.{u + 1} ((ProEt.topology X).over W) (ProEt.topology U)).obj RU :=
    (sheafCompose ((ProEt.topology X).over W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map o.completedMap
  let alpha := (Functor.sheafPushforwardContinuousNatTrans (openSliceForgetIso j).inv
    RingCat.{u + 1} ((ProEt.topology X).over W) (ProEt.topology X)).app RX
  have hphi : phi = alpha ≫
      ((S).sheafPushforwardContinuous RingCat.{u + 1}
        ((ProEt.topology X).over W) (ProEt.topology U)).map cR.hom := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext Z
    exact congrArg (fun f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (f.hom.app Z)) (completedMap_eq l E j o)
  have hcomp :
      phi ≫ ((S).sheafPushforwardContinuous RingCat.{u + 1}
        ((ProEt.topology X).over W) (ProEt.topology U)).map cR.inv = alpha := by
    erw [hphi, Category.assoc, ← Functor.map_comp, cR.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  let T := @SheafOfModules.pushforward.{u + 1} _ _ _ _
    ((ProEt.topology X).over W) (ProEt.topology U) S _ _ sliceCont phi
  have eo : o.integral.functor ≅ T := eqToIso o.integralFunctor
  let ecomp := @SheafOfModules.pushforwardComp.{u + 1} _ _ _ _ _ _
    ((ProEt.topology X).over W) (ProEt.topology U) S _ _ sliceCont phi
    (ProEt.topology X) G _ (openMapContinuous j) cR.inv
  let econgr := SheafOfModules.pushforwardCongr₂.{u + 1}
    (F := S ⋙ G) (G := Over.forget W)
    (J := (ProEt.topology X).over W) (K := ProEt.topology X)
    (φ := 𝟙 (RX.over W))
    (ψ := phi ≫ ((S).sheafPushforwardContinuous
      RingCat.{u + 1} ((ProEt.topology X).over W) (ProEt.topology U)).map cR.inv)
    (openSliceForgetIso j).symm (by
      exact (Category.id_comp _).trans hcomp.symm)
  exact Functor.isoWhiskerLeft _ eo ≪≫
    Functor.isoWhiskerRight e T ≪≫ ecomp ≪≫ econgr.symm

set_option linter.unusedVariables false in
/-- The normalized slice operations and the published ordinary open operations agree.
Source: Stacks 03DI, 03DJ, 098K, 0941; blueprint proposition-composition-base-change-rf-shriek--1,
open factor. (blueprint: lem-sf-open-factor-ordinary-transport).

Proof: the finite coefficient maps in o are determined by their constant-section
formulas: sheafification of the constant presheaf is left adjoint to inclusion.
They are therefore the canonical slice coefficient maps. Compose o.projections with
each finite quotient. Joint monicity of the projections of the completed coefficient
limit then identifies o.completedMap with the canonical completed slice map. The
formula o.integralFunctor now identifies its functor with the concrete pushforward
along the slice-to-open site equivalence. The published ringed restriction, after
this equivalence, is ordinary slice restriction; the coefficient identification is
the same one just proved. This gives the restriction comparison. Both extension
functors are left adjoint to this restriction, so uniqueness of left adjoints gives
the extension comparison. These are isomorphisms before applying complexes or localization.
All constructions remain valid for empty and identity opens, and use no boundedness
or completeness assumption. -/
theorem openFactorOrdinaryTransport
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) :
    ∃ e : IntegralOpenReduction.extension l E j o ≅ openExtension (completed l E) j,
      Nonempty (IntegralOpenReduction.restriction l E j o ≅
        proEtaleRingModulePullback j ((completed l E).ring X)
          ((completed l E).ring U) ((completed l E).pull j)) := by
  let P := proEtaleRingModulePullback j ((completed l E).ring X)
    ((completed l E).ring U) ((completed l E).pull j)
  let r : IntegralOpenReduction.restriction l E j o ≅ P :=
    Functor.isoWhiskerRight (restrictionToSlice l E j o).symm o.integral.inverse ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft P o.integral.unitIso.symm ≪≫ Functor.rightUnitor P
  exact ⟨((IntegralOpenReduction.ordinaryAdjunction l E j o).ofNatIsoRight r).leftAdjointUniq
    (PurCompactSupport.openAdjunction (completed l E) j), ⟨r⟩⟩

end WeilConjectures.OpenFactorCoherence
