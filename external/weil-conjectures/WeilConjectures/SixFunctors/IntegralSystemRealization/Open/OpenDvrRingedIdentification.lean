/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels

/-! # Identification of DVR and ringed open extension

Source: Stacks Tags 03DI, 03DJ and 0941; fixed completed coefficient projections.
(blueprint: lem-sf-open-dvr-ringed-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance inclusionContinuous {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (proEtaleOpenComposition j).IsContinuous
      (ProEt.topology X) (ProEt.topology Y) :=
  SheafOfModules.OpenTensorNormalization.openInclusion_continuous .ordinary j

private instance baseChangeContinuous {X Y : Scheme.{u}} (j : X ⟶ Y) :
    (proEtaleBaseChange j).IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
  proEtaleBaseChange_isContinuous j

private def openSiteAdj {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    proEtaleOpenComposition j ⊣ proEtaleBaseChange j :=
  SheafOfModules.OpenTensorNormalization.openSiteAdjunction .ordinary j

private def openRingAdj {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] := by
  letI := inclusionContinuous j
  letI := baseChangeContinuous j
  exact (openSiteAdj j).sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)

private theorem finite_direct {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (O : OpenDvrOpenModel l E j) (n : ℕ) :
    (openRingAdj j).unit.app (integralCoefficientCommRingSheaf l E Y n) ≫
      (proEtaleSheafDirectImage j CommRingCat.{u + 1}).map
        (show SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j
          (integralCoefficientCommRingSheaf l E Y n) ⟶
            integralCoefficientCommRingSheaf l E X n from ⟨(O.finite n).hom⟩) =
      proEtaleCoefficientDirectImageMap j (Padic.coefficientExtensionRing l E (n + 1)) := by
  let a := sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}
  apply (a.homEquiv _ _).injective
  change _ = a.homEquiv _ _ ((a.homEquiv _ _).symm _)
  erw [Equiv.apply_symm_apply]
  ext V x
  change (O.finite n).hom.app (op ((proEtaleBaseChange j).obj V.unop))
    ((integralCoefficientCommRingSheaf l E Y n).obj.map
      ((openSiteAdj j).counit.app V.unop).op
      ((adicLisseConstantUnit Y _).app V x)) =
        (adicLisseConstantUnit X _).app (op ((proEtaleBaseChange j).obj V.unop)) x
  have h := congrArg (fun f ↦ f x)
    ((adicLisseConstantUnit Y
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).naturality
        ((openSiteAdj j).counit.app V.unop).op)
  change (adicLisseConstantUnit Y _).app
      (op ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).obj
        ((proEtaleBaseChange j).obj V.unop))) x = _ at h
  change _ = (integralCoefficientCommRingSheaf l E Y n).obj.map
    ((openSiteAdj j).counit.app V.unop).op ((adicLisseConstantUnit Y _).app V x) at h
  exact (congrArg ((O.finite n).hom.app (op ((proEtaleBaseChange j).obj V.unop)))
    h.symm).trans (O.finite_constants n (op ((proEtaleBaseChange j).obj V.unop)) x)

private theorem completed_direct {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (O : OpenDvrOpenModel l E j) :
    (openRingAdj j).unit.app (completedIntegralCommRingSheafUnrestricted l E Y) ≫
      (proEtaleSheafDirectImage j CommRingCat.{u + 1}).map O.ring.hom =
        sfCompletedCoefficientMap l E j := by
  apply (sfCompletedCoefficientMap_existsUnique l E j).unique
  · intro n
    erw [Category.assoc, ← Functor.map_comp]
    have hp : O.ring.hom ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
        ((proEtaleOpenComposition j).sheafPushforwardContinuous CommRingCat.{u + 1}
            (ProEt.topology X) (ProEt.topology Y)).map
              (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
        (show SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j
          (integralCoefficientCommRingSheaf l E Y n) ⟶
            integralCoefficientCommRingSheaf l E X n from ⟨(O.finite n).hom⟩) := by
      apply Sheaf.hom_ext
      exact (O.ring_projection n).symm
    erw [hp, Functor.map_comp, ← Category.assoc]
    have hn := (openRingAdj j).unit.naturality
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    erw [← hn]
    erw [Category.assoc, finite_direct l E j O n]
    rfl
  · exact (sfCompletedCoefficientMap_existsUnique l E j).exists.choose_spec

private def ordinaryRestrictionComparison {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (O : OpenDvrOpenModel l E j) :
    integralOrdinaryPull l E j ≅
      SheafOfModules.OpenTensorNormalization.restrict .ordinary j
        (completedIntegralCommRingSheafUnrestricted l E Y) ⋙ O.modules.inverse := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let T := SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j R
  let c := SheafOfModules.OpenTensorNormalization.openRightCoefficient .ordinary j R
  let A := SheafOfModules.OpenTensorNormalization.direct .ordinary j R T c
  let a := (SheafOfModules.OpenTensorNormalization.openRestrictionAdjunction
    .ordinary j R).comp O.modules.symm.toAdjunction
  have hc : c ≫ (proEtaleSheafDirectImage j CommRingCat.{u + 1}).map O.ring.hom =
      proEtaleRingDirectImageMap j R
        (completedIntegralCommRingSheafUnrestricted l E X)
          ((PurCompactSupport.completed l E).pull j) := by
    have he : c = (openRingAdj j).unit.app R := by rfl
    have h := congrArg (fun q ↦ q ≫
      (proEtaleSheafDirectImage j CommRingCat.{u + 1}).map O.ring.hom) he
    exact h.trans ((completed_direct l E j O).trans
      (((proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _).symm)
  let H := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let ψ : (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      (proEtaleSheafDirectImage j RingCat.{u + 1}).obj (H.obj T) :=
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have e : O.modules.functor ⋙ A ≅
      proEtaleRingModuleDirectImage j R
        (completedIntegralCommRingSheafUnrestricted l E X)
          ((PurCompactSupport.completed l E).pull j) := by
    erw [O.modules_functor]
    change SheafOfModules.pushforward.{u + 1} (F := 𝟭 X.ProEt)
      (H.map O.ring.hom) ⋙ SheafOfModules.pushforward.{u + 1} ψ ≅ _
    refine SheafOfModules.pushforwardComp.{u + 1}
      (F := proEtaleBaseChange j) (G := 𝟭 X.ProEt) ψ (H.map O.ring.hom) ≪≫
      SheafOfModules.pushforwardCongr ?_
    apply Sheaf.hom_ext
    exact congrArg (fun q ↦ Functor.whiskerRight q.hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) hc
  exact (proEtaleRingModuleAdjunction j R
    (completedIntegralCommRingSheafUnrestricted l E X)
      ((PurCompactSupport.completed l E).pull j)).leftAdjointUniq (a.ofNatIsoRight e)

/-- The projection-normalized DVR open model computes actual ringed extension.
Source: Stacks 03DI, 03DJ and 0941; fix-prop-coherence, open-factor sentence
(blueprint: lem-sf-open-dvr-ringed-identification).

Proof: the finite_constants equations identify O.finite with restriction of the
constant coefficient sheaf, by the sheafification universal property. The limit
projection equations then identify O.ring with the restriction of the completed
coefficient pullback in PurCompactSupport.completed. Scalar restriction along
this isomorphism is O.modules.functor by modules_functor. Its inverse, composed
with actual open restriction, is consequently naturally isomorphic to the
ordinary completed-ring pullback integralOrdinaryPull. Compose the scalar
equivalence adjunction with O.extension.adjunction and transport this right
adjoint comparison. Both ordinary extension functors are now left adjoint to
the same actual pullback; left-adjoint uniqueness supplies their natural
isomorphism. Their exact-functor localizations, together with the composition
factorization, give the displayed derived isomorphism. No completeness or
constructibility of inputs is used, and the empty open is included. -/
theorem openDvr_ringed_identification {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (O : OpenDvrOpenModel l E j) :
    Nonempty (O.jShriek ≅ ringedOpen l E j) := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let T : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
    SheafOfModules.OpenTensorNormalization.restrictRing .ordinary j R
  let F : scalarReductionSource l E X ⥤ ProjectionRestriction.Mod T := O.modules.functor
  let G : ProjectionRestriction.Mod T ⥤ scalarReductionSource l E Y := O.extension.ordinary
  let H : scalarReductionSource l E X ⥤ scalarReductionSource l E Y :=
    PurCompactSupport.openExtension (PurCompactSupport.completed l E) j
  let : Abelian (scalarReductionSource l E Y) := by
    change Abelian (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    infer_instance
  let : HasDerivedCategory.{u + 2} (scalarReductionSource l E Y) :=
    scalarReductionSourceDerived l E Y
  have : F.IsEquivalence := O.modules.isEquivalence_functor
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  have : F.Additive := O.additive
  have : G.Additive := O.extension.additive
  have : PreservesFiniteLimits G := O.extension.limits
  have : PreservesFiniteColimits G := O.extension.colimits
  have : H.Additive := proEtaleRingOpenExtension_additive j _ _ _
  have : PreservesFiniteLimits H := proEtaleRingOpenExtension_limits j _ _ _
  have : PreservesFiniteColimits H := proEtaleRingOpenExtension_colimits j _ _ _
  have : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G
  have : PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G
  let a := O.modules.toAdjunction.comp O.extension.adjunction
  let e := ordinaryRestrictionComparison l E j O
  let b : F ⋙ G ≅ H :=
    (a.ofNatIsoRight e.symm).leftAdjointUniq
      (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j)
  exact ⟨Functor.mapDerivedCategoryCompIso
      (C₁ := scalarReductionSource l E X) (C₂ := ProjectionRestriction.Mod T)
      (C₃ := scalarReductionSource l E Y) F G ≪≫
    Functor.mapDerivedCategoryNatIso
      (C := scalarReductionSource l E X) (D := scalarReductionSource l E Y) b⟩

end WeilConjectures.IntegralSystemRealization
