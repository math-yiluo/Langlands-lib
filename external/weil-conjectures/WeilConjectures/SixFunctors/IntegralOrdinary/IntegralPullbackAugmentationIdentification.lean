/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorPullModel
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackComplexIdentification
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Identification of the ordinary pullback augmentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local implicit_reducible] PurCompactSupport.completed
  completedIntegralCommRingSheafUnrestricted
  ordinaryIntegralModulePush ordinaryIntegralPullComplex IntegralOnSlice.Site
attribute [-instance] OpenFactorCoherence.siteLocallyBijective
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] integralOperationsSiteSmall scalarReductionSourceDerived
  scalarReductionTargetDerived integralOperationsCommHasDerivedCategory
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local instance 4000] ordinaryIntegralModulePull_additive
attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted SheafOfModules.monoidalCategory
  ordinaryIntegralModulePull
  Functor.mapDerivedCategory proEtaleRingDerivedPullbackFactors
  ordinaryIntegralPullComplexCounit sfCompletedCoefficientMap ordinaryIntegralDirectRingMap

private theorem pull_quotient_augmentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : OpenFactorCoherence.Pull l E f)
    (b : OpenFactorCoherence.pullCx l E f ≅ ordinaryIntegralPullComplex l E f)
    (hb : ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
      (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
      (((b.inv.app P).f i).val.app (op ((proEtaleBaseChange f).obj V)))
        ((((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app (op V)) x) =
      (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).unit.app (P.X i)).val.app (op V)) x) :
    ordinaryIntegralQuotientAugmentation l E f =
      Functor.whiskerRight b.inv (Functor.const ℕᵒᵖ) ≫
        Functor.whiskerLeft (OpenFactorCoherence.pullCx l E f)
          (IntegralOnSlice.augmentation l E X none) ≫ p.tower.hom := by
  apply (ordinaryIntegralQuotientAugmentation_existsUnique l E f).unique
  · exact (ordinaryIntegralQuotientAugmentation_existsUnique l E f).exists.choose_spec
  · intro P n i V x
    change (((p.tower.hom.app P).app (op n)).f i).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((((IntegralOnSlice.augmentation l E X none).app
        ((OpenFactorCoherence.pullCx l E f).obj P)).app (op n)).f i).val.app
          (op ((proEtaleBaseChange f).obj V))
        (((b.inv.app P).f i).val.app
          (op ((proEtaleBaseChange f).obj V))
          (((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app
            (op V) x))) = _
    rw [hb]
    have ha := (IntegralOnSlice.augmentation_existsUnique l E X none).exists.choose_spec
      ((OpenFactorCoherence.pullCx l E f).obj P) n i
      (op ((proEtaleBaseChange f).obj V))
      (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).unit.app (P.X i)).val.app (op V) x)
    change (((((IntegralOnSlice.augmentation l E X none).app
      ((OpenFactorCoherence.pullCx l E f).obj P)).app (op n)).f i).val.app
      (op ((proEtaleBaseChange f).obj V))) _ = _ at ha
    rw [ha]
    exact p.generators P n i V x

private theorem pull_completion_chain {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : OpenFactorCoherence.Pull l E f)
    (b : OpenFactorCoherence.pullCx l E f ≅ ordinaryIntegralPullComplex l E f)
    (hb : ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
      (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
      (((b.inv.app P).f i).val.app (op ((proEtaleBaseChange f).obj V)))
        ((((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app (op V)) x) =
      (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).unit.app (P.X i)).val.app (op V)) x)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (b.hom.app P) ≫
        ordinaryIntegralCompletionChain l E f P =
      IntegralOnSlice.roosUnit l E X none ((OpenFactorCoherence.pullCx l E f).obj P) ≫
        integralOperationsRoosMap (p.tower.hom.app P) := by
  have hn : b.hom.app P ≫ ordinaryIntegralProductAugmentation l E f P =
      IntegralOnSlice.productAugmentation l E X none
          ((OpenFactorCoherence.pullCx l E f).obj P) ≫
        Limits.Pi.map (fun n ↦ (p.tower.hom.app P).app (op n)) := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, ordinaryIntegralProductAugmentation,
      IntegralOnSlice.productAugmentation, Limits.Pi.lift_comp_π, Limits.Pi.map_π,
      Limits.Pi.lift_comp_π_assoc]
    have h := congrArg (fun a ↦ (a.app P).app (op n))
      (pull_quotient_augmentation l E f p b hb)
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.const_map_app] at h
    rw [h]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hu : IntegralOnSlice.productAugmentation l E X none
      ((OpenFactorCoherence.pullCx l E f).obj P) ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((IntegralOnSlice.tower l E X none).obj
          ((OpenFactorCoherence.pullCx l E f).obj P)).obj (op n))
        (integralOperationsTowerStep ((IntegralOnSlice.tower l E X none).obj
          ((OpenFactorCoherence.pullCx l E f).obj P))) = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa only [CochainComplex.HomComplex.δ_zero, zero_add,
      CochainComplex.HomComplex.Cochain.ofHom_zero] using
      IntegralOnSlice.roosUnit_condition l E X none
        ((OpenFactorCoherence.pullCx l E f).obj P)
  have hv : ordinaryIntegralProductAugmentation l E f P ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
        (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P)) =
      0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa only [CochainComplex.HomComplex.δ_zero, zero_add,
      CochainComplex.HomComplex.Cochain.ofHom_zero] using
      ordinaryIntegralCompletionChain_condition l E f P
  unfold ordinaryIntegralCompletionChain IntegralOnSlice.roosUnit integralOperationsRoosMap
  rw [arrowConeMap]
  exact completedCoconeLift_natural (integralTowerModules l E X) _ _ _ _
    (integralOperationsRoos_square (p.tower.hom.app P)) (b.hom.app P) _ _ hu hv hn

/-- The ordinary completion comparison equals the quotient-unit comparison of every
normalized strict pullback model.

Source: Stacks 03D2, 06YY, 08TC and 0941.
(blueprint: lem-sf-integral-pullback-augmentation-identification).

Proof: identify the two ordinary module pullbacks by uniqueness of their adjunctions.
This identification preserves adjunction-unit sections. The generator normalization
of the strict tower therefore identifies its quotient augmentation with the specified
ordinary augmentation. Their maps to the Roos cones agree: the product coordinate is
that augmentation and the shifted coordinate is zero. The canonical comparison of
the derived pullbacks preserves the universal computation maps. On a flat-term K-flat
representative the defining equations for the completion unit and the strict model,
together with these identifications, give the same whole-cone map as pullComparison.
Faithful restriction along the resolving-class localization gives the asserted equality.
No tensor input, invertibility of l, or constructibility assumption is used. -/
theorem pullComparison_eq_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : OpenFactorCoherence.Pull l E f) :
    pullComparison l E f = p.unit l E := by
  obtain ⟨b, hb, hfactor⟩ := pullbackComplexIdentification l E f
  obtain ⟨ff⟩ := good_whisker_fullyFaithful l E Y
    (DerivedCategory (integralTowerModules l E X))
  apply ff.map_injective
  apply NatTrans.ext
  funext P
  have hP : IntegralOnSlice.Good l E Y none P.obj := P.property
  let T := (OpenFactorCoherence.pullCx l E f).obj P.obj
  let ε := (proEtaleRingDerivedPullbackFactors f
    ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).hom.app P.obj
  apply (cancel_mono ((integralDerivedPullbackComparison l E f).hom.app P)).1
  change (pullComparison l E f).app (DerivedCategory.Q.obj P.obj) ≫ _ =
    (p.unit l E).app (DerivedCategory.Q.obj P.obj) ≫ _
  have hm := p.model P.obj hP
  have hu := (IntegralOnSlice.completionUnit_existsUnique l E X none).exists.choose_spec
    ⟨T, p.good P.obj hP⟩
  change (IntegralOnSlice.completionUnit l E X none).app (DerivedCategory.Q.obj T) ≫
    (IntegralOnSlice.completionComparison l E X none).hom.app ⟨T, p.good P.obj hP⟩ =
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none T) at hu
  have hn := (IntegralOnSlice.completionUnit l E X none).naturality ε
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hc := (ordinaryIntegralCompletionComparison_existsUnique l E f).exists.choose_spec P
  change (ordinaryIntegralCompletionComparison l E f).app _ ≫ _ = _ at hc
  calc
    _ = (pullIso l E f).hom.app (DerivedCategory.Q.obj P.obj) ≫
        ordinaryIntegralPullComplexCounit l E f P.obj ≫
        DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E f P.obj) := by
      unfold pullComparison
      simpa only [NatTrans.comp_app, Category.assoc] using
        congrArg (fun z ↦ (pullIso l E f).hom.app (DerivedCategory.Q.obj P.obj) ≫ z) hc
    _ = ε ≫ DerivedCategory.Q.map
        (IntegralOnSlice.roosUnit l E X none T) ≫
        DerivedCategory.Q.map (integralOperationsRoosMap (p.tower.hom.app P.obj)) := by
      rw [← Category.assoc, hfactor]
      rw [Category.assoc, ← Functor.map_comp]
      change ε ≫ DerivedCategory.Q.map
        (b.hom.app P.obj ≫
          ordinaryIntegralCompletionChain l E f P.obj) = _
      rw [pull_completion_chain l E f p b hb, Functor.map_comp]
    _ = (IntegralOnSlice.completionUnit l E X none).app
          ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj
            (DerivedCategory.Q.obj P.obj)) ≫
        (IntegralOnSlice.completion l E X none).map ε ≫
        (IntegralOnSlice.completionComparison l E X none).hom.app ⟨T, p.good P.obj hP⟩ ≫
        DerivedCategory.Q.map (integralOperationsRoosMap (p.tower.hom.app P.obj)) := by
      rw [← hu, ← reassoc_of% hn]
      simp only [Category.assoc]
      rfl
    _ = _ := by
      dsimp only [OpenFactorCoherence.Pull.unit, NatTrans.comp_app,
        Functor.whiskerLeft_app]
      rw [Category.assoc, hm]
      dsimp only [ε, T]
      unfold proEtaleRingDerivedPullbackFactors
      rfl

end WeilConjectures.IntegralOrdinary
