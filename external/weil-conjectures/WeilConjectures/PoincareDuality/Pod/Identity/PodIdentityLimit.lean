/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityRestrictedTower
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityRoosMap
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityDerivedFactors

/-! # Compatibility of normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus WeilConjectures.coefficientSequenceRestriction

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem roos_model_unique (W : Scheme.{u})
    (ρ ρ' : IntegralComparisonRoosModel l E W) : ρ = ρ' := by
  suffices h : ρ.comparison = ρ'.comparison by
    cases ρ
    cases ρ'
    cases h
    rfl
  apply Iso.ext_inv
  apply NatTrans.ext
  funext C
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : QuasiIso q := hq
  have : IsIso ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W).map q) := by
    change IsIso ((coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q))
    infer_instance
  have hi : ρ.comparison.app I = ρ'.comparison.app I := by
    apply Iso.ext
    exact (ρ.computes I).trans (ρ'.computes I).symm
  apply (cancel_mono ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W).map q)).1
  rw [← ρ.comparison.inv.naturality q, ← ρ'.comparison.inv.naturality q]
  exact congrArg (fun z ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q).map q ≫ z) (congrArg Iso.inv hi)

private def limit_roos_iso (W : Scheme.{u}) (ρ : IntegralComparisonRoosModel l E W) :
    DerivedCategory.Q ⋙ coefficientSequenceLimit l E W ≅
      (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q :=
  isoWhiskerRight (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l E W) ≪≫
    isoWhiskerLeft ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ))
      ρ.comparison

private theorem restricted_roos_identity
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (D : PodCompletionReindex l E (𝟙 W))
    (hr : PodCompletionReindex.RestrictedGenerators l E (𝟙 W) D)
    (hf : PodCompletionReindex.RoosFst l E (𝟙 W) D)
    (hs : PodCompletionReindex.RoosSnd l E (𝟙 W) D)
    (a : isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _)
    (ha : ∀ (M : scalarReductionSource l E W) (U : W.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))),
      (a.hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
          (𝟙 W) rfl).hom.app U).op x)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    let H := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ integralOperationsRoosFunctor
    let σ := NatIso.mapHomologicalComplex (integralComparisonSequenceUnit l E W) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    let α := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    (D.roos (podRestrictedTower l E C)).hom ≫
        integralOperationsRoosFunctor.map (D.restricted C).hom ≫
        H.map (σ.hom.app C) = α.hom.app (H.obj C) := by
  dsimp only
  have htower := podIdentityRestrictedTower l E W D hr a ha C
  change (D.roos (podRestrictedTower l E C)).hom ≫
    integralOperationsRoosFunctor.map (D.restricted C).hom ≫
    integralOperationsRoosFunctor.map
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex (integralComparisonSequenceUnit l E W) (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app C))) = _
  rw [← integralOperationsRoosFunctor.map_comp, htower]
  exact podIdentityRoosMap (isoReductionIntegralInverse l E (𝟙 W)) a
    (podRestrictedTower l E C) (D.roos (podRestrictedTower l E C)).hom
    (hf (podRestrictedTower l E C)) (hs (podRestrictedTower l E C))

/-- Identity compatibility for the derived total-limit comparison.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5
(blueprint: lem-pod-identity-limit).

Proof: use the proved strict restricted-tower identity and both Roos coordinates.
The source and target normalized Roos models agree on K-injectives; naturality
along K-injective resolutions makes them equal everywhere. Substitute LimitModel,
use the derived identity formula on complexes, and cancel the model isomorphism.
Localization detects equality of natural transformations, giving the result on
all derived systems. -/
theorem podIdentityLimit (A : PodReindexFamily l E)
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (hD : PodCompletionReindex.Laws l E (𝟙 W) (A.completion (𝟙 W)))
    (ha : ∀ (M : scalarReductionSource l E W) (U : W.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))),
      ((A.identity W).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
          (𝟙 W) rfl).hom.app U).op x)
    (N : coefficientSequenceDerived l E W) :
    (A.completion (𝟙 W)).limit.hom.app N ≫
        (coefficientSequenceLimit l E W).map ((integralComparisonSystemUnit l E W).hom.app N) =
      (A.identityDerived l E W).hom.app ((coefficientSequenceLimit l E W).obj N) := by
  let D := A.completion (𝟙 W)
  let R := coefficientSequenceLimit l E W
  let F := podOrdinaryReindex l E (𝟙 W)
  let b := integralComparisonSystemUnit l E W
  let a := A.identityDerived l E W
  have hh : D.limit.hom ≫ whiskerRight b.hom R = whiskerLeft R a.hom := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    intro C
    let H := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ integralOperationsRoosFunctor
    let σ := NatIso.mapHomologicalComplex (integralComparisonSequenceUnit l E W) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    let α := NatIso.mapHomologicalComplex (A.identity W) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    let β := limit_roos_iso l E W D.targetRoos
    have hρ := roos_model_unique l E W D.sourceRoos D.targetRoos
    have hm : PodCompletionReindex.LimitModel l E (𝟙 W) D := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩ := hD
      exact hm
    have hr : PodCompletionReindex.RestrictedGenerators l E (𝟙 W) D := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr, _⟩ := hD
      exact hr
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hf, hs, _⟩ := hD
    have hc := restricted_roos_identity l E W D hr hf hs (A.identity W) ha C
    change (D.roos (podRestrictedTower l E C)).hom ≫
      integralOperationsRoosFunctor.map (D.restricted C).hom ≫
        H.map (σ.hom.app C) = α.hom.app (H.obj C) at hc
    have hβ := β.hom.naturality (σ.hom.app C)
    change R.map (DerivedCategory.Q.map (σ.hom.app C)) ≫ β.hom.app C =
      β.hom.app _ ≫ DerivedCategory.Q.map (H.map (σ.hom.app C)) at hβ
    have hb := podIdentityDerivedFactors (integralComparisonSequencePullback l E (𝟙 W))
      (integralComparisonSequenceUnit l E W) C
    change b.hom.app (DerivedCategory.Q.obj C) =
      (integralComparisonSequencePullback l E (𝟙 W)).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map (σ.hom.app C) at hb
    have haC := podIdentityDerivedFactors (isoReductionIntegralInverse l E (𝟙 W))
      (A.identity W) (H.obj C)
    change a.hom.app (DerivedCategory.Q.obj (H.obj C)) =
      (isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app (H.obj C) ≫
        DerivedCategory.Q.map (α.hom.app (H.obj C)) at haC
    have hmC := hm C
    dsimp only [PodCompletionReindex.LimitModel] at hm
    rw [hρ] at hmC
    change F.map (β.hom.app C) ≫
        (isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app (H.obj C) ≫
        DerivedCategory.Q.map (D.roos (podRestrictedTower l E C)).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map (D.restricted C).hom) =
      D.limit.hom.app (DerivedCategory.Q.obj C) ≫ R.map
        ((integralComparisonSequencePullback l E (𝟙 W)).mapDerivedCategoryFactors.hom.app C) ≫
        β.hom.app _ at hmC
    change D.limit.hom.app (DerivedCategory.Q.obj C) ≫
      R.map (b.hom.app (DerivedCategory.Q.obj C)) =
        a.hom.app (R.obj (DerivedCategory.Q.obj C))
    apply (cancel_mono (β.hom.app C)).1
    calc
      _ = D.limit.hom.app (DerivedCategory.Q.obj C) ≫
          R.map
            ((integralComparisonSequencePullback l E (𝟙 W)).mapDerivedCategoryFactors.hom.app C) ≫
          β.hom.app _ ≫ DerivedCategory.Q.map (H.map (σ.hom.app C)) := by
        rw [hb, R.map_comp, Category.assoc, Category.assoc, hβ]
      _ = F.map (β.hom.app C) ≫
          (isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app (H.obj C) ≫
          DerivedCategory.Q.map (α.hom.app (H.obj C)) := by
        rw [← reassoc_of% hmC, ← DerivedCategory.Q.map_comp,
          ← DerivedCategory.Q.map_comp, hc]
      _ = F.map (β.hom.app C) ≫ a.hom.app (DerivedCategory.Q.obj (H.obj C)) := by rw [haC]
      _ = _ := a.hom.naturality (β.hom.app C)
  exact congr_app hh N

end WeilConjectures
