/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift

/-! # Comparison with a fixed normalized quotient model

Source: Stacks 03D7, 06YY and 0941.
(blueprint: lem-trf-coherent-quotient-model-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem limitComparison_eq (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W) (M : CompletionUnit.OrdinaryModel l E W)
    (D : CompletionUnit.DerivedModel l E W S M)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    M.limitComparison.hom.app C =
      D.towerLimitComparison.hom.app ((CompletionUnit.tower l E W).obj C) := by
  apply limit.hom_ext
  intro n
  ext i : 1
  exact (M.limitComparison_projection C n.unop i).trans
    (D.towerLimitComparison_projection ((CompletionUnit.tower l E W).obj C) n.unop i).symm

private theorem limitUnit_counit (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W) (M : CompletionUnit.OrdinaryModel l E W)
    (D : CompletionUnit.DerivedModel l E W S M)
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    (integralComparisonConstantTower l E W).map
        (DerivedCategory.Q.map (D.towerLimitComparison.hom.app Z) ≫ D.limitUnit.app Z) ≫
      (integralComparisonTowerCounit l E W).app (DerivedCategory.Q.obj Z) =
    (Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤
      ℕᵒᵖ ⥤ scalarReductionSource l E W).mapDerivedCategoryFactors.hom.app
        (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj Z) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E W)).counit (.up ℤ)).app Z) := by
  let L : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W := lim
  let F : scalarReductionSource l E W ⥤ ℕᵒᵖ ⥤ scalarReductionSource l E W :=
    Functor.const ℕᵒᵖ
  let δ : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W :=
    Functor.whiskerRight D.towerLimitComparison.hom DerivedCategory.Q ≫ D.limitUnit
  let α : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
      integralComparisonConstantTower l E W ⟶ DerivedCategory.Q :=
    Functor.whiskerRight δ (integralComparisonConstantTower l E W) ≫
      Functor.whiskerLeft DerivedCategory.Q (integralComparisonTowerCounit l E W)
  let β : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
      integralComparisonConstantTower l E W ⟶ DerivedCategory.Q :=
    Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatTrans.mapHomologicalComplex
        (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E W)).counit (.up ℤ))
          DerivedCategory.Q
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [I.IsKInjective] : α.app I = β.app I := by
    let e := L.rightDerivedFunctorObjQIso I
    have hδ : δ.app I = e.inv := by
      apply (cancel_mono e.hom).1
      change (DerivedCategory.Q.map (D.towerLimitComparison.hom.app I) ≫
        D.limitUnit.app I) ≫ e.hom = e.inv ≫ e.hom
      rw [Category.assoc, D.limitUnit_normalization, ← CategoryTheory.Functor.map_comp,
        Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, e.inv_hom_id]
    change (integralComparisonConstantTower l E W).map (δ.app I) ≫
      (integralComparisonTowerCounit l E W).app (DerivedCategory.Q.obj I) = _
    rw [hδ, integralComparisonTowerCounit_computes]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, e.inv_hom_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have h : α = β := by
    apply NatTrans.ext
    funext K
    obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    let : I.IsKInjective := hI
    let : QuasiIso j := hj
    have : IsIso (DerivedCategory.Q.map j) := inferInstance
    apply (Iso.cancel_iso_hom_right (α.app K) (β.app K)
      (asIso (DerivedCategory.Q.map j))).1
    change α.app K ≫ DerivedCategory.Q.map j = β.app K ≫ DerivedCategory.Q.map j
    exact (α.naturality j).symm.trans
      ((congrArg (fun f ↦ (L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
        integralComparisonConstantTower l E W).map j ≫ f) (hi I)).trans (β.naturality j))
  exact NatTrans.congr_app h Z

private theorem derivedTranspose (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W) (M : CompletionUnit.OrdinaryModel l E W)
    (D : CompletionUnit.DerivedModel l E W S M)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : (M.quotient l E W).obj P ⟶ C) :
    (integralComparisonConstantTower l E W).map
      (S.adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj C)
        (D.reductionComparison.app P ≫ DerivedCategory.Q.map a)) ≫
      (integralComparisonTowerCounit l E W).app
        ((coefficientSequenceDerivedRestriction l E W).obj (DerivedCategory.Q.obj C)) =
    (Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤
      ℕᵒᵖ ⥤ scalarReductionSource l E W).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map (
        (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E W)).mapHomologicalComplex
          (.up ℤ)).homEquiv P ((CompletionUnit.tower l E W).obj C)).symm
          (((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C) a)) ≫
      (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C := by
  let F := integralComparisonConstantTower l E W
  let Z := (CompletionUnit.tower l E W).obj C
  let u := ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C) a
  let r := (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C
  have hr := (integralComparisonTowerCounit l E W).naturality r
  dsimp only [Functor.comp_map, Functor.id_map] at hr
  calc
    _ = F.map (DerivedCategory.Q.map u) ≫
        (F.map (DerivedCategory.Q.map (D.towerLimitComparison.hom.app Z) ≫
          D.limitUnit.app Z) ≫
          (integralComparisonTowerCounit l E W).app (DerivedCategory.Q.obj Z)) ≫ r := by
      rw [D.hom_normalization, D.systemUnit_composition,
        limitComparison_eq l E W S M D C]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      erw [hr]
      rfl
    _ = F.map (DerivedCategory.Q.map u) ≫
        ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤
          ℕᵒᵖ ⥤ scalarReductionSource l E W).mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
              scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj Z) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E W)).counit
              (.up ℤ)).app Z)) ≫ r := by
      rw [limitUnit_counit l E W S M D Z]
    _ = _ := by
      have hn := (Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E W).mapDerivedCategoryFactors.hom.naturality u
      dsimp only [Functor.comp_map] at hn
      simp only [Category.assoc]
      erw [reassoc_of% hn]
      rw [← CategoryTheory.Functor.map_comp_assoc]
      rfl

/-- Whole-system coherence identifies the strict presentation with a fixed
normalized ordinary and derived quotient model.
Source: Stacks 06YY (derived adjunction) and 0941 (derived tower limit).
(blueprint: lem-trf-coherent-quotient-model-comparison).

Proof: the ordinary reconstruction gives a strict isomorphism with the prescribed
finite comparisons. Normalize the derived constant-tower counit using D.limitUnit
on K-injective towers; extend the formula to all towers by naturality along a
K-injective resolution, whose localization is invertible. The ordinary limit
comparison projections identify the two termwise limit comparisons. The
normalizations of D then identify the double adjoint transpose of its reduction
comparison followed by the strict isomorphism with Q(b). Coherence gives the
same double transpose for e. Injectivity of both adjunction Hom bijections gives
the equality in the entire derived system category. -/
theorem coherentQuotientModelComparison (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W) (M : CompletionUnit.OrdinaryModel l E W)
    (D : CompletionUnit.DerivedModel l E W S M)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (hcoh : IsIntegralComparisonPresentationCoherent l E W S P C e κ) :
    ∃ a : (M.quotient l E W).obj P ≅ C,
      D.reductionComparison.app P ≫ DerivedCategory.Q.map a.hom = e.hom ∧
      ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
          κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P := by
  unfold IsIntegralComparisonPresentationCoherent at hcoh
  obtain ⟨b, hb, he⟩ := hcoh
  obtain ⟨a, ha, hκ⟩ := coherentQuotientOrdinaryLift l E W M P C κ b hb
  refine ⟨a, ?_, hκ⟩
  · apply (S.adjunction.homEquiv (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj C)).injective
    apply ((integralComparisonConstantAdjunction l E W).homEquiv
      (DerivedCategory.Q.obj P)
      ((coefficientSequenceDerivedRestriction l E W).obj (DerivedCategory.Q.obj C))).symm.injective
    rw [Adjunction.homEquiv_counit]
    erw [derivedTranspose l E W S M D P C a.hom]
    rw [ha, Equiv.symm_apply_apply]
    exact he.symm

end WeilConjectures
