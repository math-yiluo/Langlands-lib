/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import WeilConjectures.SmoothPurity.Pur.PurSequenceOrdinaryFactorization
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift

/-! # Coherent presentations in the fixed ordinary quotient coordinates

Source: Stacks 03D7, 06YY and 0941; step 2 of
stage3-pur-scalar-tensor-model-normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  pullbackTensorCalculus

private theorem referenceEvaluation_eq (Y : Scheme.{u})
    (O : PurSequenceOrdinaryAdjoints l E Y) (n : ℕ) :
    pullbackTensorReductionEvaluation l E Y n =
      (O.tensor n).symm ≪≫ Functor.isoWhiskerRight
        ((O.adjunction.ofNatIsoRight O.limit).leftAdjointUniq
          (pullbackTensorOrdinaryAdjunction l E Y))
        (coefficientSequenceEvaluation l E Y n) := by
  let adj := O.adjunction.ofNatIsoRight O.limit
  let a := adj.leftAdjointUniq (pullbackTensorOrdinaryAdjunction l E Y)
  let e := (O.tensor n).symm ≪≫
    Functor.isoWhiskerRight a (coefficientSequenceEvaluation l E Y n)
  apply ((pullbackTensorReductionEvaluation_existsUnique l E Y n).unique
    (show _ from ?_)
    (pullbackTensorReductionEvaluation_existsUnique l E Y n).exists.choose_spec).symm
  intro M
  have h := O.transpose M ((pullbackTensorOrdinaryReduction l E Y).obj M)
    (O.adjunction.homEquiv _ _ (a.hom.app M)) n
  rw [Equiv.symm_apply_apply] at h
  have ha := Adjunction.homEquiv_leftAdjointUniq_hom_app
    adj (pullbackTensorOrdinaryAdjunction l E Y) M
  change adj.homEquiv _ _ (a.hom.app M) = _ at ha
  dsimp only [adj] at ha
  erw [Adjunction.homEquiv_ofNatIsoRight_apply] at ha
  rw [O.projection_limit] at h
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  exact h.trans (by simpa only [Category.assoc] using
    (congrArg (fun k ↦ k ≫
      limit.π ((coefficientSequenceRestriction l E Y).obj
        ((pullbackTensorOrdinaryReduction l E Y).obj M)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom.app
        ((pullbackTensorOrdinaryReduction l E Y).obj M)) ha))

private theorem referenceEvaluation_transition (Y : Scheme.{u})
    (M : scalarReductionSource l E Y) (m n : ℕ) (h : n ≤ m) :
    (coefficientSequenceTransition l E Y h).app
        ((pullbackTensorOrdinaryReduction l E Y).obj M) ≫
      (normalizedDVRModuleRes l E Y h).map
        ((pullbackTensorReductionEvaluation l E Y n).inv.app M) =
      (pullbackTensorReductionEvaluation l E Y m).inv.app M ≫
        (coefficientOrdinaryQuotient l E Y h).app M := by
  obtain ⟨O, _⟩ := purSequenceOrdinaryFactorization l E Y
  rw [referenceEvaluation_eq l E Y O n, referenceEvaluation_eq l E Y O m]
  let a := (O.adjunction.ofNatIsoRight O.limit).leftAdjointUniq
    (pullbackTensorOrdinaryAdjunction l E Y)
  change _ ≫ (normalizedDVRModuleRes l E Y h).map
    ((coefficientSequenceEvaluation l E Y n).map (a.inv.app M) ≫
      (O.tensor n).hom.app M) =
    ((coefficientSequenceEvaluation l E Y m).map (a.inv.app M) ≫
      (O.tensor m).hom.app M) ≫ _
  have ht := (coefficientSequenceTransition l E Y h).naturality (a.inv.app M)
  dsimp only [Functor.comp_map] at ht
  rw [Functor.map_comp, ← Category.assoc]
  erw [← ht]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg ((coefficientSequenceEvaluation l E Y m).map (a.inv.app M) ≫ ·)
      (O.tensor_transition M m n h)

private theorem referenceOrdinaryUnit (W : Scheme.{u})
    (M : integralTowerModules l E W) (n : ℕ) :
    (pullbackTensorOrdinaryAdjunction l E W).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj
        ((pullbackTensorOrdinaryReduction l E W).obj M)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        ((pullbackTensorOrdinaryReduction l E W).obj M) ≫
      (scalarReductionRestriction l E W n).map
        ((pullbackTensorReductionEvaluation l E W n).inv.app M) =
      (pullbackTensorFiniteAdjunction l E W n).unit.app M := by
  have he := (pullbackTensorReductionEvaluation_existsUnique l E W n).exists.choose_spec M
  change (pullbackTensorFiniteAdjunction l E W n).homEquiv _ _
    ((pullbackTensorReductionEvaluation l E W n).hom.app M) = _ at he
  rw [Adjunction.homEquiv_unit] at he
  rw [← reassoc_of% he, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

private def referenceOrdinaryModel (W : Scheme.{u}) : CompletionUnit.OrdinaryModel l E W where
  tensor := pullbackTensorOrdinaryReduction l E W
  additive := pullbackTensorOrdinaryReduction_additive l E W
  evaluation n := (pullbackTensorReductionEvaluation l E W n).symm
  transition := fun M {m n} h ↦ referenceEvaluation_transition l E W M m n h
  adjunction := pullbackTensorOrdinaryAdjunction l E W
  unit_tensor := by
    intro M n V x
    exact (congrArg (fun f ↦ f.val.app V x) (referenceOrdinaryUnit l E W M n)).trans
      (scalarUnit_tensor l E W M n V x)
  limitComparison := Functor.isoWhiskerLeft (CompletionUnit.tower l E W)
    (CompletionUnit.termwiseLimitComparison l E W)
  limitComparison_projection := by
    intro I n p
    exact CompletionUnit.termwiseLimitComparison_projection l E W
      ((CompletionUnit.tower l E W).obj I) n p

private theorem referenceSystemUnit (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (CompletionUnit.systemLimitUnit l E W (referenceOrdinaryModel l E W)
      (CompletionUnit.constantLimitUnit l E W)).app C =
      pullbackTensorLimitUnit l E W C := by
  unfold CompletionUnit.systemLimitUnit CompletionUnit.constantLimitUnit
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.assoc]
  change DerivedCategory.Q.map
    ((CompletionUnit.termwiseLimitComparison l E W).hom.app
      ((CompletionUnit.tower l E W).obj C)) ≫ _ = _
  erw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hqA : (DerivedCategory.quotientCompQhIso
      (ℕᵒᵖ ⥤ scalarReductionSource l E W)).hom.app
        ((CompletionUnit.tower l E W).obj C) = 𝟙 _ := rfl
  have hqiB (K : CochainComplex (scalarReductionSource l E W) ℤ) :
      (DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app K =
        𝟙 _ := rfl
  have hf : ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomotopyCategoryFactors (.up ℤ)).inv.app
        ((CompletionUnit.tower l E W).obj C) = 𝟙 _ := rfl
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  erw [hqA, hqiB, hf]
  simp only [CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp, Category.id_comp]
  unfold pullbackTensorLimitUnit
  change _ = DerivedCategory.Q.map (𝟙 _) ≫ _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp, Category.id_comp]
  dsimp only [Functor.rightDerivedFunctorUnitQ]
  erw [hqiB, hqA, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]; rfl

private theorem referenceDerivedModel (W : Scheme.{u}) :
    ∃ D : CompletionUnit.DerivedModel l E W (pullbackTensorCalculus l E W)
        (referenceOrdinaryModel l E W),
      ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        D.reductionComparison.app P.obj = (pullbackTensorReductionModel l E W).hom.app P := by
  let S := pullbackTensorCalculus l E W
  let M := referenceOrdinaryModel l E W
  obtain ⟨r, hr⟩ := CompletionUnit.constantRoosComparison_exists l E W
  obtain ⟨hI, ε, hε, hflat, heval, hhom⟩ :=
    CompletionUnit.fixedDerivedComparison l E W S M
      (CompletionUnit.termwiseLimitComparison l E W)
      (CompletionUnit.termwiseLimitComparison_projection l E W)
      (CompletionUnit.constantLimitUnit l E W)
      (CompletionUnit.constantLimitUnit_normalization l E W)
  let D : CompletionUnit.DerivedModel l E W S M := {
    towerLimitComparison := CompletionUnit.termwiseLimitComparison l E W
    towerLimitComparison_projection := CompletionUnit.termwiseLimitComparison_projection l E W
    limitUnit := CompletionUnit.constantLimitUnit l E W
    limitUnit_normalization := CompletionUnit.constantLimitUnit_normalization l E W
    roos := r
    roos_normalization := hr
    systemUnit := CompletionUnit.systemLimitUnit l E W M (CompletionUnit.constantLimitUnit l E W)
    system_isIso := hI
    systemUnit_composition := fun I ↦ rfl
    reductionComparison := ε
    reduction_isLeftDerived := hε
    reduction_isIso := hflat
    reduction_evaluation := heval
    hom_normalization := hhom }
  refine ⟨D, ?_⟩
  intro P
  apply (S.adjunction.homEquiv _ _).injective
  have h := D.hom_normalization P.obj ((M.quotient l E W).obj P.obj) (𝟙 _)
  have hid := (DerivedCategory.Q (C := coefficientSequenceModules l E W)).map_id
    ((M.quotient l E W).obj P.obj)
  erw [hid, Category.comp_id, Adjunction.homEquiv_id] at h
  refine h.trans ?_
  change DerivedCategory.Q.map
    ((Adjunction.mapHomologicalComplex (.up ℤ)
      (pullbackTensorOrdinaryAdjunction l E W)).unit.app P.obj) ≫
    (CompletionUnit.systemLimitUnit l E W (referenceOrdinaryModel l E W)
      (CompletionUnit.constantLimitUnit l E W)).app
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj) = _
  erw [referenceSystemUnit]
  exact ((pullbackTensorReductionModel_existsUnique l E W).exists.choose_spec P).symm

/-- Whole-system coherence identifies a presentation with the fixed ordinary quotient
complex and the adjunction-normalized reference reduction model.
Source: Stacks 03D7, 06YY and 0941; step 2 of
stage3-pur-scalar-tensor-model-normalization.
(blueprint: lem-pur-coherent-reference-quotient-comparison).

Proof: reconstruct the ordinary quotient isomorphism by transposing the strict
unit map in the coherence hypothesis through the ordinary tensor/limit adjunction.
The finite extension/restriction Hom bijections identify each evaluated map with
the inverse prescribed quotient identification followed by the reference evaluation.
In particular each evaluation is invertible, so the map is a strict isomorphism.
The normalized right-derived limit unit gives the derived transpose of this map.
Both the reference reduction model and the given coherent presentation have this
transpose: use the reference reduction model's defining unit equation, the
constant-tower counit's K-injective normalization, and naturality along a
K-injective replacement. The unique left-adjoint comparison preserves the unit.
Injectivity of the two derived Hom bijections therefore gives the first equality
in the entire system derived category. This is the fixed-coordinate version of
coherentQuotientModelComparison and uses no finite derived evaluation faithfulness.
The construction works for zero complexes, the first quotient and the empty scheme. -/
theorem coherentReferenceQuotientComparison (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (P : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P.obj)
    (hc : IsIntegralComparisonPresentationCoherent l E W S P.obj C e κ) :
    ∃ a : (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
        P.obj) ≅ C,
      (pullbackTensorReductionModel l E W).hom.app P ≫ DerivedCategory.Q.map a.hom =
        ((pullbackTensorCalculus l E W).adjunction.leftAdjointUniq S.adjunction).hom.app
          (DerivedCategory.Q.obj P.obj) ≫ e.hom ∧
      ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
          κ n = ((pullbackTensorReductionEvaluationComplex l E W n).app P.obj).symm := by
  let T := pullbackTensorCalculus l E W
  let j := T.adjunction.leftAdjointUniq S.adjunction
  let e' := j.app (DerivedCategory.Q.obj P.obj) ≪≫ e
  have hc' : IsIntegralComparisonPresentationCoherent l E W T P.obj C e' κ := by
    unfold IsIntegralComparisonPresentationCoherent at hc ⊢
    obtain ⟨b, hb, he⟩ := hc
    refine ⟨b, hb, ?_⟩
    change (integralComparisonConstantTower l E W).map
      (T.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E W).map
          (j.hom.app (DerivedCategory.Q.obj P.obj) ≫ e.hom)) ≫ _ = _
    have hu : T.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E W).map
          (j.hom.app (DerivedCategory.Q.obj P.obj) ≫ e.hom) =
        S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientSequenceLimit l E W).map e.hom := by
      rw [(coefficientSequenceLimit l E W).map_comp, ← Category.assoc]
      exact congrArg (fun f ↦ f ≫ (coefficientSequenceLimit l E W).map e.hom)
        (T.adjunction.unit_leftAdjointUniq_hom_app S.adjunction _)
    rw [hu]
    exact he
  obtain ⟨D, hD⟩ := referenceDerivedModel l E W
  obtain ⟨a, ha, hκ⟩ := coherentQuotientModelComparison l E W T
    (referenceOrdinaryModel l E W) D P.obj C e' κ hc'
  refine ⟨a, ?_, hκ⟩
  rw [hD P] at ha
  exact ha

end WeilConjectures
