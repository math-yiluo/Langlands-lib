/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismMultiplicationConeDescent
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.TraceFormula.Supporting.StrictQuotientConeAugmentation
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitStrictQuotientModel
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation

/-! # The actual completion unit in the strict quotient cone

Source: blueprint main-20261015, rational Frobenius integral model, proof (2)--(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence coefficientSequenceRestriction
  coefficientSequenceEvaluation unrestrictedTowerUnit coefficientConstantTowerLimit

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem cone_hom_ext
    {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    {X Y P : CochainComplex A ℤ} (δ : X ⟶ Y)
    (f g : P ⟶ CochainComplex.mappingCocone δ)
    (hf : f ≫ CochainComplex.mappingCocone.fst δ =
      g ≫ CochainComplex.mappingCocone.fst δ)
    (hs : ∀ p : ℤ, f.f (p + 1) ≫ (CochainComplex.mappingCocone.snd δ).v
      (p + 1) p (add_neg_cancel_right p 1) = 0)
    (hs' : ∀ p : ℤ, g.f (p + 1) ≫ (CochainComplex.mappingCocone.snd δ).v
      (p + 1) p (add_neg_cancel_right p 1) = 0) : f = g := by
  ext i : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective i
  change f.f (p + 1) = g.f (p + 1)
  have hfi := congrArg (fun f ↦ HomologicalComplex.Hom.f f (p + 1)) hf
  dsimp only [HomologicalComplex.comp_f] at hfi
  calc
    _ = _ ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = _ ≫ ((CochainComplex.mappingCocone.fst δ).f (p + 1) ≫
        (CochainComplex.mappingCocone.inl δ).v (p + 1) (p + 1) (add_zero _) +
        (CochainComplex.mappingCocone.snd δ).v (p + 1) p
          (add_neg_cancel_right p 1) ≫
        (CochainComplex.mappingCocone.inr δ).1.v p (p + 1) (by omega)) := by
      rw [CochainComplex.mappingCocone.id_X]
    _ = _ := by
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        hs p, zero_comp, add_zero, hfi]
      conv_rhs => rw [← Category.comp_id (g.f (p + 1)),
        ← CochainComplex.mappingCocone.id_X δ (p + 1) p
          (add_neg_cancel_right p 1)]
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        hs' p, zero_comp, add_zero]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem roos_inclusion_fst
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    roosι X ≫ CochainComplex.mappingCocone.fst (roosU X) ≫
      Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n =
        limit.π X.asFunctor (op n) := by
  dsimp only [roosι, roosLift]
  rw [← Category.assoc, CochainComplex.mappingCocone.lift_fst, Pi.lift_comp_π]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem moduleEqToHom_section
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {A B : SheafOfModules R}
    (h : A = B) (U : Cᵒᵖ) (x : A.val.obj U) :
    HEq (((eqToHom h).val.app U) x) x := by
  subst h
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem groupEqToHom_section {A B : AddCommGrpCat} (h : A = B) (x : A) :
    HEq ((eqToHom h) x) x := by
  subst h
  rfl

-- Identify section transports without unfolding the scalar-extension witnesses.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem restriction_section
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t})
    (A : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : A.val.obj (op (n, U.unop))) :
    (((eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom.app A).val.app U)
        (integralComparisonRestrictedSection l E Y A n U x) =
      coefficientEvaluationSection l E Y A n U x := by
  simp only [eqToIso.hom, eqToHom_app]
  have hleft := moduleEqToHom_section
    (Functor.congr_obj (coefficientSequenceRestriction_evaluation l E Y n) A) U
    (integralComparisonRestrictedSection l E Y A n U x)
  have hcast : HEq (integralComparisonRestrictedSection l E Y A n U x) x :=
    cast_heq _ x
  have hright : HEq (coefficientEvaluationSection l E Y A n U x) x :=
    groupEqToHom_section (coefficientSequenceEvaluationAb_eq l E Y A n U).symm x
  exact eq_of_heq (hleft.trans (hcast.trans hright.symm))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem normalized_tower_map
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t})
    (K : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (Q : CochainComplex (scalarReductionSource l E Y) ℤ)
    (kappa : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj K ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj Q)
    (a : (((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)).obj
        K).asFunctor ≅ (trfQuotientTowerFunctor l E Y).obj Q)
    (ha : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (x : (K.X i).val.obj (op (n, U.unop))),
      ((a.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l E Y (K.X i) n U x) =
        ((kappa n).hom.f i).val.app U
          (coefficientEvaluationSection l E Y (K.X i) n U x)) (n : ℕ) :
    a.hom.app (op n) =
      (NatIso.mapHomologicalComplex
        (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)) (.up ℤ)).hom.app K ≫
      ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).map
        (kappa n).hom := by
  ext i U x
  obtain ⟨x, rfl⟩ := (Equiv.cast
    (integralComparisonRestrictedSectionType l E Y (K.X i) n U).symm).surjective x
  change ((a.hom.app (op n)).f i).val.app U
    (integralComparisonRestrictedSection l E Y (K.X i) n U x) = _
  rw [ha]
  exact congrArg (((kappa n).hom.f i).val.app U)
    (restriction_section l E Y (K.X i) n U x).symm

-- Explicit comparison between the two published strict quotient presentations.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The actual adjunction unit in the normalized strict quotient cone.
Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md (2)--(3), step 1 of the
normalization node; Stacks 06YY, 07A6, 09T5, 0D6E and 0941.
(blueprint: lem-trf-strict-quotient-completion-unit).

Proof: use M.tensor applied degreewise to P as the simultaneous quotient
presentation. D.reductionComparison is invertible on the given flat-term K-flat
P. The evaluation comparisons are M.evaluation applied to complexes; their
finite equations are D.reduction_evaluation and their horizontal equations are
M.transition. Apply hrho to this presentation. Its strict tower isomorphism a
identifies the original sections through the finite evaluation comparisons.
The ordinary adjunction transpose of the identity has nth component the ordinary
unit followed by the nth limit projection. M.unit_tensor and
M.limitComparison_projection therefore make its image under a the actual
quotient map x to 1 tensor x. The Roos inclusion has zero shifted component.
Both cocone coordinates show that its image under H(a) is exactly
trfStrictQuotientConeAugmentation. D.hom_normalization on the identity, together
with D.systemUnit_composition and D.roos_normalization, identifies its localized
class with the actual S.adjunction.unit, followed by the inverse of
D.completionComparison. The specified compatibility hr identifies r with
D.roos inverse, as holds for the model explicitly constructed in the main proof.
Substitute hrho,
cancel the finite reductionComparison and exact restriction factors, and obtain
the displayed equality of entire derived maps. Zero complexes use the same
universal properties; there is no completeness or boundedness assumption. -/
theorem strictQuotientCompletionUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E Y)
    (M : CompletionUnit.OrdinaryModel l E Y)
    (D : CompletionUnit.DerivedModel l E Y S M)
    (r : IntegralComparisonRoosModel l E Y)
    (rho : integralOperationsGoodLocalization l E Y ⋙
          (S.reduction ⋙ coefficientSequenceLimit l E Y) ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ trfQuotientTowerFunctor l E Y ⋙
          integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
    (hr : ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ,
      r.comparison.hom.app I = D.roos.inv.app I)
    (hrho : TrfCompletionRoosNormalized l E Y S r rho)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫ rho.hom.app P =
      DerivedCategory.Q.map (trfStrictQuotientConeAugmentation l E Y P.obj) := by
  have hP : P.obj.IsKFlatIndependentCoefficients := P.property.1
  have hflat (i : ℤ) : (P.obj.X i).IsFlatOnSite := P.property.2 i
  have := D.reduction_isIso P.obj hP hflat
  let K := (M.quotient l E Y).obj P.obj
  let e := asIso (D.reductionComparison.app P.obj)
  let kappa (n : ℕ) := (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P.obj
  have hp : CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      P.obj hP K e kappa := by
    constructor
    · exact D.reduction_evaluation P.obj hP hflat
    · intro m n h
      ext i : 1
      exact M.transition (P.obj.X i) h
  have hc : IsIntegralComparisonPresentationCoherent l E Y S P.obj K e kappa := by
    unfold IsIntegralComparisonPresentationCoherent
    let b := (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E Y)).mapHomologicalComplex
      (.up ℤ)).homEquiv P.obj ((CompletionUnit.tower l E Y).obj K)).symm
        ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P.obj)
    refine ⟨b, ?_, ?_⟩
    · intro n i U x
      exact ordinary_unit_section l E Y M P.obj n i U x
    · have ht := derivedTranspose l E Y S M D P.obj K (𝟙 K)
      have hQ : DerivedCategory.Q.map (𝟙 K) = 𝟙 (DerivedCategory.Q.obj K) :=
        (DerivedCategory.Q (C := coefficientSequenceModules l E Y)).map_id K
      have hε : D.reductionComparison.app P.obj ≫ DerivedCategory.Q.map (𝟙 K) =
          e.hom := by
        rw [hQ]
        exact Category.comp_id _
      have hM : (M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P.obj K
          (𝟙 K) = (M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P.obj :=
        (M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv_id P.obj
      simp only [hε, hM, Adjunction.homEquiv_unit] at ht
      convert ht using 1
  obtain ⟨a, ha, hrhoa⟩ := hrho P K e kappa hp hc
  have ha' := normalized_tower_map l E Y K P.obj kappa a ha
  let c : P.obj ⟶ integralOperationsRoos
      (((CompletionUnit.tower l E Y).obj K).asFunctor) := M.coneAugmentation l E Y P.obj
  have hf : (c ≫
        integralOperationsRoosFunctor.map a.hom) ≫
        CochainComplex.mappingCocone.fst (trfQuotientDifference l E Y P.obj) =
      (trfStrictQuotientConeAugmentation l E Y P.obj) ≫
        CochainComplex.mappingCocone.fst (trfQuotientDifference l E Y P.obj) := by
    rw [Category.assoc]
    erw [(IntegralAmbient.roosMap_coordinates a.hom).1]
    change c ≫ (CochainComplex.mappingCocone.fst _) ≫ _ = _
    rw [show trfStrictQuotientConeAugmentation l E Y P.obj ≫
      CochainComplex.mappingCocone.fst (trfQuotientDifference l E Y P.obj) =
      Pi.lift (f := fun n : ℕ ↦ ((trfQuotientTowerFunctor l E Y).obj P.obj).obj (op n))
        (fun n : ℕ ↦ unrestrictedTowerUnit l E Y P.obj n) from
      CochainComplex.mappingCocone.lift_fst _ _ _ _]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.map_π, Pi.lift_comp_π]
    have hi := roos_inclusion_fst ((CompletionUnit.tower l E Y).obj K) n
    dsimp only [c, CompletionUnit.OrdinaryModel.coneAugmentation]
    simp only [Category.assoc]
    conv_lhs => rhs; erw [reassoc_of% hi]
    rw [ha' n]
    ext i U x
    exact (CompletionUnit.augmentation_sections l E Y M P.obj i n U x).trans
      (unrestrictedTowerUnit_condition l E Y P.obj n i U x).symm
  have hs (p : ℤ) :
      (c ≫ integralOperationsRoosFunctor.map a.hom).f (p + 1) ≫
        (CochainComplex.mappingCocone.snd (trfQuotientDifference l E Y P.obj)).v
          (p + 1) p (add_neg_cancel_right p 1) = 0 := by
    erw [HomologicalComplex.comp_f, Category.assoc,
      (IntegralAmbient.roosMap_coordinates a.hom).2
        (p + 1) p (add_neg_cancel_right p 1), ← Category.assoc]
    have hz : c.f (p + 1) ≫
        (CochainComplex.mappingCocone.snd
          (scalarRoosBoundary (((CompletionUnit.tower l E Y).obj K).asFunctor))).v
            (p + 1) p (add_neg_cancel_right p 1) = 0 := by
      dsimp only [c, CompletionUnit.OrdinaryModel.coneAugmentation]
      rw [HomologicalComplex.comp_f, Category.assoc]
      change _ ≫ ((roosι _).f (p + 1) ≫
        (CochainComplex.mappingCocone.snd (roosU _)).v _ _ _) = _
      dsimp only [roosι, roosLift]
      rw [CochainComplex.mappingCocone.lift_f_snd_v]
      simp only [CochainComplex.HomComplex.Cochain.zero_v, comp_zero]
    rw [hz, zero_comp]
  have hs' (p : ℤ) :
      (trfStrictQuotientConeAugmentation l E Y P.obj).f (p + 1) ≫
        (CochainComplex.mappingCocone.snd (trfQuotientDifference l E Y P.obj)).v
          (p + 1) p (add_neg_cancel_right p 1) = 0 :=
    CochainComplex.mappingCocone.lift_f_snd_v _ _ _
      (trfStrictQuotientUnit_condition l E Y P.obj) _ _ _
  rw [CompletionUnit.unit_at_complex l E Y D P.obj hP hflat, Category.assoc,
    hrhoa]
  let L := coefficientSequenceLimit l E Y
  let Z := (CompletionUnit.tower l E Y).obj K
  let C := coefficientConstantTowerLimit l E Y
  let f := (coefficientSequenceRestriction l E Y).mapDerivedCategoryFactors.app K
  let e' := L.mapIso e
  let f' := C.mapIso f
  let b := D.roos.app Z
  have hr' : (integralComparisonRoosBridge l E Y r K).hom = f'.hom ≫ b.inv := by
    dsimp only [integralComparisonRoosBridge, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app, f', b]
    rw [hr]
    rfl
  have he' : (D.completionComparison l E Y P.obj hP hflat).hom =
      b.hom ≫ f'.inv ≫ e'.inv := by
    dsimp only [CompletionUnit.DerivedModel.completionComparison, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, b, f', e', f, C, L, Z, K]
  have hm : (D.completionComparison l E Y P.obj hP hflat).hom ≫
      L.map e.hom ≫ (integralComparisonRoosBridge l E Y r K).hom = 𝟙 _ := by
    rw [he', hr']
    change (b.hom ≫ f'.inv ≫ e'.inv) ≫ e'.hom ≫ f'.hom ≫ b.inv = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    rfl
  have hm' := congrArg
    (fun z ↦ DerivedCategory.Q.map (M.coneAugmentation l E Y P.obj) ≫ z ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map a.hom)) hm
  simp only [Category.assoc, Category.id_comp] at hm'
  erw [hm']
  rw [← DerivedCategory.Q.map_comp]
  apply congrArg DerivedCategory.Q.map
  exact cone_hom_ext (trfQuotientDifference l E Y P.obj) _ _ hf hs hs'

end WeilConjectures
