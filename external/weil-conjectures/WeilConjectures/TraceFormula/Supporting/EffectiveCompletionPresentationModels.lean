/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import WeilConjectures.TraceFormula.Supporting.StrictQuotientCompletionRealization
import all WeilConjectures.TraceFormula.Supporting.StrictQuotientCompletionUnit
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation

/-! # Completion-unit normalization on simultaneous quotient presentations

Source: Stacks 0941, the strict quotient augmentation construction and its
transport to simultaneous flat-term K-flat quotient presentations.
(blueprint: lem-trf-effective-completion-presentation-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence coefficientSequenceRestriction
  coefficientSequenceEvaluation unrestrictedTowerUnit coefficientConstantTowerLimit

/-- The actual completion unit is the strict quotient augmentation on every
whole-system coherent flat-term K-flat presentation, using one fixed reduction calculus
and one fixed natural Roos comparison.

Source: Stacks 03EK, 07A6, 09T5, 0D6E and 0941; the actual-unit refinement
lem-trf-strict-quotient-completion-unit and normalized strict presentation comparison
lem-trf-strict-quotient-completion-realization.
(blueprint: lem-trf-effective-completion-presentation-models).

Proof: choose S, its ordinary quotient tensor/limit adjunction M and its compatible
derived comparison D from CompletionUnit.canonicalModels. The inverse of D.roos
is the Roos comparison: its normalization on K-injective towers follows by
cancelling the invertible localized ordinary-limit inclusion. Apply
strictQuotientCompletionRealization to get one natural comparison rho normalized
on every whole-system coherent simultaneous presentation. For a flat-term K-flat
P, strictQuotientCompletionUnit identifies the actual unit followed by rho with
the localization of the strict quotient augmentation b. For any coherent presentation C,
rho's normalization gives a strict tower isomorphism a from the restriction of C
to the ordinary quotient tower of P. Set v=b followed by H(a inverse). Its nth
product coordinate is the ordinary tensor unit followed by Res(kappa inverse)
and the canonical restriction/evaluation identification. Sectionwise this is
exactly the required cast of kappa inverse applied to 1 tensor x. The Roos map
is diagonal in its two cocone coordinates, so the shifted coordinate stays zero.
Finally postcompose the desired derived equality with Q(H(a)). Its left side
becomes unit followed by rho, while its right side becomes Q(b), by the inverse
identity. The strict-quotient unit theorem proves their equality; cancellation
of the isomorphism proves the required entire derived-morphism equation.
This construction applies to every coherent presentation and to the zero complex without
completeness or bounds. -/
theorem effectiveCompletionPresentationModels
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t})
    [∀ x : X, Invertible (l : X.residueField x)] :
    ∃ (S : CoefficientDerivedSystemCalculus l E X)
      (ρ : IntegralComparisonRoosModel l E X),
    ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    IsIntegralComparisonPresentationCoherent l E X S P.obj C e κ →
    ∃ v : P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
        (((v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫ Pi.π (fun m ↦
              ((((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
                C).asFunctor.obj (op m))) n).f i).val.app U) x =
          integralComparisonRestrictedSection l E X (C.X i) n U
            (integralComparisonSequenceSection l E X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x)))) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), v.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor)).v i j h = 0) ∧
      S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E X).map e.hom ≫
        (integralComparisonRoosBridge l E X ρ C).hom = DerivedCategory.Q.map v := by
  classical
  obtain ⟨S, _hS, M, ⟨D⟩⟩ := CompletionUnit.canonicalModels l E X
  let r := roosModel l E X S M D
  obtain ⟨rho, hrho⟩ := strictQuotientCompletionRealization l E X S r
  refine ⟨S, r, ?_⟩
  intro P C e κ hp hc
  obtain ⟨a, ha, hrhoa⟩ := hrho P C e κ hp hc
  let b := trfStrictQuotientConeAugmentation l E X P.obj
  let v := b ≫ integralOperationsRoosFunctor.map a.inv
  have ha' := normalized_tower_map l E X C P.obj κ a ha
  have hinv (n : ℕ) :
      a.inv.app (op n) ≫
        (NatIso.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) (.up ℤ)).hom.app C =
      ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
        (κ n).inv := by
    apply (cancel_mono (((scalarReductionRestriction l E X n).mapHomologicalComplex
      (.up ℤ)).map (κ n).hom)).1
    rw [Category.assoc, ← ha' n]
    rw [Iso.inv_hom_id_app, ← Functor.map_comp, Iso.inv_hom_id]
    exact (((scalarReductionRestriction l E X n).mapHomologicalComplex
      (.up ℤ)).map_id _).symm
  refine ⟨v, ?_, ?_, ?_⟩
  · intro n i U x
    have hv : v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫ Pi.π (fun m ↦
              ((((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
                C).asFunctor.obj (op m))) n =
        unrestrictedTowerUnit l E X P.obj n ≫ a.inv.app (op n) := by
      dsimp only [v]
      rw [Category.assoc,
        ← Category.assoc (integralOperationsRoosFunctor.map a.inv)]
      erw [(IntegralAmbient.roosMap_coordinates a.inv).1]
      rw [← Category.assoc, ← Category.assoc]
      change (b ≫ CochainComplex.mappingCocone.fst _) ≫ _ ≫ _ = _
      dsimp only [b, trfStrictQuotientConeAugmentation]
      rw [CochainComplex.mappingCocone.lift_fst]
      rw [Pi.map_π]
      erw [← Category.assoc, Pi.lift_comp_π]
    rw [hv]
    change ((a.inv.app (op n)).f i).val.app U
      ((((unrestrictedTowerUnit l E X P.obj n).f i).val.app U) x) = _
    rw [unrestrictedTowerUnit_condition]
    let z := ((NatIso.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) (.up ℤ)).app C)
    let zi := (HomologicalComplex.eval _ (.up ℤ) i).mapIso z
    let zu := (SheafOfModules.evaluation _ U).mapIso zi
    apply (ConcreteCategory.bijective_of_isIso zu.hom).1
    have hi := congrArg (fun f ↦ (f.f i).val.app U
      (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x)) (hinv n)
    exact hi.trans (restricted_section_cancel l E X (C.X i) n U _).symm
  · intro i j h
    dsimp only [v]
    erw [HomologicalComplex.comp_f, Category.assoc,
      (IntegralAmbient.roosMap_coordinates a.inv).2 i j h, ← Category.assoc]
    have hb : b.f i ≫
        (CochainComplex.mappingCocone.snd (trfQuotientDifference l E X P.obj)).v i j h =
        0 := CochainComplex.mappingCocone.lift_f_snd_v _ _ _
          (trfStrictQuotientUnit_condition l E X P.obj) i j h
    rw [hb, zero_comp]
  · apply (cancel_mono (DerivedCategory.Q.map
      (integralOperationsRoosFunctor.map a.hom))).1
    simp only [Category.assoc, ← hrhoa]
    have hu := strictQuotientCompletionUnit l E X S M D r rho (fun I ↦ by
      dsimp only [r, roosModel, comparisonFromModel, Iso.trans_hom, NatTrans.comp_app,
        Iso.symm_hom, NatIso.ofComponents_hom_app, Iso.refl_hom]
      exact Category.comp_id _) hrho P
    rw [hu]
    dsimp only [v]
    rw [← DerivedCategory.Q.map_comp, Category.assoc,
      ← integralOperationsRoosFunctor.map_comp, a.inv_hom_id,
      integralOperationsRoosFunctor.map_id]
    exact congrArg DerivedCategory.Q.map (Category.comp_id b).symm

end WeilConjectures
