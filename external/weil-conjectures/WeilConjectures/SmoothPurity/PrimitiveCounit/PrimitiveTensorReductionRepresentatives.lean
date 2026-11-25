/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PrimitiveCounit.PrimitiveCounitComparisonModels
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import all WeilConjectures.SmoothPurity.IntegralCoherence.IntegralGoodQuotientPresentation

/-! # Functorial strict quotient representatives

Source: Stacks Project, Tags 06YY, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PrimitiveCounit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local implicit_reducible] integralOperationsGoodLocalization

/-- Functorial models of reduction on the good category, with strict quotient coordinates
and normalized ordinary units.
Source: Stacks 06YY and 0941.
(blueprint: stage3-v3-primitive-tensor-reduction-representatives). -/
structure ReductionRepresentatives (S : CoefficientDerivedSystemReduction l E W) where
  complexes : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
    CochainComplex (coefficientSequenceModules l E W) ℤ
  good : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients
    (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
    (R := coefficientSequenceCommRingSheaf l E W) (complexes.obj P)
  comparison : integralOperationsGoodLocalization l E W ⋙ S.reduction ≅
    complexes ⋙ DerivedCategory.Q
  evaluation : ∀ n : ℕ,
    complexes ⋙ (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ) ≅
      (integralOperationsGoodComplex l E W).ι ⋙
        (scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)
  presentation : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
    CoefficientReductionPresentation l E W S P.obj P.property.1
    (complexes.obj P) (comparison.app P) (fun n ↦ (evaluation n).app P)

  unit : ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (i : ℤ),
    P.obj.X i ⟶ limit ((coefficientSequenceRestriction l E W).obj ((complexes.obj P).X i))
  unit_evaluation : ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
      (n : ℕ) (i : ℤ),
    unit P i ≫
        limit.π ((coefficientSequenceRestriction l E W).obj ((complexes.obj P).X i)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
          ((complexes.obj P).X i) ≫
        (scalarReductionRestriction l E W n).map (((evaluation n).hom.app P).f i) =
      (coefficientOrdinaryScalarAdjunction l E W n).unit.app (P.obj.X i)

private theorem reduction_transport_evaluation
    (S T : CoefficientDerivedSystemReduction l E W)
    (K : DerivedCategory (integralTowerModules l E W)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).map
        ((S.adjunction.leftAdjointUniq T.adjunction).hom.app K) ≫
      (T.reductionEvaluation n).hom.app K = (S.reductionEvaluation n).hom.app K := by
  let V := coefficientSequenceDerivedEvaluation l E W n
  let R := coefficientFiniteDerivedRestriction l E W n
  let α := S.adjunction.leftAdjointUniq T.adjunction
  have he : (S.reductionEvaluation n).inv.app K ≫ V.map (α.hom.app K) =
      (T.reductionEvaluation n).inv.app K := by
    apply ((coefficientFiniteAdjunction l E W n).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R.map_comp,
      ← Category.assoc, ← S.unit_projection]
    have hp := (coefficientSequenceProjection l E W n).naturality (α.hom.app K)
    dsimp only [Functor.comp_map] at hp
    rw [Category.assoc, ← hp, ← Category.assoc]
    rw [Adjunction.unit_leftAdjointUniq_hom_app, T.unit_projection]
  apply (cancel_epi ((S.reductionEvaluation n).inv.app K)).1
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
    congrArg (fun f ↦ f ≫ (T.reductionEvaluation n).hom.app K) he

/-- The actual quotient functor gives simultaneous functorial reduction models.
Source: Stacks 06YY, 07A4 and 0941; the reduction part of step 1 of
lem-pur-primitive-counit-tensor-realization.
(blueprint: stage3-v3-primitive-tensor-reduction-representatives).

Proof: take the ordinary model constructed by CompletionUnit.ordinaryModel_exists
and its normalized derived comparison for a coherent calculus T. Restrict its
quotient functor and finite evaluation isomorphisms to good complexes. Each finite
scalar extension preserves K-flatness, and kflat_of_levels gives K-flatness on the
sequence site. Uniqueness of the left adjoint to the fixed coefficient limit
transports the normalized comparison from T.reduction to S.reduction. The finite
unit projection equations identify the transported comparison with
S.reductionEvaluation. The ordinary model transition formula supplies the strict
quotient transition clause. Its ordinary unit supplies the degreewise cone unit,
whose finite evaluations are the normalized scalar units by unit_tensor.
These formulas also cover zero complexes, level zero
and the empty scheme. -/
theorem reductionRepresentatives_nonempty
    (S : CoefficientDerivedSystemReduction l E W) :
    Nonempty (ReductionRepresentatives l E W S) := by
  classical
  obtain ⟨T, _⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  obtain ⟨M⟩ := CompletionUnit.ordinaryModel_exists l E W
  obtain ⟨ε, hiso, heval, _⟩ := WeilConjectures.normalized_comparison l E W T M
  let G := integralOperationsGoodComplex l E W
  let F := G.ι ⋙ M.quotient l E W
  let κ (n : ℕ) := Functor.isoWhiskerLeft G.ι
    (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ))
  let e : integralOperationsGoodLocalization l E W ⋙ T.reduction ≅
      F ⋙ DerivedCategory.Q := NatIso.ofComponents
    (fun P ↦ by
      haveI := hiso P
      exact asIso (ε.app P.obj))
    (by intro P Q f; exact ε.naturality f.hom)
  let d := S.adjunction.leftAdjointUniq T.adjunction
  let e' := Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E W) d ≪≫ e
  refine ⟨{ complexes := F
            good := ?_
            comparison := e'
            evaluation := κ
            presentation := ?_
            unit := fun P i ↦ M.adjunction.unit.app (P.obj.X i)
            unit_evaluation := ?_ }⟩
  · intro P
    apply WeilConjectures.kflat_of_levels l E W
    intro n
    exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E W n)
      ((κ n).app P).symm
      ((coefficientTensorModelPreservation l E W).1 P.obj P.property.1 n)
  · intro P
    constructor
    · intro n
      change (coefficientSequenceDerivedEvaluation l E W n).map
          (d.hom.app (DerivedCategory.Q.obj P.obj) ≫ ε.app P.obj) ≫
          (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
            ((M.quotient l E W).obj P.obj) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P.obj) = _
      rw [Functor.map_comp, Category.assoc]
      have ht := heval P n
      change (coefficientSequenceDerivedEvaluation l E W n).map
          (ε.app P.obj) ≫ _ = _ at ht
      erw [ht, ← Category.assoc]
      exact congrArg (fun f ↦ f ≫
        (coefficientFiniteReductionModel l E W P.obj P.property.1 n).hom)
        (reduction_transport_evaluation l E W S T.toCoefficientDerivedSystemReduction
          (DerivedCategory.Q.obj P.obj) n)
    · intro m n h
      apply HomologicalComplex.hom_ext
      intro i
      exact M.transition (P.obj.X i) h
  · intro P n i
    ext U x
    have hu := (scalarReductionExtension_adjunction l E W n).choose_spec (P.obj.X i) U x
    change ((coefficientOrdinaryScalarAdjunction l E W n).unit.app
      (P.obj.X i)).val.app U x =
        unrestrictedIntegralTensorSection l E W n (P.obj.X i) U 1 x at hu
    exact (M.unit_tensor (P.obj.X i) n U x).trans hu.symm

end WeilConjectures.PrimitiveCounit
