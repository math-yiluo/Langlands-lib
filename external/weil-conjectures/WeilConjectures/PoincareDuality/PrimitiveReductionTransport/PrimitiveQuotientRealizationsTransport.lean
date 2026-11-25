/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationsUnique

/-! # Transport of normalized primitive realizations between reduction calculi

Source: the normalization of whole-system quotient presentations in the blueprint
operations construction; the canonical uniqueness isomorphism of left adjoints
(blueprint: lem-pod-primitive-quotient-realizations-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.PrimitiveReductionTransport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel
  coefficientSequenceRestriction coefficientSequenceLimit
  integralDerivedPullback integralScalarExtensionOfUniverses

private theorem reduction_transport_evaluation
    (W : AlgebraicGeometry.Scheme.{u})
    (S T : CoefficientDerivedSystemCalculus l E W)
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

private theorem presentation_transport
    (W : AlgebraicGeometry.Scheme.{u})
    (S T : CoefficientDerivedSystemCalculus l E W)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P.obj)
    (hp : CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ) :
    CoefficientReductionPresentation l E W T.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C
      ((T.adjunction.leftAdjointUniq S.adjunction).app _ ≪≫ e) κ := by
  refine ⟨?_, hp.2⟩
  intro n
  dsimp only [CoefficientComparisonEquation, Iso.trans_hom, Iso.app_hom]
  rw [Functor.map_comp, Category.assoc, hp.1 n, ← Category.assoc,
    reduction_transport_evaluation]

@[irreducible] private def transportedPullbackModel
    {V W : AlgebraicGeometry.Scheme.{u}} (f : V ⟶ W)
    (S T : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E V)
    (M : IntegralComparisonPullbackModel l E f T ρ) :
    IntegralComparisonPullbackModel l E f S ρ where
  realization := M.realization ≪≫ Functor.isoWhiskerRight
    (T.adjunction.leftAdjointUniq S.adjunction)
    (integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E V)
  normalization := by
    intro P C e κ hp hc
    let a := T.adjunction.leftAdjointUniq S.adjunction
    have hpT := presentation_transport l E W S T P C e κ hp
    have hcT : IsIntegralComparisonPresentationCoherent l E W T P.obj C
        (a.app _ ≪≫ e) κ := by
      unfold IsIntegralComparisonPresentationCoherent at hc ⊢
      obtain ⟨b, hb, he⟩ := hc
      refine ⟨b, hb, ?_⟩
      have hu : T.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientSequenceLimit l E W).map ((a.app _ ≪≫ e).hom) =
          S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
            (coefficientSequenceLimit l E W).map e.hom := by
        dsimp only [a, Iso.trans_hom, Iso.app_hom]
        rw [Functor.map_comp, ← Category.assoc,
          Adjunction.unit_leftAdjointUniq_hom_app]
      rw [hu]
      exact he
    obtain ⟨q, hq, he⟩ := M.normalization P C (a.app _ ≪≫ e) κ hpT hcT
    refine ⟨q, hq, ?_⟩
    simpa only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.comp_map,
      Functor.map_comp, Category.assoc] using he

@[irreducible] private def transportedScalarModel
    (W : AlgebraicGeometry.Scheme.{u})
    (S T : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l L W)
    (M : IntegralComparisonScalarModel l E L ι W T ρ) :
    IntegralComparisonScalarModel l E L ι W S ρ where
  realization := M.realization ≪≫ Functor.isoWhiskerRight
    (T.adjunction.leftAdjointUniq S.adjunction)
    (integralComparisonDerivedSequenceScalar l E L ι W ⋙ coefficientSequenceLimit l L W)
  normalization := by
    intro P C e κ hp hc
    let a := T.adjunction.leftAdjointUniq S.adjunction
    have hpT := presentation_transport l E W S T P C e κ hp
    have hcT : IsIntegralComparisonPresentationCoherent l E W T P.obj C
        (a.app _ ≪≫ e) κ := by
      unfold IsIntegralComparisonPresentationCoherent at hc ⊢
      obtain ⟨b, hb, he⟩ := hc
      refine ⟨b, hb, ?_⟩
      have hu : T.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientSequenceLimit l E W).map ((a.app _ ≪≫ e).hom) =
          S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
            (coefficientSequenceLimit l E W).map e.hom := by
        dsimp only [a, Iso.trans_hom, Iso.app_hom]
        rw [Functor.map_comp, ← Category.assoc,
          Adjunction.unit_leftAdjointUniq_hom_app]
      rw [hu]
      exact he
    obtain ⟨q, hq, he⟩ := M.normalization P C (a.app _ ≪≫ e) κ hpT hcT
    refine ⟨q, hq, ?_⟩
    simpa only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.comp_map,
      Functor.map_comp, Category.assoc] using he

/-- Normalized primitive realizations commute with the canonical comparison of
reduction left adjoints. The conclusion compares whole derived quotient systems.

Source: blueprint operations construction, normalized primitive quotient models;
Mathlib's uniqueness of left adjoints
(blueprint: lem-pod-primitive-quotient-realizations-transport).

Proof: let a compare S and T. Injectivity of each finite reduction adjunction,
together with the unit-projection equations, identifies its evaluated maps.
Thus every strict quotient presentation for S transports to T by a inverse.
The whole-system coherence equation transports by the left-adjoint unit equation.
Transport the two T-models back to S by postcomposing their realizations with
L(O(a inverse)). Their original strict quotient witnesses still satisfy the
generator equations and the Roos realization equations, so these transported
models are normalized. Primitive uniqueness identifies any supplied S-model
with the transported one. Postcompose with L(O(a)) and cancel the two canonical
left-adjoint comparisons. This proves both assertions with no assumption on
finite quotient flatness, completeness, or the scheme morphism. For S = T the
comparison is the identity; zero objects and identity coefficient maps are
included without an additional case. -/
theorem realizations_transport
    {V W : AlgebraicGeometry.Scheme.{u}} (f : V ⟶ W)
    (S T : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E V) (σ : IntegralComparisonRoosModel l L W)
    (U : IntegralComparisonPullbackModel l E f T ρ)
    (B : IntegralComparisonScalarModel l E L ι W T σ) :
    (∀ (M : IntegralComparisonPullbackModel l E f S ρ)
      (K : DerivedCategory (integralTowerModules l E W)),
      M.realization.hom.app K ≫ (coefficientSequenceLimit l E V).map
          ((integralComparisonDerivedSequencePullback l E f).map
            ((S.adjunction.leftAdjointUniq T.adjunction).hom.app K)) =
        U.realization.hom.app K) ∧
    (∀ (M : IntegralComparisonScalarModel l E L ι W S σ)
      (K : DerivedCategory (integralTowerModules l E W)),
      M.realization.hom.app K ≫ (coefficientSequenceLimit l L W).map
          ((integralComparisonDerivedSequenceScalar l E L ι W).map
            ((S.adjunction.leftAdjointUniq T.adjunction).hom.app K)) =
        B.realization.hom.app K) := by
  let U' := transportedPullbackModel l E f S T ρ U
  let B' := transportedScalarModel l E L ι W S T σ B
  have h := primitiveQuotientRealizations_unique l E L ι f S ρ σ U' B'
  constructor
  · intro M K
    have he := congrArg (fun a ↦ a.hom.app K) (h.1 M)
    dsimp only [U'] at he
    unfold transportedPullbackModel at he
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.comp_map] at he
    rw [he]
    simp only [Category.assoc, ← Functor.map_comp,
      Adjunction.leftAdjointUniq_trans_app, Adjunction.leftAdjointUniq_refl,
      NatTrans.id_app, CategoryTheory.Functor.map_id]
    erw [CategoryTheory.Category.comp_id]
  · intro M K
    have he := congrArg (fun a ↦ a.hom.app K) (h.2 M)
    dsimp only [B'] at he
    unfold transportedScalarModel at he
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.comp_map] at he
    rw [he]
    simp only [Category.assoc, ← Functor.map_comp,
      Adjunction.leftAdjointUniq_trans_app, Adjunction.leftAdjointUniq_refl,
      NatTrans.id_app, CategoryTheory.Functor.map_id]
    erw [CategoryTheory.Category.comp_id]

end WeilConjectures.PrimitiveReductionTransport
