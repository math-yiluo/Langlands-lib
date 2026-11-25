/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.SixFunctors.Tensor.TensorReductionEvaluationIdentification
import WeilConjectures.SixFunctors.Tensor.TensorReductionFiniteDegreeLift

/-! # Finite components of ordinary reduction tensor comparison

Source: Stacks 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory pullbackTensorCalculus
attribute [local irreducible] coefficientScalarTensorIso coefficientEvaluationTensorIso
  constantSheaf
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem SheafOfModules.systemSequenceRing
  SheafOfModules.systemSequenceRingPresheaf
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The balanced finite scalar tensor map, transported to ordinary reductions.
Source: Stacks 07A4 (blueprint: lem-coef-tensor-reduction-finite-components). -/
def tensorReductionFiniteComponent (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj (G.obj T) ⟶
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj B :=
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  (pullbackTensorReductionEvaluationComplex l E W n).inv.app T ≫
    (coefficientScalarTensorIso l E W n P Q).hom ≫
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).map
      (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).hom.app P)
        ((pullbackTensorReductionEvaluationComplex l E W n).hom.app Q)) ≫
    (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).inv

/-- The same component using literal vertical evaluation of the sequence ring.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-finite-components). -/
def tensorReductionSystemFiniteComponent (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).obj
          (G.obj T) ⟶
      ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).obj B :=
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let B := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
  let e := tensorReductionEvaluationComplexIso l E W n
  e.inv.app (G.obj T) ≫ tensorReductionFiniteComponent l E W P Q n ≫ e.hom.app B

private theorem conjugate_map
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    {X Y : C} (f : X ⟶ Y) (a : F.obj X ⟶ F.obj Y) (h : F.map f = a) :
    e.inv.app X ≫ a ≫ e.hom.app Y = G.map f := by
  rw [← h, ← e.inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app, Category.comp_id]

attribute [local implicit_reducible] Functor.ofOpSequence Functor.ofSequence
attribute [local irreducible] coefficientTotalTensor coefficientSequenceEvaluation
  SheafOfModules.systemSequenceEvaluation pullbackTensorOrdinaryReduction

private theorem evaluationIso_component (W : Scheme.{u}) (n : ℕ)
    (M N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj M ⟶
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj N)
    (i : ℤ) :
    ((tensorReductionEvaluationComplexIso l E W n).inv.app M ≫ a ≫
      (tensorReductionEvaluationComplexIso l E W n).hom.app N).f i =
      (eqToIso (tensorReduction_evaluation_eq l E W n)).inv.app (M.X i) ≫ a.f i ≫
        (eqToIso (tensorReduction_evaluation_eq l E W n)).hom.app (N.X i) := by
  unfold tensorReductionEvaluationComplexIso
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    NatIso.mapHomologicalComplex_hom_app_f]

private theorem tensorDegreeMap_literal (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) (n : ℕ)
    (ψ : let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
      let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
      let B := (coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
      (G.obj T).X i ⟶ B.X i)
    (hψ : (coefficientSequenceEvaluation l E W n).map ψ =
      (tensorReductionFiniteComponent l E W P Q n).f i) :
    (tensorReductionSystemFiniteComponent l E W P Q n).f i =
      (tensorReductionLiteralEvaluation l E W n).map ψ := by
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let B := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
  unfold tensorReductionSystemFiniteComponent
  dsimp only
  exact (evaluationIso_component l E W n (G.obj T) B
    (tensorReductionFiniteComponent l E W P Q n) i).trans
      (conjugate_map (eqToIso (tensorReduction_evaluation_eq l E W n)) ψ
        ((tensorReductionFiniteComponent l E W P Q n).f i) hψ)

private theorem literal_transition_naturality (W : Scheme.{u})
    {M N : coefficientSequenceModules l E W} (f : M ⟶ N) {m n : ℕ} (h : m ≤ n) :
    (tensorReductionLiteralEvaluation l E W n).map f ≫
        SheafOfModules.sequenceSystemTransition (coefficientSequenceCommRingSystem l E W) N h =
      SheafOfModules.sequenceSystemTransition (coefficientSequenceCommRingSystem l E W) M h ≫
        (SheafOfModules.systemRestriction (coefficientSequenceCommRingSystem l E W) h).map
          ((tensorReductionLiteralEvaluation l E W m).map f) := by
  exact ((SheafOfModules.sequenceToStrictSystemFunctor
    (coefficientSequenceCommRingSystem l E W)).map f).comm h

/-- The balanced finite tensor maps commute with every quotient transition,
before localization, without K-flatness or flat-term hypotheses.

Source: Stacks 07A4 and 0941; step 1 of
lem-coef-tensor-reduction-ordinary-model.
Proof: use the ordinary reduction/evaluation adjunction-unit equations to replace
both finite reductions by scalar extension. Transpose through the scalar
adjunction at level n. On the total summand of bidegree (p,q), both routes send
b tensor (x tensor y) to the tensor of the two quotient reductions, multiplying
b into the first factor. Scalar balancing gives equality for all b. The ordinary
scalar and evaluation tensor comparisons have exactly these generator formulas.
Sheafification and the total-summand universal properties give equality in each
degree. The formula uses the actual quotient maps, hence works also for m = n;
zero complexes and the empty site give the same equality of zero maps.
(blueprint: lem-coef-tensor-reduction-finite-components). -/
theorem tensorReductionFiniteComponents_compatible (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    ∀ (i : ℤ) {m n : ℕ} (h : m ≤ n),
      (tensorReductionSystemFiniteComponent l E W P Q n).f i ≫
          SheafOfModules.sequenceSystemTransition
            (coefficientSequenceCommRingSystem l E W) (B.X i) h =
        SheafOfModules.sequenceSystemTransition
            (coefficientSequenceCommRingSystem l E W) ((G.obj T).X i) h ≫
          (SheafOfModules.systemRestriction (coefficientSequenceCommRingSystem l E W) h).map
            ((tensorReductionSystemFiniteComponent l E W P Q m).f i) := by
  dsimp only
  intro i m n h
  obtain ⟨ψ, hψ⟩ := tensorReductionFiniteDegreeLift l E W P Q i
  change ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).map ψ =
    (tensorReductionFiniteComponent l E W P Q n).f i at hψ
  rw [tensorDegreeMap_literal l E W P Q i n ψ (hψ n),
    tensorDegreeMap_literal l E W P Q i m ψ (hψ m)]
  exact literal_transition_naturality l E W ψ h

end WeilConjectures
