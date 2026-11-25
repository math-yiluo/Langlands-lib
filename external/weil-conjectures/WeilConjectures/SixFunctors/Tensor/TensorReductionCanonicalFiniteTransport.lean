/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
import WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality

/-! # Finite components of canonical representative transport

Source: Stacks 07A4 and 0941, evaluation of the ordinary tensor comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory pullbackTensorCalculus
attribute [local implicit_reducible]
  unrestrictedIntegralReductionFunctor integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] coefficientSequenceRestriction scalarReductionExtension
  coefficientScalarTensorIso coefficientEvaluationTensorIso
attribute [local implicit_reducible] pullbackTensorReductionEvaluationComplex
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem map_pair_comp
    {C D H : Type*} [Category C] [Category D] [Category H]
    (T : C × D ⥤ H) {P Q R : C} {P' Q' R' : D}
    (a : P ⟶ Q) (b : P' ⟶ Q') (c : Q ⟶ R) (d : Q' ⟶ R') :
    T.map (Prod.mkHom (a ≫ c) (b ≫ d)) =
      T.map (Prod.mkHom a b) ≫ T.map (Prod.mkHom c d) :=
  T.map_comp (Prod.mkHom a b) (Prod.mkHom c d)

private theorem inverse_evaluation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q : C} {R : D} (a : P ≅ Q) (b : F.obj Q ≅ R) (e : R ≅ F.obj P)
    (h : F.map a.hom ≫ b.hom = e.inv) : F.map a.inv = b.hom ≫ e.hom := by
  apply (cancel_epi (F.map a.hom)).1
  rw [← CategoryTheory.Functor.map_comp, a.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [← Category.assoc, h, e.inv_hom_id]

private theorem finite_transport
    {A B : Type*} [Category A] [Category B]
    (V : A ⥤ B) (U : A × A ⥤ A) (F : B × B ⥤ B)
    {GP GQ GT C D Z : A} {SP SQ ST : B}
    (aC : GP ≅ C) (aD : GQ ≅ D) (aZ : GT ≅ Z)
    (κC : V.obj C ≅ SP) (κD : V.obj D ≅ SQ) (κZ : V.obj Z ≅ ST)
    (εC : SP ≅ V.obj GP) (εD : SQ ≅ V.obj GQ) (εZ : ST ≅ V.obj GT)
    (ρ : ST ≅ F.obj (SP, SQ))
    (eCD : V.obj (U.obj (C, D)) ≅ F.obj (V.obj C, V.obj D))
    (eGP : V.obj (U.obj (GP, GQ)) ≅ F.obj (V.obj GP, V.obj GQ))
    (ψ : Z ⟶ U.obj (C, D))
    (hnat : V.map (U.map (Prod.mkHom aC.inv aD.inv)) ≫ eGP.hom =
      eCD.hom ≫ F.map (Prod.mkHom (V.map aC.inv) (V.map aD.inv)))
    (hψ : V.map ψ ≫ eCD.hom ≫ F.map (Prod.mkHom κC.hom κD.hom) = κZ.hom ≫ ρ.hom)
    (hc : V.map aC.hom ≫ κC.hom = εC.inv)
    (hd : V.map aD.hom ≫ κD.hom = εD.inv)
    (hz : V.map aZ.hom ≫ κZ.hom = εZ.inv) :
    V.map (aZ.hom ≫ ψ ≫ U.map (Prod.mkHom aC.inv aD.inv)) =
      εZ.inv ≫ ρ.hom ≫ F.map (Prod.mkHom εC.hom εD.hom) ≫ eGP.inv := by
  have hic := inverse_evaluation V aC κC εC hc
  have hid := inverse_evaluation V aD κD εD hd
  apply (Iso.cancel_iso_hom_right _ _ eGP).1
  simp only [V.map_comp, Category.assoc]
  rw [hnat, hic, hid, map_pair_comp]
  rw [reassoc_of% hψ, reassoc_of% hz]
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- Conjugating a strict tensor comparison by finite-normalized chain isomorphisms
preserves its prescribed finite component maps.

Source: Stacks 07A4 and 0941. Use evaluation-tensor naturality, substitute the three
finite comparison equations, and cancel the evaluation tensor isomorphism. The result
is the finite component of the already assembled strict map. Naturality of the
comparison between the two ordinary evaluation functors gives the literal system maps.
(blueprint: lem-coef-tensor-reduction-canonical-finite-transport). -/
theorem tensorReductionCanonicalFiniteTransport (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let U := coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
    ∀ (C D Z : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (aC : G.obj P ≅ C) (aD : G.obj Q ≅ D) (aZ : G.obj T ≅ Z)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
      (κZ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Z ≅
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj T)
      (ψ : Z ⟶ U.obj (C, D)),
      (∀ n : ℕ, CoefficientComparisonEquation
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ)
        (coefficientEvaluationTensorIso l E W n C D).hom
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
            (Prod.mkHom (κC n).hom (κD n).hom))
        (κZ n).hom (coefficientScalarTensorIso l E W n P Q).hom) →
      (∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map aC.hom ≫
          (κC n).hom = (pullbackTensorReductionEvaluationComplex l E W n).inv.app P) →
      (∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map aD.hom ≫
          (κD n).hom = (pullbackTensorReductionEvaluationComplex l E W n).inv.app Q) →
      (∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map aZ.hom ≫
          (κZ n).hom = (pullbackTensorReductionEvaluationComplex l E W n).inv.app T) →
      ∀ n : ℕ,
        ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
          (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).map
            (aZ.hom ≫ ψ ≫ U.map (Prod.mkHom aC.inv aD.inv)) =
        ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
          (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).map
            (tensorReductionStrictMap l E W P Q) := by
  dsimp only
  intro C D Z aC aD aZ κC κD κZ ψ hfinite haC haD haZ
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let U := coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  let φ : G.obj T ⟶ U.obj (G.obj P, G.obj Q) :=
    aZ.hom ≫ ψ ≫ U.map (Prod.mkHom aC.inv aD.inv)
  intro n
  let V := (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)
  let F := coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  have hφ : V.map φ = tensorReductionFiniteComponent l E W P Q n := by
    have h := finite_transport V U F aC aD aZ (κC n) (κD n) (κZ n)
      ((pullbackTensorReductionEvaluationComplex l E W n).app P)
      ((pullbackTensorReductionEvaluationComplex l E W n).app Q)
      ((pullbackTensorReductionEvaluationComplex l E W n).app T)
      (coefficientScalarTensorIso l E W n P Q)
      (coefficientEvaluationTensorIso l E W n C D)
      (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)) ψ
      (pullbackTensorEvaluationTensor_naturality l E W n aC.inv aD.inv)
      (hfinite n) (haC n) (haD n) (haZ n)
    simpa only [φ, tensorReductionFiniteComponent, Iso.app_hom, Iso.app_inv] using h
  have hstrict : V.map φ = V.map (tensorReductionStrictMap l E W P Q) :=
    hφ.trans (tensorReductionStrictMap_component l E W P Q n).symm
  let e := tensorReductionEvaluationComplexIso l E W n
  apply (cancel_epi (e.hom.app (G.obj T))).1
  exact (e.hom.naturality φ).symm.trans
    ((congrArg (fun f ↦ f ≫ e.hom.app (U.obj (G.obj P, G.obj Q))) hstrict).trans
      (e.hom.naturality (tensorReductionStrictMap l E W P Q)))

end WeilConjectures
