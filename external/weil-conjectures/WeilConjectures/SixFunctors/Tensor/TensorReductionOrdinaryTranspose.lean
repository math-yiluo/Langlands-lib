/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationConstruction
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentation
import WeilConjectures.SixFunctors.Tensor.TensorReductionFiniteTransposeCoordinates
import WeilConjectures.SixFunctors.Tensor.TensorReductionFiniteProjection
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Ordinary transpose of the strict balanced tensor map

Source: Stacks 07A4, 07A6 and 0941; the simultaneous representative normalization
of the coefficient-system calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option cleanup.letToHave false
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
attribute [local implicit_reducible] pullbackTensorOrdinaryLimit pullbackTensorConstantLimit
  integralOperationsRoos pullbackTensorRoosUnit integralOperationsTensorTowerFunctor
  integralOperationsTensorLevel integralOperationsTensorComposite integralOperationsFiniteMonoidal
  pullbackTensorRestrictedTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem comp_four_congr {A : Type*} [Category* A]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Y : A} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)
    (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) (k : X₅ ⟶ X₆)
    (a : X₂ ⟶ Y) (b : Y ⟶ X₆) (hh : h ≫ i ≫ j ≫ k = a ≫ b) :
    ((f ≫ g ≫ h ≫ i) ≫ j) ≫ k = f ≫ g ≫ a ≫ b := by
  simpa only [Category.assoc] using congrArg (fun t ↦ f ≫ g ≫ t) hh

private theorem complex_comp_zero {A : Type*} [Category* A] [HasZeroMorphisms A]
    {B C D E F : CochainComplex A ℤ} (f : B ⟶ C) (g : C ⟶ D)
    (h : D ⟶ E) (k : E ⟶ F) (i : ℤ) {X : A} (s : F.X i ⟶ X)
    (hz : (h ≫ k).f i ≫ s = 0) : (f ≫ g ≫ h ≫ k).f i ≫ s = 0 := by
  simp only [HomologicalComplex.comp_f, Category.assoc] at hz ⊢
  rw [hz, comp_zero, comp_zero]

private theorem roos_projection (W : Scheme.{u})
    (C : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ)
    (D : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ)
    (τ : HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj C ⟶ D) (n : ℕ) :
    pullbackTensorRoosUnit l E W C ≫ integralOperationsRoosMap τ ≫
        CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism (K := fun j ↦ D.obj (op j))
            (integralOperationsTowerStep D)) ≫ Pi.π (fun j ↦ D.obj (op j)) n =
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app C ≫ τ.app (op n) := by
  rw [← Category.assoc (integralOperationsRoosMap τ),
    (IntegralAmbient.roosMap_coordinates τ).1]
  simp only [← Category.assoc]
  rw [show pullbackTensorRoosUnit l E W C ≫ _ =
      pullbackTensorRoosAugmentation l E W C from
    CochainComplex.mappingCocone.lift_fst _ _ _ _]
  simp only [Category.assoc, Pi.map_π, pullbackTensorRoosAugmentation]
  erw [Pi.lift_comp_π_assoc]
  rfl

private theorem roos_shifted_zero (W : Scheme.{u})
    (C : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ)
    (D : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ)
    (τ : HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj C ⟶ D) (i : ℤ) :
    (pullbackTensorRoosUnit l E W C ≫ integralOperationsRoosMap τ).f i ≫
        (CochainComplex.mappingCocone.snd
          (towerTransitionEndomorphism (K := fun j ↦ D.obj (op j))
            (integralOperationsTowerStep D))).v i (i - 1) (by omega) = 0 := by
  rw [HomologicalComplex.comp_f, Category.assoc,
    (IntegralAmbient.roosMap_coordinates τ).2 i (i - 1) (by omega), ← Category.assoc]
  rw [show (pullbackTensorRoosUnit l E W C).f i ≫ _ = 0 from
    CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ i (i - 1) (by omega)]
  simp only [zero_comp]

attribute [local irreducible] coefficientTotalTensor pullbackTensorTensorTower
  coefficientScalarTensorIso coefficientEvaluationTensorIso
  pullbackTensorReductionEvaluationComplex StrictTensorAugmentation.map
  pullbackTensorFiniteAdjunction pullbackTensorOrdinaryAdjunction
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor unrestrictedIntegralReductionFunctor

-- The normalized total-tensor source appears in both adjunctions and the Roos coordinates.
/-- The ordinary transpose of the balanced scalar tensor chain map has the
quotient pure-tensor coordinates and zero shifted coordinate in the full Roos
complex. No derived category, K-flatness or good-representative hypothesis occurs
in this assertion.

Source: Stacks 07A4, 07A6 and 0941; the ordinary scalar tensor unit formulas.

Proof: project the ordinary adjunction transpose to level n. The defining Hom
transpose equation of pullbackTensorReductionEvaluation identifies this projection
with the finite scalar adjunction unit, whose section formula is 1 tensor x.
The assumed finite chain equation and coefficientScalarTensorIso's pure-tensor
formula therefore send each homogeneous x tensor y to
(1 tensor x) tensor (1 tensor y). The ordinary-limit Roos lift has zero shifted
coordinate. The specified tensor tower comparison has exactly the displayed
finite components and its Roos map preserves both coordinates. Compare with
StrictTensorAugmentation.coordinates on pure generators. Tensor sheafification
and total-summand injections give equality of each product projection; product
extensionality gives the first coordinate, and both shifted coordinates vanish.
The two-coordinate mapping-cocone extensionality theorem proves the equality.
The zero complex, empty site and positive exponent one use these same equations.
(blueprint: lem-coef-tensor-reduction-ordinary-transpose). -/
theorem tensorReduction_ordinaryTranspose (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    ∀ ψ : G.obj T ⟶ B,
      (∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ ≫
          (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).hom ≫
          (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
            (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
              ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q)) =
        (pullbackTensorReductionEvaluationComplex l E W n).inv.app T ≫
          (coefficientScalarTensorIso l E W n P Q).hom) →
      ((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).homEquiv
          T B ψ ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app B ≫
        pullbackTensorRoosUnit l E W
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj B) ≫
        integralOperationsRoosMap (pullbackTensorTensorTower l E W P Q).hom =
      (StrictTensorAugmentation.map l E W).app (P, Q) := by
  dsimp only
  intro ψ hψ
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let B := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
  let C := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj B
  let D := (integralOperationsTensorTowerFunctor l E W).obj (P, Q)
  let τ := (pullbackTensorTensorTower l E W P Q).hom
  let a := ((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).homEquiv
    T B ψ
  let e := (Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceRestriction l E W ⋙
      pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app B
  refine StrictTensorAugmentation.mappingCocone_hom_ext (M := T)
    (towerTransitionEndomorphism (K := fun j ↦ D.obj (op j)) (integralOperationsTowerStep D))
    (f := a ≫ e ≫ pullbackTensorRoosUnit l E W C ≫ integralOperationsRoosMap τ)
    (g := (StrictTensorAugmentation.map l E W).app (P, Q)) ?_ ?_
  · apply Pi.hom_ext
    intro n
    have hr := roos_projection l E W C D τ n
    calc
      _ = a ≫ e ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app C ≫
          τ.app (op n) := by
        exact comp_four_congr a e _ _ _ _ _ _ hr
      _ = _ := by
        have h₁ := tensorReduction_finiteProjection l E W P Q ψ n (hψ n)
        have h₂ := tensorReduction_finiteTransposeCoordinates l E W P Q n
        dsimp only [a, e, C, D, τ, T, B, G]
        unfold coefficientTotalTensor at h₁ h₂ ⊢
        have h := h₁.trans h₂
        exact h
  · intro i
    have hz := roos_shifted_zero l E W C D τ i
    have h := (StrictTensorAugmentation.coordinates l E W).2 P Q i
    exact (complex_comp_zero a e (pullbackTensorRoosUnit l E W C)
      (integralOperationsRoosMap τ) i _ hz).trans h.symm

end WeilConjectures
