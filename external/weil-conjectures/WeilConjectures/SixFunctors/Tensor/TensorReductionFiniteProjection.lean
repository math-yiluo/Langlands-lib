/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Finite projections of the ordinary tensor transpose

Compute the ordinary reduction/limit transpose at a fixed finite tensor level.
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

private theorem compose_prefix {A : Type*} [Category* A]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : A} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)
    (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) (k : X₅ ⟶ X₆) :
    f ≫ g ≫ h ≫ i ≫ j ≫ k = (f ≫ g ≫ h ≫ i) ≫ j ≫ k := by
  simp only [Category.assoc]

private theorem transpose_postcompose {A B : Type*} [Category* A] [Category* B]
    {F : A ⥤ B} {R : B ⥤ A} (adj : F ⊣ R) {X : A} {Y₀ Y₁ Y₂ Y₃ : B}
    (f : F.obj X ⟶ Y₀) (g : Y₀ ⟶ Y₁) (h : Y₁ ⟶ Y₂) (i : Y₂ ⟶ Y₃) :
    adj.homEquiv X Y₁ (f ≫ g) ≫ R.map h ≫ R.map i =
      adj.homEquiv X Y₃ (f ≫ g ≫ h ≫ i) := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem transpose_cancel {A B : Type*} [Category* A] [Category* B]
    {F : A ⥤ B} {R : B ⥤ A} (adj : F ⊣ R) {X : A} {Y Z : B}
    (e : F.obj X ≅ Y) (f : Y ⟶ Z) (g : F.obj X ⟶ Z) (hf : f = e.inv ≫ g) :
    adj.homEquiv X Z (e.hom ≫ f) = adj.homEquiv X Z g := by
  rw [hf, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem transpose_projection (W : Scheme.{u})
    (M : integralTowerModules l E W) (N : coefficientSequenceModules l E W)
    (ψ : (pullbackTensorOrdinaryReduction l E W).obj M ⟶ N) (n : ℕ) :
    (pullbackTensorOrdinaryAdjunction l E W).homEquiv M N ψ ≫
        limit.π ((coefficientSequenceRestriction l E W).obj N) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app N =
      (pullbackTensorFiniteAdjunction l E W n).homEquiv M _
        ((pullbackTensorReductionEvaluation l E W n).hom.app M ≫
          (coefficientSequenceEvaluation l E W n).map ψ) := by
  have h := (pullbackTensorReductionEvaluation_existsUnique l E W n).exists.choose_spec M
  change (pullbackTensorFiniteAdjunction l E W n).homEquiv M _
    ((pullbackTensorReductionEvaluation l E W n).hom.app M) = _ at h
  rw [Adjunction.homEquiv_naturality_right, h, Adjunction.homEquiv_unit]
  simp only [Category.assoc]
  erw [limMap_π_assoc]
  exact congrArg (fun f ↦ (pullbackTensorOrdinaryAdjunction l E W).unit.app M ≫
    limit.π ((coefficientSequenceRestriction l E W).obj
      ((pullbackTensorOrdinaryReduction l E W).obj M)) (op n) ≫ f)
    ((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.naturality ψ)

private theorem transpose_complex_projection (W : Scheme.{u})
    (M : CochainComplex (integralTowerModules l E W) ℤ)
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (ψ : ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj M ⟶ N)
    (n : ℕ) :
    ((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).homEquiv M N ψ ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app N ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N) ≫
        (pullbackTensorRestrictedLevel l E W N n).hom =
      ((pullbackTensorFiniteAdjunction l E W n).mapHomologicalComplex (.up ℤ)).homEquiv M _
        ((pullbackTensorReductionEvaluationComplex l E W n).hom.app M ≫
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ) := by
  apply HomologicalComplex.hom_ext
  intro k
  exact transpose_projection l E W (M.X k) (N.X k) (ψ.f k) n

private theorem tensor_tower_level (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    @Eq ((pullbackTensorRestrictedTower l E W B).obj (op n) ⟶
        ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n))
      ((pullbackTensorTensorTower l E W P Q).hom.app (op n))
      ((pullbackTensorRestrictedLevel l E W B n).hom ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
          (coefficientEvaluationTensorIso l E W n
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)).hom ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
          ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
            (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
              ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q)))) := by
  dsimp only
  have ht := (pullbackTensorTensorTower_existsUnique l E W P Q).exists.choose_spec n
  change (pullbackTensorTensorTower l E W P Q).app (op n) = _ at ht
  exact congrArg Iso.hom ht

attribute [local irreducible] pullbackTensorTensorTower coefficientScalarTensorIso
  coefficientEvaluationTensorIso pullbackTensorReductionEvaluationComplex

attribute [local irreducible] pullbackTensorFiniteAdjunction pullbackTensorOrdinaryAdjunction

private theorem tensor_level_projection (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    let D := (integralOperationsTensorTowerFunctor l E W).obj (P, Q)
    ∀ (ψ : G.obj T ⟶ B) (n : ℕ),
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ ≫
        (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).hom ≫
        (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
          (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
            ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q)) =
        (pullbackTensorReductionEvaluationComplex l E W n).inv.app T ≫
          (coefficientScalarTensorIso l E W n P Q).hom) →
      @Eq (T ⟶ D.obj (op n))
        (((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).homEquiv
          T B ψ ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app B ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj B) ≫
        (pullbackTensorRestrictedLevel l E W B n).hom ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
          (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).hom ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
          ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
            (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
              ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q))))
      (((pullbackTensorFiniteAdjunction l E W n).mapHomologicalComplex (.up ℤ)).homEquiv T
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
            ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))
        (coefficientScalarTensorIso l E W n P Q).hom) := by
  dsimp only
  intro ψ n hψ
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let B := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
  let C := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj B
  let a := ((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).homEquiv
    T B ψ
  let e := (Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceRestriction l E W ⋙
      pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app B
  let R := (scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)
  let κ := (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).hom
  let t := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).map
      (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
        ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q))
  calc
    _ = (a ≫ e ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app C ≫
        (pullbackTensorRestrictedLevel l E W B n).hom) ≫ R.map κ ≫ R.map t :=
      compose_prefix _ _ _ _ _ _
    _ = ((pullbackTensorFiniteAdjunction l E W n).mapHomologicalComplex (.up ℤ)).homEquiv
        T _ ((pullbackTensorReductionEvaluationComplex l E W n).hom.app T ≫
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ) ≫
        R.map κ ≫ R.map t := by rw [transpose_complex_projection]
    _ = ((pullbackTensorFiniteAdjunction l E W n).mapHomologicalComplex (.up ℤ)).homEquiv
        T _ ((pullbackTensorReductionEvaluationComplex l E W n).hom.app T ≫
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ ≫
            κ ≫ t)) := by
      exact transpose_postcompose _ _ _ _ _
    _ = _ := transpose_cancel _
      ((pullbackTensorReductionEvaluationComplex l E W n).app T) _ _ hψ

/-- A finite projection of the ordinary tensor transpose is the finite scalar
adjunction transpose of the prescribed scalar tensor comparison.

Source: Stacks 07A4 and 0941, the ordinary tensor/limit adjunction and normalized
finite tensor comparisons. Proof: the defining unit equation of the
reduction/evaluation isomorphism identifies a limit projection of the ordinary
transpose with a finite adjunction transpose. The specified tensor-tower component
is the restricted evaluation tensor comparison followed by the two inverse
reduction/evaluation maps. Naturality moves these comparisons inside the finite
transpose. The assumed normalization then cancels the reduction/evaluation
isomorphism and leaves the scalar tensor comparison. All calculations are chain
maps, obtained degreewise from the ordinary module adjunction.
(blueprint: lem-coef-tensor-reduction-finite-projection). -/
theorem tensorReduction_finiteProjection (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    let D := (integralOperationsTensorTowerFunctor l E W).obj (P, Q)
    ∀ (ψ : G.obj T ⟶ B) (n : ℕ),
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ ≫
        (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).hom ≫
        (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
          (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
            ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q)) =
        (pullbackTensorReductionEvaluationComplex l E W n).inv.app T ≫
          (coefficientScalarTensorIso l E W n P Q).hom) →
      @Eq (T ⟶ D.obj (op n))
        (((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).homEquiv
          T B ψ ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app B ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj B) ≫
        (pullbackTensorTensorTower l E W P Q).hom.app (op n))
      (((pullbackTensorFiniteAdjunction l E W n).mapHomologicalComplex (.up ℤ)).homEquiv T
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
            ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))
        (coefficientScalarTensorIso l E W n P Q).hom) := by
  dsimp only
  intro ψ n hψ
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let B := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
  let C := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj B
  let D := (integralOperationsTensorTowerFunctor l E W).obj (P, Q)
  let a := ((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).homEquiv
    T B ψ
  let e := (Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceRestriction l E W ⋙
      pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app B
  have h := tensor_level_projection l E W P Q ψ n hψ
  have ht := tensor_tower_level l E W P Q n
  have ht' := congrArg
    (fun f : (pullbackTensorRestrictedTower l E W B).obj (op n) ⟶ D.obj (op n) ↦
      a ≫ e ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app C ≫ f) ht
  exact ht'.trans h

end WeilConjectures
