/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.SixFunctors.Tensor.TensorReductionEvaluationIdentification
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictConeCoordinates

/-! # Degreewise coherent lifts of finite tensor comparisons

Transpose the normalized strict tensor cone through the ordinary reduction/limit
adjunction. Source: Stacks 07A4 and 0941.
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

private theorem restrictedLevel_hom_f (W : Scheme.{u}) (n : ℕ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (i : ℤ) :
    (pullbackTensorRestrictedLevel l E W C n).hom.f i =
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (C.X i) := by
  change (𝟙 _ ≫ (eqToIso
    (coefficientSequenceRestriction_evaluation l E W n)).hom.app (C.X i)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

attribute [local implicit_reducible] IntegralOnSlice.ring IntegralOnSlice.restrict
  IntegralOnSlice.topology IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralAmbient.tensorTower pullbackTensorRestrictedTower
  integralOperationsTensorComplexFunctor integralOperationsRoosFunctor
  unrestrictedIntegralReductionFunctor
  integralOperationsRoos integralOperationsTensorTowerFunctor
  integralOperationsTensorLevel integralOperationsTensorComposite integralOperationsFiniteMonoidal
  pullbackTensorOrdinaryLimit

attribute [local irreducible] coefficientSequenceRestriction
  pullbackTensorOrdinaryAdjunction

private theorem reductionEvaluation_inv_f (W : Scheme.{u}) (n : ℕ)
    (C : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) :
    ((pullbackTensorReductionEvaluationComplex l E W n).inv.app C).f i =
      (pullbackTensorReductionEvaluation l E W n).inv.app (C.X i) := by
  change 𝟙 _ ≫ (pullbackTensorReductionEvaluation l E W n).inv.app (C.X i) = _
  exact Category.id_comp _

attribute [local irreducible] pullbackTensorReductionEvaluationComplex

attribute [local implicit_reducible] tensorReductionStrictCone
attribute [local irreducible] tensorReductionStrictConeMap

attribute [local irreducible] pullbackTensorFiniteAdjunction

-- Keep the fixed coefficient models folded while elaborating the projection equation.
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

private def tensorDegreeConeMap (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    (Functor.const ℕᵒᵖ).obj (tensorReductionStrictCone l E W P Q).pt ⟶
      pullbackTensorRestrictedTower l E W B :=
  (tensorReductionStrictCone l E W P Q).π ≫ (pullbackTensorTensorTower l E W P Q).inv

attribute [local irreducible] tensorDegreeConeMap

private def tensorDegreeCone (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) :
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    Cone ((coefficientSequenceRestriction l E W).obj (B.X i)) := by
  dsimp only
  let β := tensorDegreeConeMap l E W P Q
  exact {
    pt := (tensorReductionStrictCone l E W P Q).pt.X i
    π := {
      app := fun n ↦ (β.app n).f i
      naturality := fun m n f ↦ by
        have h := congrArg (fun g ↦ g.f i) (β.naturality f)
        exact h } }

attribute [local implicit_reducible] tensorDegreeCone

private theorem tensorDegreeCone_projection (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) (n : ℕ) :
    (tensorDegreeCone l E W P Q i).π.app (op n) ≫
        ((pullbackTensorTensorTower l E W P Q).hom.app (op n)).f i =
      ((tensorReductionStrictCone l E W P Q).π.app (op n)).f i := by
  change ((tensorDegreeConeMap l E W P Q).app (op n)).f i ≫ _ = _
  unfold tensorDegreeConeMap
  change (((tensorReductionStrictCone l E W P Q).π.app (op n) ≫
    (pullbackTensorTensorTower l E W P Q).inv.app (op n)).f i) ≫ _ = _
  simp only [Category.assoc, ← HomologicalComplex.comp_f,
    Iso.inv_hom_id_app, Category.comp_id]

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
          (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).hom ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
          ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
            (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
              ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q)))) := by
  dsimp only
  have h := (pullbackTensorTensorTower_existsUnique l E W P Q).exists.choose_spec n
  exact congrArg Iso.hom h

private theorem comparison_unique {C : Type*} [Category C]
    {A A' B B' Z : C} (e : A' ≅ A) (s : A' ≅ B) (a : B ≅ B') (k : Z ≅ B')
    (f : A ⟶ Z) (h : e.hom ≫ f ≫ k.hom ≫ a.inv = s.hom) :
    f = e.inv ≫ s.hom ≫ a.hom ≫ k.inv := by
  apply (cancel_epi e.hom).mp
  apply (cancel_mono (k.hom ≫ a.inv)).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, Category.id_comp, Category.comp_id] using h

private theorem transpose_coordinate
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {R : D ⥤ C}
    (adj : F ⊣ R) {M S : C} {V X Y Z : D}
    (ev : F.obj M ⟶ V) (f : V ⟶ X) (k : X ⟶ Y) (t : Y ⟶ Z)
    (β : M ⟶ S) (π : S ⟶ R.obj X) (τ : S ⟶ R.obj Z) (α : M ⟶ R.obj Z)
    (hp : adj.homEquiv M X (ev ≫ f) = β ≫ π)
    (ht : τ = π ≫ R.map k ≫ R.map t) (ha : β ≫ τ = α) :
    adj.homEquiv M Z (ev ≫ f ≫ k ≫ t) = α := by
  have hn : adj.homEquiv M Z (ev ≫ f ≫ k ≫ t) =
      adj.homEquiv M X (ev ≫ f) ≫ R.map k ≫ R.map t := by
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [hn, hp]
  simpa only [Category.assoc] using (congrArg (fun a ↦ β ≫ a) ht).symm.trans ha

set_option cleanup.letToHave false in
-- Several fixed model identifications occur in the two adjunctions.
/-- In each degree the prescribed finite tensor maps are evaluations of one
sequence-module map. Source: Stacks 07A4 and 0941. Transport the strict tensor cone
by the fixed tensor-tower comparison, take its degreewise limit, and transpose
through ordinary coherent reduction. The normalized finite adjunction equations
and cone coordinate formula identify the evaluated map. Cancel the comparison
isomorphisms to obtain the displayed formula. This uses no flatness or boundedness.
(blueprint: lem-coef-tensor-reduction-finite-degree-lift). -/
theorem tensorReductionFiniteDegreeLift (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    ∃ ψ : (G.obj T).X i ⟶ B.X i, ∀ n : ℕ,
      (coefficientSequenceEvaluation l E W n).map ψ =
        ((pullbackTensorReductionEvaluationComplex l E W n).inv.app T ≫
          (coefficientScalarTensorIso l E W n P Q).hom ≫
          (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
            (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).hom.app P)
              ((pullbackTensorReductionEvaluationComplex l E W n).hom.app Q)) ≫
          (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).inv).f i := by
  dsimp only
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let B := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
  let c := tensorDegreeCone l E W P Q i
  let ψ := ((pullbackTensorOrdinaryAdjunction l E W).homEquiv (T.X i) (B.X i)).symm
    (limit.lift _ c)
  refine ⟨ψ, ?_⟩
  intro n
  let R := scalarReductionRestriction l E W n
  let e := (pullbackTensorReductionEvaluation l E W n).app (T.X i)
  let s := coefficientScalarTensorIso l E W n P Q
  let a := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).mapIso
      (Iso.prod ((pullbackTensorReductionEvaluationComplex l E W n).app P)
        ((pullbackTensorReductionEvaluationComplex l E W n).app Q))
  let k := coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)
  have hp := transpose_projection l E W (T.X i) (B.X i) ψ n
  have hψ : (pullbackTensorOrdinaryAdjunction l E W).homEquiv (T.X i) (B.X i) ψ =
      limit.lift _ c := Equiv.apply_symm_apply _ _
  rw [hψ, limit.lift_π_assoc] at hp
  have ht := congrArg (fun f ↦ f.f i) (tensor_tower_level l E W P Q n)
  simp only [HomologicalComplex.comp_f, restrictedLevel_hom_f] at ht
  change ((pullbackTensorTensorTower l E W P Q).hom.app (op n)).f i =
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (B.X i) ≫
      R.map (k.hom.f i) ≫ R.map (a.inv.f i) at ht
  have he := transpose_coordinate (pullbackTensorFiniteAdjunction l E W n)
    e.hom ((coefficientSequenceEvaluation l E W n).map ψ) (k.hom.f i) (a.inv.f i)
    (c.π.app (op n))
    ((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (B.X i))
    (((pullbackTensorTensorTower l E W P Q).hom.app (op n)).f i)
    (((tensorReductionStrictCone l E W P Q).π.app (op n)).f i) hp.symm ht
    (tensorDegreeCone_projection l E W P Q i n)
  have hc := tensorReductionStrictCone_finiteTranspose l E W P Q n
  have hci := congrArg (fun f ↦ f.f i) hc
  change (pullbackTensorFiniteAdjunction l E W n).homEquiv (T.X i) _ (s.hom.f i) =
    ((tensorReductionStrictCone l E W P Q).π.app (op n)).f i at hci
  have hf := ((pullbackTensorFiniteAdjunction l E W n).homEquiv (T.X i) _).injective
    (he.trans hci.symm)
  simp only [HomologicalComplex.comp_f, reductionEvaluation_inv_f]
  exact comparison_unique
    e
    ((HomologicalComplex.eval _ (.up ℤ) i).mapIso s)
    ((HomologicalComplex.eval _ (.up ℤ) i).mapIso a)
    ((HomologicalComplex.eval _ (.up ℤ) i).mapIso k) _ hf

end WeilConjectures
