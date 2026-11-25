/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.GeneratorReduction.RingedTensorChainIdentification
import WeilConjectures.SixFunctors.Tensor.TensorReductionOrdinaryModel
import WeilConjectures.SixFunctors.Tensor.TensorReductionOrdinaryTranspose
import WeilConjectures.SixFunctors.Supporting.LimitUnitRoosNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Tensor transpose on good representatives

Source: current blueprint fix-prop-coherence, primitive comparisons
(blueprint: lem-sf-tensor-quotient-augmentation-on-good).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  StrictTensorAugmentation.map
attribute [local implicit_reducible] PurCompactSupport.completed
  integralOperationsGoodLocalization
  pullbackTensorOrdinaryLimit pullbackTensorConstantLimit pullbackTensorTowerQ
  coefficientConstantTowerLimit coefficientSequenceLimit
  integralOperationsTensorComplexFunctor integralOperationsRoos integralOperationsRoosFunctor
  IntegralOnSlice.Site IntegralOnSlice.topology IntegralOnSlice.ring IntegralOnSlice.Good
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem limitUnit_natural (W : Scheme.{u})
    {C D : CochainComplex (coefficientSequenceModules l E W) ℤ} (f : C ⟶ D) :
    DerivedCategory.Q.map
        (((pullbackTensorOrdinaryLimit l E W).mapHomologicalComplex (.up ℤ)).map f) ≫
      pullbackTensorLimitUnit l E W D =
    pullbackTensorLimitUnit l E W C ≫
      (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map f) := by
  let U := coefficientSequenceRestriction l E W
  let F := pullbackTensorConstantLimit l E W
  let η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun {_ _} g ↦ F.rightDerivedFunctorUnitQ_naturality g }
  let e := Functor.mapHomologicalComplexCompIso (Iso.refl (U ⋙ F)) (.up ℤ)
  let θ := (Functor.isoWhiskerRight e.symm DerivedCategory.Q).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (U.mapHomologicalComplex (.up ℤ)) η ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight U.mapDerivedCategoryFactors.inv F.rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom
  have hη (K : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
      η.app K = F.rightDerivedFunctorUnitQ K := rfl
  have hθ (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
      θ.app K = pullbackTensorLimitUnit l E W K := by
    simp only [θ, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, hη]
    rfl
  change DerivedCategory.Q.map (((U ⋙ F).mapHomologicalComplex (.up ℤ)).map f) ≫
    pullbackTensorLimitUnit l E W D = pullbackTensorLimitUnit l E W C ≫
      F.rightDerivedFunctor.map (U.mapDerivedCategory.map (DerivedCategory.Q.map f))
  simpa only [Functor.comp_map, hθ] using θ.naturality f

private theorem transpose_roos (W : Scheme.{u})
    (T : (integralOperationsGoodComplex l E W).FullSubcategory)
    (B : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (ψ : ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
      T.obj ⟶ B) :
    (pullbackTensorCalculus l E W).adjunction.unit.app (DerivedCategory.Q.obj T.obj) ≫
      (coefficientSequenceLimit l E W).map
        ((pullbackTensorReductionModel l E W).hom.app T ≫ DerivedCategory.Q.map ψ) ≫
      (pullbackTensorLimitRoos l E W B).hom =
    DerivedCategory.Q.map
      (((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).homEquiv
        T.obj B ψ) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app B) ≫
      DerivedCategory.Q.map (pullbackTensorRoosUnit l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj B)) := by
  have h := (pullbackTensorReductionModel_existsUnique l E W).exists.choose_spec T
  change (pullbackTensorCalculus l E W).adjunction.homEquiv _ _
    ((pullbackTensorReductionModel l E W).hom.app T) = _ at h
  rw [Adjunction.homEquiv_unit] at h
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% h, ← reassoc_of% (limitUnit_natural l E W ψ)]
  erw [pullbackTensorLimitUnit_roos]
  simp only [Adjunction.homEquiv_unit, DerivedCategory.Q.map_comp, Category.assoc]
  rfl

private theorem adjunction_unit_comp
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (R : D ⥤ C)
    (a : F ⊣ R) {A B : C} {Z : D} (f : A ⟶ B) (g : F.obj B ⟶ Z) :
    f ≫ a.unit.app B ≫ R.map g = a.unit.app A ≫ R.map (F.map f ≫ g) := by
  simp only [Functor.map_comp]
  simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
    congrArg (fun k ↦ k ≫ R.map g) (a.unit.naturality f)

private theorem unit_reference_transport
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (R : D ⥤ C)
    (a : F ⊣ R) {A B V : C} {Y Z U : D} {H K : C}
    (ρ : A ⟶ B) (α : B ⟶ V) (δ : F.obj V ⟶ Y) (χ : Y ⟶ Z) (τ : Z ⟶ U)
    (σ : F.obj A ⟶ U) (r : R.obj U ⟶ H) (q : H ⟶ K) (e : R.obj Y ⟶ K)
    (hm : F.map ρ ≫ F.map α ≫ δ ≫ χ ≫ τ = σ)
    (he : e = R.map χ ≫ R.map τ ≫ r ≫ q) :
    ρ ≫ a.unit.app B ≫ R.map (F.map α ≫ δ) ≫ e =
      a.unit.app A ≫ R.map σ ≫ r ≫ q := by
  rw [he]
  have h := adjunction_unit_comp F R a ρ (F.map α ≫ δ ≫ χ ≫ τ)
  rw [hm] at h
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ r ≫ q) h

private theorem append_mapped_triple
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B V U H : C} {Y Z : D}
    (a : F.obj A ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ F.obj U)
    (f : A ⟶ B) (g : B ⟶ V) (h : V ⟶ U) (k : U ⟶ H) (w : A ⟶ H)
    (ha : a ≫ b ≫ c = F.map f ≫ F.map g ≫ F.map h)
    (hw : f ≫ g ≫ h ≫ k = w) :
    a ≫ b ≫ c ≫ F.map k = F.map w := by
  have hp := congrArg (fun z ↦ z ≫ F.map k) ha
  have hq := congrArg F.map hw
  simp only [Functor.map_comp, Category.assoc] at hp hq
  exact hp.trans hq

attribute [local irreducible] CoefficientTensorModels.iso
  CoefficientClosedStructure.tensor pullbackTensorCalculus
  integralOperationsTensorTowerFunctor integralOperationsRoos integralOperationsRoosMap
attribute [local implicit_reducible] integralOperationsTensorOnGood
  pullbackTensorReferenceTensor pullbackTensorRestrictedTower

section
attribute [local irreducible] coefficientTotalTensor

private theorem reference_model_hom (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P.obj, G.obj Q.obj)
    (pullbackTensorReferenceTensorModel l E W P Q).hom =
      (coefficientSequenceLimit l E W).map
        ((pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
            ((pullbackTensorReductionModel l E W).hom.app Q))) ≫
      (coefficientSequenceLimit l E W).map
        (pullbackTensorSystemModel l E W _ _
          (pullbackTensorReductionGood l E W P) (pullbackTensorReductionGood l E W Q)).inv ≫
      (pullbackTensorLimitRoos l E W B).hom ≫
      DerivedCategory.Q.map
        (integralOperationsRoosMap (pullbackTensorTensorTower l E W P.obj Q.obj).hom) := by
  simp only [pullbackTensorReferenceTensorModel, Iso.trans_hom,
    Functor.mapIso_hom]
  rfl

end

attribute [local irreducible] pullbackTensorReferenceTensorModel pullbackTensorLimitRoos

/-- The scalar-adjunction transpose of the balanced tensor map is the strict
quotient augmentation, in the published full Roos coordinates.
Source: current blueprint fix-prop-coherence.proof.md, maps-used sentence;
Stacks 07A4, 07A6, 0941.

Proof: transport the ordinary tensor representative using
ringed.tensorRepresentative. Apply reductionTensor_normalization to the good
complexes P and Q: it supplies simultaneous strict presentations C, D, Z and
the balanced chain map Z to the total tensor of C and D. On each homogeneous
pure tensor its finite component reduces each factor. Use the cochain transpose
formula for the derived reduction/limit adjunction. The unit_projection equations
identify the transpose with the quotient maps into the product; the strict
Roos augmentation has zero shifted coordinate. The tensor chain normalization
has exactly these first coordinates and zero shifted coordinate. Tensor
sheafification and total-summand injections prove equality of the first coordinate;
the second coordinate is zero on both sides. Thus the full cochain maps agree.
Localize this equality and compose with the published reduction and system-tensor
representative comparisons. Their product is precisely
pullbackTensorReferenceTensorModel, yielding the displayed equation. This lemma
only computes a transpose on good complexes; the consumer separately uses
Tensor.canonical.2 and the global tensor model, then descends to all objects.
(blueprint: lem-sf-tensor-quotient-augmentation-on-good). -/
theorem tensorQuotientTranspose_onGood
    (ringed : IntegralSystemRealization.RingedModels l E) (X : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (ringed.tensor X).ordinary.representative.hom.app
        (⟨P.obj, P.property⟩, ⟨Q.obj, Q.property⟩) ≫
      (IntegralSystemRealization.calculus l E X).adjunction.unit.app
        ((ringed.tensor X).ordinary.tensor.obj
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
      (coefficientSequenceLimit l E X).map
        ((IntegralSystemRealization.calculus l E X).reduction.map
          (eqToIso (congrArg (fun T ↦ T.obj
            (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
              (ringed.tensorClosed X))).hom ≫
          (IntegralSystemRealization.calculus l E X).reductionTensor.hom.app
            (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
      (pullbackTensorReferenceTensorModel l E X P Q).hom =
      DerivedCategory.Q.map ((ringed.tensor X).chain.app (P.obj, Q.obj)) := by
  let S := pullbackTensorCalculus l E X
  let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X)).obj (P.obj, Q.obj)
  have hT : integralOperationsGoodComplex l E X T :=
    IntegralAmbient.tensor_good l E X P.obj Q.obj P.property Q.property
  obtain ⟨ψ, hψ, hfinite⟩ := tensorReduction_ordinaryModel l E X P Q hT
  have hc := tensorReduction_ordinaryTranspose l E X P.obj Q.obj ψ hfinite
  let G := (pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)
  let B := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)).obj (G.obj P.obj, G.obj Q.obj)
  let α := (eqToIso (congrArg (fun U ↦ U.obj
    (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
      (ringed.tensorClosed X))).hom
  let β := (S.integralTensorModel.iso (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X) S.integralClosed
    P.obj Q.obj P.property.1 Q.property.1).hom
  let ρ := (ringed.tensor X).ordinary.representative.hom.app
      (⟨P.obj, P.property⟩, ⟨Q.obj, Q.property⟩)
  let δ := S.reductionTensor.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
  let χ := S.systemClosed.tensor.map
    (Prod.mkHom ((pullbackTensorReductionModel l E X).hom.app P)
      ((pullbackTensorReductionModel l E X).hom.app Q))
  let τ := (pullbackTensorSystemModel l E X _ _
    (pullbackTensorReductionGood l E X P) (pullbackTensorReductionGood l E X Q)).inv
  let κ := δ ≫ χ ≫ τ
  have hrep : ρ ≫ α = β :=
    ringed.tensorRepresentative X P.obj Q.obj P.property Q.property
  have hcanon : S.reduction.map β ≫ κ =
      (pullbackTensorReductionModel l E X).hom.app ⟨T, hT⟩ ≫ DerivedCategory.Q.map ψ := hψ
  have hm : S.reduction.map ρ ≫ (S.reduction.map α ≫ κ) =
      (pullbackTensorReductionModel l E X).hom.app ⟨T, hT⟩ ≫ DerivedCategory.Q.map ψ :=
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ κ) (S.reduction.map_comp ρ α).symm)).trans
        (congrArg (fun k ↦ S.reduction.map k ≫ κ) hrep)).trans hcanon
  have ht := transpose_roos l E X ⟨T, hT⟩ B ψ
  rw [ringedTensorChain_eq_strictAugmentation l E ringed X]
  change _ = DerivedCategory.Q.map ((StrictTensorAugmentation.map l E X).app (P.obj, Q.obj))
  calc
    _ = S.adjunction.unit.app (DerivedCategory.Q.obj T) ≫
        (coefficientSequenceLimit l E X).map
          ((pullbackTensorReductionModel l E X).hom.app ⟨T, hT⟩ ≫
            DerivedCategory.Q.map ψ) ≫
        (pullbackTensorLimitRoos l E X B).hom ≫
        DerivedCategory.Q.map
          (integralOperationsRoosMap (pullbackTensorTensorTower l E X P.obj Q.obj).hom) := by
      exact unit_reference_transport S.reduction (coefficientSequenceLimit l E X)
        S.adjunction ρ α δ χ τ
        ((pullbackTensorReductionModel l E X).hom.app ⟨T, hT⟩ ≫ DerivedCategory.Q.map ψ)
        (pullbackTensorLimitRoos l E X B).hom
        (DerivedCategory.Q.map
          (integralOperationsRoosMap (pullbackTensorTensorTower l E X P.obj Q.obj).hom))
        (pullbackTensorReferenceTensorModel l E X P Q).hom hm
        (reference_model_hom l E X P Q)
    _ = _ := by
      exact append_mapped_triple DerivedCategory.Q
        (S.adjunction.unit.app (DerivedCategory.Q.obj T))
        ((coefficientSequenceLimit l E X).map
          ((pullbackTensorReductionModel l E X).hom.app ⟨T, hT⟩ ≫ DerivedCategory.Q.map ψ))
        (pullbackTensorLimitRoos l E X B).hom
        (((pullbackTensorOrdinaryAdjunction l E X).mapHomologicalComplex (.up ℤ)).homEquiv
          T B ψ)
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E X ⋙
            pullbackTensorConstantLimit l E X)) (.up ℤ)).inv.app B)
        (pullbackTensorRoosUnit l E X
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj B))
        (integralOperationsRoosMap (pullbackTensorTensorTower l E X P.obj Q.obj).hom)
        ((StrictTensorAugmentation.map l E X).app (P.obj, Q.obj)) ht hc

end WeilConjectures.GeneratorReduction
