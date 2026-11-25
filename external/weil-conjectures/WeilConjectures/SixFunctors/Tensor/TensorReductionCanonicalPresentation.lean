/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SixFunctors.Coefficient.CoefficientReductionUnitPresentation
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all Mathlib.Algebra.Homology.Localization

/-! # Strict adjunction-normalized reduction presentations

Source: Stacks 07A4, 07A6 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option cleanup.letToHave false
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
attribute [local irreducible] pullbackTensorReductionModel
attribute [local implicit_reducible] integralOperationsGoodLocalization
  integralOperationsGoodComplex
  coefficientIntegralTensorModelIso coefficientSystemTensorModelIso
  coefficientKFlatInclusion CoefficientTensorModels.iso
  scalarReductionSourceDerived scalarReductionTargetDerived coefficientSequenceHasDerived
  coefficientFiniteHasDerived coefficientConstantTowerDerived
  unrestrictedIntegralReductionFunctor integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local implicit_reducible] pullbackTensorOrdinaryLimit pullbackTensorConstantLimit
  coefficientConstantTowerLimit coefficientSequenceLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem sheaf_isIso_of_components
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (h : ∀ V, IsIso (f.val.app V)) : IsIso f := by
  let e : M.val ≅ N.val :=
    PresheafOfModules.isoMk (fun V ↦ @asIso _ _ _ _ (f.val.app V) (h V))
      (by intro X Y g; exact f.val.naturality g)
  have : IsIso ((SheafOfModules.forget _).map f) := e.isIso_hom
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

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
        (NatTrans.mapHomologicalComplex
          (Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)))
            (.up ℤ)).app N ≫
        (NatIso.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ)).hom.app N =
      ((pullbackTensorFiniteAdjunction l E W n).mapHomologicalComplex (.up ℤ)).homEquiv M _
        ((pullbackTensorReductionEvaluationComplex l E W n).hom.app M ≫
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ) := by
  apply HomologicalComplex.hom_ext
  intro k
  exact transpose_projection l E W (M.X k) (N.X k) (ψ.f k) n

attribute [local irreducible] constantSheaf coefficientSequenceCommRingSheaf in
private theorem isIso_of_evaluations (W : Scheme.{u})
    {P C : CochainComplex (coefficientSequenceModules l E W) ℤ} (a : P ⟶ C)
    (ha : ∀ n : ℕ,
      IsIso (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a)) :
    IsIso a := by
  have hi (i : ℤ) : IsIso (a.f i) := by
    have hc (V : (ℕ × W.ProEt)ᵒᵖ) : IsIso ((a.f i).val.app V) := by
      let n := V.unop.1
      let U := V.unop.2
      let := ha n
      have : IsIso ((coefficientSequenceEvaluation l E W n).map (a.f i)) :=
        inferInstanceAs (IsIso ((HomologicalComplex.eval _ (.up ℤ) i).map
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a)))
      have h : IsIso
          (((coefficientSequenceEvaluation l E W n).map (a.f i)).val.app (op U)) :=
        inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (op U)).map
          ((coefficientSequenceEvaluation l E W n).map (a.f i))))
      apply (ConcreteCategory.isIso_iff_bijective ((a.f i).val.app V)).2
      exact (ConcreteCategory.isIso_iff_bijective
        (((coefficientSequenceEvaluation l E W n).map (a.f i)).val.app (op U))).1 h
    exact sheaf_isIso_of_components (a.f i) hc
  let := hi
  exact HomologicalComplex.Hom.isIso_of_components a

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
  have hθ (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
      θ.app K = pullbackTensorLimitUnit l E W K := by
    simp only [θ, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    rfl
  change DerivedCategory.Q.map (((U ⋙ F).mapHomologicalComplex (.up ℤ)).map f) ≫
    pullbackTensorLimitUnit l E W D = pullbackTensorLimitUnit l E W C ≫
      F.rightDerivedFunctor.map (U.mapDerivedCategory.map (DerivedCategory.Q.map f))
  simpa only [Functor.comp_map, hθ] using θ.naturality f

attribute [local irreducible] coefficientSequenceRestriction scalarReductionExtension

attribute [local implicit_reducible] pullbackTensorReductionEvaluationComplex
attribute [local irreducible] coefficientScalarTensorIso coefficientEvaluationTensorIso

/-- A strict ordinary quotient-unit presentation is canonically isomorphic to ordinary
reduction, and its localization agrees with the fixed whole-system reduction model.

Source: Stacks 07A4, 07A6 and 0941. Transpose the retained ordinary-limit map through
ordinary reduction/limit adjunction. Its finite projections identify its evaluations
with the inverse evaluation comparisons followed by the representative identifications.
These evaluations are isomorphisms, so sectionwise detection gives a chain isomorphism.
Naturality of the derived-limit unit and injectivity of the derived adjunction then
identify its localization with the prescribed representative isomorphism.
(blueprint: lem-coef-tensor-reduction-canonical-presentation). -/
theorem tensorReductionCanonicalPresentation (W : Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : (pullbackTensorCalculus l E W).reduction.obj (DerivedCategory.Q.obj P.obj) ≅
      DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj)
    (hc : CoefficientStrictReductionUnitPresentation l E W
      (pullbackTensorCalculus l E W).toCoefficientDerivedSystemReduction.reduction
      (pullbackTensorCalculus l E W).toCoefficientDerivedSystemReduction.adjunction
      P.obj C e κ) :
    ∃ a : ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj ≅ C,
      (pullbackTensorReductionModel l E W).hom.app P ≫ DerivedCategory.Q.map a.hom = e.hom ∧
      ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a.hom ≫
          (κ n).hom = (pullbackTensorReductionEvaluationComplex l E W n).inv.app P.obj := by
  obtain ⟨z, hz, hπ⟩ := hc
  let adj := (pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)
  let a := (adj.homEquiv P.obj C).symm z
  have ha : adj.homEquiv P.obj C a = z := (adj.homEquiv P.obj C).apply_symm_apply z
  have hfinite (n : ℕ) :
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a ≫
        (κ n).hom = (pullbackTensorReductionEvaluationComplex l E W n).inv.app P.obj := by
    apply (cancel_epi
      ((pullbackTensorReductionEvaluationComplex l E W n).hom.app P.obj)).1
    erw [Iso.hom_inv_id_app]
    let finAdj := (pullbackTensorFiniteAdjunction l E W n).mapHomologicalComplex (.up ℤ)
    apply (finAdj.homEquiv _ _).injective
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rw [← transpose_complex_projection, ha]
    erw [Adjunction.homEquiv_id]
    simpa only [finAdj, pullbackTensorFiniteAdjunction, Category.assoc] using hπ n
  have hai : IsIso a := by
    apply isIso_of_evaluations l E W a
    intro n
    have : IsIso
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a ≫
          (κ n).hom) := by
      rw [hfinite n]
      exact ((pullbackTensorReductionEvaluationComplex l E W n).app P.obj).isIso_inv
    exact IsIso.of_isIso_comp_right _ (κ n).hom
  refine ⟨asIso a, ?_, hfinite⟩
  apply ((pullbackTensorCalculus l E W).adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  have hunit := (pullbackTensorReductionModel_existsUnique l E W).exists.choose_spec P
  simp only [pullbackTensorReductionModel, pullbackTensorUniqueChoice,
    integralOperationsGoodLocalization, CategoryTheory.Functor.comp_obj, ObjectProperty.ι_obj]
  rw [hunit, Category.assoc, ← limitUnit_natural]
  erw [← CategoryTheory.Functor.map_comp_assoc]
  change DerivedCategory.Q.map (adj.homEquiv P.obj C a) ≫
    pullbackTensorLimitUnit l E W C = _
  rw [ha]
  refine Eq.trans ?_ hz.symm
  simp only [pullbackTensorLimitUnit]
  have hq₁ (K : CochainComplex (integralTowerModules l E W) ℤ) :
      (DerivedCategory.quotientCompQhIso (integralTowerModules l E W)).inv.app K = 𝟙 _ := rfl
  have hq₂ (K : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
      (DerivedCategory.quotientCompQhIso (ℕᵒᵖ ⥤ integralTowerModules l E W)).hom.app K =
        𝟙 _ := rfl
  simp only [Functor.rightDerivedFunctorUnitQ]
  erw [hq₁, hq₂]
  erw [(pullbackTensorConstantLimit l E W).rightDerivedFunctor.map_id]
  erw [Category.comp_id]
  erw [Category.id_comp]
  rfl

end WeilConjectures
