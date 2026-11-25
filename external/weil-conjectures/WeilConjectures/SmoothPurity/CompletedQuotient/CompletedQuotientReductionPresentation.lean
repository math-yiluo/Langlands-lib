/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.SmoothPurity.Pur.PurSequenceOrdinaryFactorization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # The prescribed ordinary quotient reduction presentation

Source: Stacks 0941 and 06YY; the normalized coherent reduction model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substituteInputs substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  SheafOfModules.monoidalCategory completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible]
  coefficientFiniteDerivedExtension coefficientFiniteDerivedRestriction
  coefficientConstantTowerLimit coefficientConstantTowerEvaluation
  coefficientSequenceLimit
  scalarReductionDerivedRestriction unrestrictedIntegralReductionFunctor
  pullbackTensorOrdinaryLimit pullbackTensorConstantLimit
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralOperationsGoodLocalization
attribute [local implicit_reducible] DerivedCategory.Q DerivedCategory.Qh

private theorem reductionEvaluation_eq (Y : Scheme.{u})
    (O : PurSequenceOrdinaryAdjoints l E Y) (n : ℕ) :
    pullbackTensorReductionEvaluation l E Y n =
      (O.tensor n).symm ≪≫ Functor.isoWhiskerRight
        ((O.adjunction.ofNatIsoRight O.limit).leftAdjointUniq
          (pullbackTensorOrdinaryAdjunction l E Y))
        (coefficientSequenceEvaluation l E Y n) := by
  let adj := O.adjunction.ofNatIsoRight O.limit
  let a := adj.leftAdjointUniq (pullbackTensorOrdinaryAdjunction l E Y)
  let e := (O.tensor n).symm ≪≫
    Functor.isoWhiskerRight a (coefficientSequenceEvaluation l E Y n)
  apply ((pullbackTensorReductionEvaluation_existsUnique l E Y n).unique
    (show _ from ?_)
    (pullbackTensorReductionEvaluation_existsUnique l E Y n).exists.choose_spec).symm
  intro M
  have h := O.transpose M ((pullbackTensorOrdinaryReduction l E Y).obj M)
    (O.adjunction.homEquiv _ _ (a.hom.app M)) n
  rw [Equiv.symm_apply_apply] at h
  have ha := Adjunction.homEquiv_leftAdjointUniq_hom_app
    adj (pullbackTensorOrdinaryAdjunction l E Y) M
  change adj.homEquiv _ _ (a.hom.app M) = _ at ha
  dsimp only [adj] at ha
  erw [Adjunction.homEquiv_ofNatIsoRight_apply] at ha
  rw [O.projection_limit] at h
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  exact h.trans (by simpa only [Category.assoc] using
    (congrArg (fun k ↦ k ≫
      limit.π ((coefficientSequenceRestriction l E Y).obj
        ((pullbackTensorOrdinaryReduction l E Y).obj M)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom.app
        ((pullbackTensorOrdinaryReduction l E Y).obj M)) ha))

private theorem reductionEvaluation_transition (Y : Scheme.{u})
    (M : scalarReductionSource l E Y) (m n : ℕ) (h : n ≤ m) :
    (coefficientSequenceTransition l E Y h).app
        ((pullbackTensorOrdinaryReduction l E Y).obj M) ≫
      (normalizedDVRModuleRes l E Y h).map
        ((pullbackTensorReductionEvaluation l E Y n).inv.app M) =
      (pullbackTensorReductionEvaluation l E Y m).inv.app M ≫
        (coefficientOrdinaryQuotient l E Y h).app M := by
  obtain ⟨O, _⟩ := purSequenceOrdinaryFactorization l E Y
  rw [reductionEvaluation_eq l E Y O n, reductionEvaluation_eq l E Y O m]
  let a := (O.adjunction.ofNatIsoRight O.limit).leftAdjointUniq
    (pullbackTensorOrdinaryAdjunction l E Y)
  change _ ≫ (normalizedDVRModuleRes l E Y h).map
    ((coefficientSequenceEvaluation l E Y n).map (a.inv.app M) ≫
      (O.tensor n).hom.app M) =
    ((coefficientSequenceEvaluation l E Y m).map (a.inv.app M) ≫
      (O.tensor m).hom.app M) ≫ _
  have ht := (coefficientSequenceTransition l E Y h).naturality (a.inv.app M)
  dsimp only [Functor.comp_map] at ht
  rw [Functor.map_comp, ← Category.assoc]
  erw [← ht]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg ((coefficientSequenceEvaluation l E Y m).map (a.inv.app M) ≫ ·)
      (O.tensor_transition M m n h)

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

/-- Localization factors for the canonical square of exact functors. -/
private theorem square_factors
    {A B B' D : Type*} [Category* A] [Category* B] [Category* B'] [Category* D]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory D]
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (G₁ : A ⥤ B') (G₂ : B' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (I : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app I) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj I) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app I) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj I) =
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) := by
  apply (cancel_epi (F₂.mapDerivedCategoryFactors.inv.app
    ((F₁.mapHomologicalComplex (.up ℤ)).obj I))).mp
  rw [Iso.inv_hom_id_app_assoc]
  have hF := Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ I
  have hG := Functor.mapDerivedCategoryCompIso_hom_app_factors G₁ G₂ I
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [hG, Functor.mapDerivedCategoryNatIso_fac]
  rw [← hF]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [F₂.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]

/-- Localization of a termwise adjunction unit agrees in the two quotient coordinates. -/
private theorem localized_unit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F : A ⥤ B} {R : B ⥤ A} [F.Additive] [R.Additive] (a : F ⊣ R)
    (Q : CochainComplex A ℤ) :
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q) := by
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  rfl

/-- The finite scalar unit on a K-flat complex in the cochain localization coordinates. -/
private theorem finiteModel_unit (W : Scheme.{u})
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (n : ℕ) :
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          (coefficientFiniteReductionModel l E W Q hQ n).hom ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app Q) := by
  have h := (derivedScalarExtensionRestrictionAdjunction l E W n).choose_spec Q hQ
  have hfac := (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh_hom_app
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
  have hfac' : (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) := by
    erw [hfac]
    change (scalarReductionDerivedRestriction l E W n).map (𝟙 _) ≫ _ ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [(scalarReductionRestriction l E W n).mapDerivedCategory.map_id,
      DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]
    erw [Category.comp_id]
  have hunit : DerivedCategory.Qh.map
      ((((scalarReductionExtension_adjunction l E W n).choose).mapHomotopyCategory
        (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app Q) :=
    localized_unit (scalarReductionExtension_adjunction l E W n).choose Q
  have hmodel : (coefficientFiniteReductionModel l E W Q hQ n).hom =
      (scalarReductionCounit l E W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) := by
    dsimp only [coefficientFiniteReductionModel, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app, asIso_hom]
    change (coefficientFiniteDerivedExtension l E W n).map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    erw [Category.comp_id]
    erw [(coefficientFiniteDerivedExtension l E W n).map_id, Category.id_comp]
    rfl
  refine (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (coefficientFiniteDerivedRestriction l E W n).map f ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))
          hmodel).trans ?_
  exact (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (scalarReductionDerivedRestriction l E W n).map
        ((scalarReductionCounit l E W n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) ≫ f) hfac'.symm).trans
      (h.trans hunit)

private theorem towerUnit_projection (Y : Scheme.{u})
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ) (n : ℕ) :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
      scalarReductionSource l E Y).rightDerivedFunctorUnitQ C ≫
      (coefficientConstantTowerProjection l E Y n).app (DerivedCategory.Q.obj C) ≫
      (coefficientConstantTowerEvaluationFactors l E Y n).hom.app C =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
      C) := by
  let F : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ scalarReductionSource l E Y := lim
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n)
  let α : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    { app := fun K ↦ F.rightDerivedFunctorUnitQ K ≫
        (coefficientConstantTowerProjection l E Y n).app (DerivedCategory.Q.obj K) ≫
        V.mapDerivedCategoryFactors.hom.app K
      naturality := by
        intro K L f
        rw [Functor.comp_map, Functor.comp_map,
          F.rightDerivedFunctorUnitQ_naturality_assoc]
        erw [(coefficientConstantTowerProjection l E Y n).naturality_assoc
          (DerivedCategory.Q.map f)]
        erw [V.mapDerivedCategoryFactors_hom_naturality]
        simp only [Category.assoc] }
  let β := Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (lim.π (op n) : F ⟶ V) (.up ℤ)) DerivedCategory.Q
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ)
      [I.IsKInjective] : α.app I = β.app I := by
    change F.rightDerivedFunctorUnitQ I ≫ _ ≫ _ = _
    erw [(coefficientConstantTowerProjection_exists l E Y n).choose_spec.1 I]
    rw [← Category.assoc, F.rightDerivedFunctorUnitQ_eq,
      Iso.inv_hom_id, Category.id_comp]
    rfl
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  let : I.IsKInjective := hI
  let : QuasiIso q := hq
  have : QuasiIso ((V.mapHomologicalComplex (.up ℤ)).map q) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology q V
  apply (cancel_mono (DerivedCategory.Q.map ((V.mapHomologicalComplex (.up ℤ)).map q))).1
  change α.app C ≫ (V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map q =
    β.app C ≫ (V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map q
  rw [← α.naturality, ← β.naturality, hi I]

private theorem limitUnit_projection (Y : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ) :
    pullbackTensorLimitUnit l E Y C ≫
      (coefficientSequenceProjection l E Y n).app (DerivedCategory.Q.obj C) ≫
      (coefficientFiniteDerivedRestriction l E Y n).map
        ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C) ≫
      (scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.hom.app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) =
    DerivedCategory.Q.map
      (((Functor.mapHomologicalComplexCompIso
        (Iso.refl (coefficientSequenceRestriction l E Y ⋙
          pullbackTensorConstantLimit l E Y)) (.up ℤ)).inv.app C) ≫
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          (((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)).obj C)) ≫
        (NatTrans.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom (.up ℤ)).app C) := by
  let U := coefficientSequenceRestriction l E Y
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n)
  let F := coefficientSequenceEvaluation l E Y n
  let R := scalarReductionRestriction l E Y n
  let e := eqToIso (coefficientSequenceRestriction_evaluation l E Y n)
  have hsq := square_factors U V F R e C
  have hπ := towerUnit_projection l E Y ((U.mapHomologicalComplex (.up ℤ)).obj C) n
  change (pullbackTensorConstantLimit l E Y).rightDerivedFunctorUnitQ
    ((U.mapHomologicalComplex (.up ℤ)).obj C) ≫ _ = _ at hπ
  unfold pullbackTensorLimitUnit coefficientSequenceProjection
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  erw [(coefficientConstantTowerProjection l E Y n).naturality_assoc
    (U.mapDerivedCategoryFactors.inv.app C)]
  have hsq' : (coefficientConstantTowerEvaluation l E Y n).map
      (U.mapDerivedCategoryFactors.inv.app C) ≫
      (coefficientRestrictedEvaluationIso l E Y n).hom.app (DerivedCategory.Q.obj C) ≫
      R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app C) ≫
      R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj C) =
    V.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app C) := hsq
  erw [hsq', reassoc_of% hπ]
  simp only [← DerivedCategory.Q.map_comp]
  rfl

private theorem ordinaryComplex_unit (Y : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    ((pullbackTensorOrdinaryAdjunction l E Y).mapHomologicalComplex (.up ℤ)).unit.app P ≫
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (coefficientSequenceRestriction l E Y ⋙
          pullbackTensorConstantLimit l E Y)) (.up ℤ)).inv.app (quotient l E P)) ≫
      ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
        (((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)).obj
          (quotient l E P))) ≫
      (NatTrans.mapHomologicalComplex
        (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom (.up ℤ)).app
          (quotient l E P) ≫
      ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).map
        ((pullbackTensorReductionEvaluationComplex l E Y n).inv.app P) =
    ((pullbackTensorFiniteAdjunction l E Y n).mapHomologicalComplex (.up ℤ)).unit.app P := by
  apply HomologicalComplex.hom_ext
  intro i
  have he := (pullbackTensorReductionEvaluation_existsUnique l E Y n).exists.choose_spec
    (P.X i)
  change (pullbackTensorFiniteAdjunction l E Y n).homEquiv _ _
    ((pullbackTensorReductionEvaluation l E Y n).hom.app (P.X i)) = _ at he
  rw [Adjunction.homEquiv_unit] at he
  change (pullbackTensorOrdinaryAdjunction l E Y).unit.app (P.X i) ≫ 𝟙 _ ≫
    limit.π ((coefficientSequenceRestriction l E Y).obj
      ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i))) (op n) ≫
    (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom.app
      ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i)) ≫
    (scalarReductionRestriction l E Y n).map
      ((pullbackTensorReductionEvaluation l E Y n).inv.app (P.X i) ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]
  erw [← reassoc_of% he]
  rw [← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The actual ordinary quotient complex, with its fixed reduction-model and
ordinary evaluation isomorphisms, is a coherent reduction presentation.
Source: Stacks 0941 and 06YY; the adjunction normalizations of
pullbackTensorReductionModel_existsUnique and pullbackTensorReductionEvaluation_existsUnique
(blueprint: lem-pur-completed-quotient-reduction-presentation).

Proof: transpose the fixed reduction-model component under the reduction/limit
adjunction. Its defining equation is the localization of the ordinary quotient
unit followed by the canonical total-limit comparison. Project to level n and
transpose under the finite scalar-extension/restriction adjunction. The ordinary
evaluation comparison is normalized by exactly this projected ordinary unit.
The finite K-flat reduction comparison is likewise normalized by this unit;
uniqueness of adjoints gives the CoefficientComparisonEquation. For m >= n,
transpose the two composites of the ordinary evaluation isomorphisms with the
quotient transition under the ordinary extension/restriction adjunction. Both
are the same ordinary quotient unit followed by the quotient map. Injectivity
of the Hom equivalence gives the CoefficientTransitionEquation; applying the
cochain-complex functors preserves the equality. No replacement complex or
new representative is chosen. The argument applies to zero complexes, n=0
(the exponent-one quotient), and m=n, where the quotient map is the identity. -/
theorem completedQuotientReductionPresentation
    (Y : Scheme.{u})
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    CoefficientReductionPresentation l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction
      P.obj P.property.1 (quotient l E P.obj)
      ((pullbackTensorReductionModel l E Y).app P)
      (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app P.obj).symm) := by
  constructor
  · intro n
    change (coefficientSequenceDerivedEvaluation l E Y n).map
        ((pullbackTensorReductionModel l E Y).hom.app P) ≫
      (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app
        (quotient l E P.obj) ≫
      DerivedCategory.Q.map ((pullbackTensorReductionEvaluationComplex l E Y n).inv.app
        P.obj) =
      ((pullbackTensorCalculus l E Y).reductionEvaluation n).hom.app
        (DerivedCategory.Q.obj P.obj) ≫
      (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom
    let S := pullbackTensorCalculus l E Y
    let K := DerivedCategory.Q.obj P.obj
    let C := quotient l E P.obj
    let R := scalarReductionRestriction l E Y n
    let e := (pullbackTensorReductionEvaluationComplex l E Y n).inv.app P.obj
    have hunit := (pullbackTensorReductionModel_existsUnique l E Y).exists.choose_spec P
    change S.adjunction.homEquiv K (DerivedCategory.Q.obj C)
      ((pullbackTensorReductionModel l E Y).hom.app P) = _ at hunit
    apply (cancel_epi ((S.reductionEvaluation n).inv.app K)).mp
    erw [Iso.inv_hom_id_app_assoc]
    apply ((coefficientFiniteAdjunction l E Y n).homEquiv K _).injective
    apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
      (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj))).mp
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% (S.unit_projection K n)]
    erw [← (coefficientSequenceProjection l E Y n).naturality_assoc
      ((pullbackTensorReductionModel l E Y).hom.app P)]
    rw [← reassoc_of% (S.adjunction.homEquiv_unit K (DerivedCategory.Q.obj C)
      ((pullbackTensorReductionModel l E Y).hom.app P)), hunit]
    erw [R.mapDerivedCategoryFactors.hom.naturality e]
    have hp := limitUnit_projection l E Y C n
    have hu := ordinaryComplex_unit l E Y P.obj n
    simp only [Category.assoc] at hp ⊢
    erw [reassoc_of% hp]
    simp only [Functor.comp_map, ← Functor.map_comp, Category.assoc]
    erw [hu]
    exact (finiteModel_unit l E Y P.obj P.property.1 n).symm
  · intro m n h
    apply HomologicalComplex.hom_ext
    intro i
    change (coefficientSequenceTransition l E Y h).app
        ((pullbackTensorOrdinaryReduction l E Y).obj (P.obj.X i)) ≫
      (normalizedDVRModuleRes l E Y h).map
        ((pullbackTensorReductionEvaluation l E Y n).inv.app (P.obj.X i) ≫ 𝟙 _) =
      ((pullbackTensorReductionEvaluation l E Y m).inv.app (P.obj.X i) ≫ 𝟙 _) ≫ _
    simp only [Category.comp_id]
    exact reductionEvaluation_transition l E Y (P.obj.X i) m n h

end WeilConjectures.CompletedQuotient
