/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarQuotientOrdinaryInterchange
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarQuotientRoosAugmentation

/-! # Coherent quotient presentations and scalar completion

Source: Stacks 06YY and 0941. This isolates the source-side presentation
transport in the scalar/pullback realization calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf completedIntegralCommRingSheafUnrestricted coefficientSequenceCommRingSheaf
  coefficientSequenceEvaluation coefficientSequenceRestriction

-- Naturality across the large coefficient-site instance expressions needs extra elaboration fuel.
private theorem restrictedSection_map (Y : Scheme.{u})
    {D C : coefficientSequenceModules l E Y} (f : D ⟶ C) (n : ℕ)
    (U : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E Y n).obj D).val.obj U) :
    (((coefficientSequenceRestriction l E Y).map f).app (op n)).val.app U
        (integralComparisonRestrictedSection l E Y D n U
          (integralComparisonSequenceSection l E Y D n U x)) =
      integralComparisonRestrictedSection l E Y C n U
        (integralComparisonSequenceSection l E Y C n U
          (((coefficientSequenceEvaluation l E Y n).map f).val.app U x)) := by
  let z := eqToIso (coefficientSequenceRestriction_evaluation l E Y n)
  let v := (SheafOfModules.evaluation _ U).mapIso (z.app C)
  apply (ConcreteCategory.bijective_of_isIso v.hom).1
  have hn := congrArg (fun g ↦ g.val.app U
      (integralComparisonRestrictedSection l E Y D n U
        (integralComparisonSequenceSection l E Y D n U x)))
    (z.hom.naturality f)
  change (((eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom.app C).val.app U)
    _ = (((eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom.app C).val.app U) _
  rw [restricted_section_cancel l E Y C n U]
  change _ = ((coefficientSequenceEvaluation l E Y n).map f).val.app U x
  exact hn.trans (congrArg
    (fun y ↦ ((coefficientSequenceEvaluation l E Y n).map f).val.app U y)
    (restricted_section_cancel l E Y D n U x))

-- Naturality across the large coefficient-site instance expressions needs extra elaboration fuel.
private theorem presentation_transport (Y : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (D C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj D)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)
    (hp : CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 D e κ)
    (hc : IsIntegralComparisonPresentationCoherent l E Y S P.obj D e κ)
    (a : D ≅ C) :
    let e' := e ≪≫ DerivedCategory.Q.mapIso a
    let κ' := fun n ↦
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).mapIso
        a.symm ≪≫ κ n
    CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e' κ' ∧
    IsIntegralComparisonPresentationCoherent l E Y S P.obj C e' κ' := by
  dsimp only
  constructor
  · constructor
    · intro n
      have hn := hp.1 n
      change _ ≫ _ ≫ _ = _ at hn ⊢
      dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
      rw [Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      erw [(coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.naturality_assoc
        a.hom]
      simp only [Functor.comp_map, ← Functor.map_comp_assoc]
      rw [← ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).map_comp,
        a.hom_inv_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
      exact hn
    · intro m n h
      have hn := hp.2 m n h
      change _ ≫ _ = _ ≫ _ at hn ⊢
      apply HomologicalComplex.hom_ext
      intro i
      have hi := congrArg (fun g ↦ g.f i) hn
      have ha := (coefficientSequenceTransition l E Y h).naturality (a.inv.f i)
      simp only [HomologicalComplex.comp_f, Iso.trans_hom, Functor.mapIso_hom,
        Iso.symm_hom, Functor.mapHomologicalComplex_map_f, Functor.map_comp]
      change (coefficientSequenceTransition l E Y h).app (C.X i) ≫
        (normalizedDVRModuleRes l E Y h).map
          ((coefficientSequenceEvaluation l E Y n).map (a.inv.f i)) ≫
        (normalizedDVRModuleRes l E Y h).map ((κ n).hom.f i) = _
      erw [← Category.assoc, ← ha, Category.assoc]
      exact congrArg (fun g ↦ (coefficientSequenceEvaluation l E Y m).map (a.inv.f i) ≫ g) hi
  · unfold IsIntegralComparisonPresentationCoherent at hc ⊢
    obtain ⟨b, hb, he⟩ := hc
    let R := (coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)
    refine ⟨b ≫ R.map a.hom, ?_, ?_⟩
    · intro n i U x
      change (((coefficientSequenceRestriction l E Y).map (a.hom.f i)).app (op n)).val.app U
        ((((b.f i).app (op n)).val.app U) x) = _
      rw [hb, restrictedSection_map l E Y (a.hom.f i) n U]
      rfl
    · let T := integralComparisonConstantTower l E Y
      let H := coefficientSequenceDerivedRestriction l E Y
      let v := (coefficientSequenceRestriction l E Y).mapDerivedCategoryFactors.inv
      have hn := (integralComparisonTowerCounit l E Y).naturality
        (H.map (DerivedCategory.Q.map a.hom))
      dsimp only [Functor.comp_map, Functor.id_map] at hn
      change T.map (_ ≫ (coefficientSequenceLimit l E Y).map
        (e.hom ≫ DerivedCategory.Q.map a.hom)) ≫ _ = _
      rw [(coefficientSequenceLimit l E Y).map_comp, ← Category.assoc,
        T.map_comp, Category.assoc]
      erw [hn]
      rw [← Category.assoc, he]
      rw [Category.assoc, Category.assoc]
      erw [← v.naturality a.hom]
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
      rfl

private theorem scalarPresentation_homEquiv
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) {X Y : A} {Z Z' Z'' : B}
    (f : X ⟶ Y) (g : Y ⟶ G.obj Z) (h : Z ⟶ Z') (k : Z' ⟶ Z'') :
    adj.homEquiv X Z'' (F.map f ≫ (F.map g ≫ adj.counit.app Z) ≫ h ≫ k) =
      f ≫ g ≫ G.map h ≫ G.map k := by
  simp only [Category.assoc]
  rw [← F.map_comp_assoc]
  simp only [← Category.assoc]
  change adj.homEquiv X Z'' (((adj.homEquiv X Z).symm (f ≫ g) ≫ h) ≫ k) = _
  rw [adj.homEquiv_naturality_right,
    adj.homEquiv_naturality_right, Equiv.apply_symm_apply]

-- Compose the large derived functor interfaces without unfolding their constructions.
/-- Scalar completion induces the coherent quotient presentation of ordinary scalar change.
Source: Stacks 06YY, 0941; scalar normalization and the tensor-unit augmentation
in step 1 of stage3-pur-scalar-pullback-left-roos.
(blueprint: lem-pur-scalar-completion-quotient-presentation).

Proof: choose ordinary quotient models for the good complexes P and its ordinary
scalar extension PS, with their normalized derived reduction presentations (the
coherent primitive presentation construction). Coherence of (C,eC,kappa) identifies
C with the first ordinary model. Associate, level by level, quotient scalar tensors
with the quotient of ordinary scalar extension. These associations commute with
differentials and every quotient transition, so they give an isomorphism from CS
to the ordinary quotient model of PS. Transport its normalized comparison and finite
identifications back along this isomorphism to obtain eS and kappaS. The balanced
associators send nested unit tensors to 1 tensor (1 tensor x), proving the section
formula. Their tensor-unit maps also agree before localization, so transporting the
ordinary adjunction transpose gives both reduction-presentation and whole-system
coherence equations. Finally apply the reduction/total-limit adjunction to the last
equality. Scalar normalization of SY identifies its realized side with the scalar
representative comparison. ScalarCompletionNormalization identifies the ordinary
scalar source augmentation with that same comparison composed with scalarCompletion.
The ordinary constant-tower/limit unit and counit identities then identify the two
transposes. Injectivity of the adjunction equivalence proves the last displayed
equality in the derived category of the entire sequence site; no faithfulness of
individual derived evaluations is used.
No pullback, derived completeness, invertibility of l on Y or flatness of a finite
quotient coefficient map is used. Empty sites, zero complexes, identity embeddings,
n=0 and ramified embeddings have the same balanced tensor association. -/
theorem scalarCompletionQuotientPresentation (Y : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L Y)
    (ρ : IntegralComparisonRoosModel.{u, u} l L Y)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι Y SE ρ)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (eC : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E Y
      SE.toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E Y SE P.obj C eC κ) :
    let PS := ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj
    let CS := ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
      (.up ℤ)).obj C
    ∃ (eS : SL.reduction.obj (DerivedCategory.Q.obj PS) ≅ DerivedCategory.Q.obj CS)
      (κS : ∀ n : ℕ,
        ((coefficientSequenceEvaluation.{u, u} l L Y n).mapHomologicalComplex (.up ℤ)).obj CS ≅
          (unrestrictedIntegralFiniteComplex.{u, u} l L Y n).obj PS),
      CoefficientReductionPresentation.{u, u} l L Y SL.toCoefficientDerivedSystemReduction
        PS (scalarGood l E L ι Y P).1 CS eS κS ∧
      IsIntegralComparisonPresentationCoherent.{u, u} l L Y SL PS CS eS κS ∧
      (∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (P.obj.X i).val.obj (op U)),
        ((κS n).hom.f i).val.app (op U)
          (coefficientEvaluationSection.{u, u} l L Y (CS.X i) n (op U)
            (integralComparisonSequenceTensorSection.{u, u} l E L ι Y (C.X i)
              (op (n, U)) 1
              (integralComparisonSequenceSection.{u, u} l E Y (C.X i) n (op U)
                (((κ n).inv.f i).val.app (op U)
                  (unrestrictedIntegralTensorSection.{u, u} l E Y n (P.obj.X i)
                    (op U) 1 x))))) =
          unrestrictedIntegralTensorSection.{u, u} l L Y n (PS.X i) (op U) 1
            (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) (op U) 1 x)) ∧
      SL.reduction.map
          ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
        eS.hom =
      SL.reduction.map ((scalarCompletion l E L ι Y).app (DerivedCategory.Q.obj P.obj)) ≫
        scalarReduction l E L ι Y SE SL ρ SY (DerivedCategory.Q.obj P.obj) ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι Y).map eC.hom ≫
        (integralComparisonSequenceScalarModel.{u, u} l E L ι Y).ε.app C := by
  classical
  dsimp only
  let GP : (integralOperationsGoodComplex l L Y).FullSubcategory :=
    ⟨_, scalarGood l E L ι Y P⟩
  obtain ⟨D, eD, κD, hpD, hcD⟩ := coherentPrimitiveReductionPresentation l L SL GP
  have hc' := hc
  have hcD' := hcD
  unfold IsIntegralComparisonPresentationCoherent at hc' hcD'
  obtain ⟨bC, hbC, _⟩ := hc'
  obtain ⟨bD, hbD, _⟩ := hcD'
  obtain ⟨a, ha⟩ := scalarQuotientOrdinaryInterchange l E L ι Y P.obj C κ bC hbC
    D κD bD hbD
  let eS := eD ≪≫ DerivedCategory.Q.mapIso a.symm
  let κS (n : ℕ) :=
    ((coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫ κD n
  obtain ⟨hpS, hcS⟩ := presentation_transport l L Y SL GP D _ eD κD hpD hcD a.symm
  refine ⟨eS, κS, hpS, hcS, ha, ?_⟩
  obtain ⟨q, hq, hSY⟩ := SY.normalization P C eC κ hp hc
  have haug := scalarQuotientRoosAugmentation l E L ι Y SL ρ P C κ eS κS hpS hcS ha q hq
  let T := coefficientSequenceLimit l L Y
  let A := integralComparisonDerivedSequenceScalar l E L ι Y
  let t := (integralComparisonSequenceScalarModel l E L ι Y).ε.app C
  let d := (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj
  let r := (integralComparisonRoosBridge l L Y ρ
    (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
      (.up ℤ)).obj C)).hom
  let z := DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)
  have hχ := (scalarCompletion_existsUnique l E L ι Y).exists.choose_spec.1 P
  apply (SL.adjunction.homEquiv _ _).injective
  apply (cancel_mono (r ≫ z)).1
  have hm : SL.adjunction.homEquiv _ _
      (SL.reduction.map ((scalarCompletion l E L ι Y).app (DerivedCategory.Q.obj P.obj)) ≫
        scalarReduction l E L ι Y SE SL ρ SY (DerivedCategory.Q.obj P.obj) ≫
        A.map eC.hom ≫ t) =
      (scalarCompletion l E L ι Y).app (DerivedCategory.Q.obj P.obj) ≫
        SY.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        T.map (A.map eC.hom) ≫ T.map t := by
    exact scalarPresentation_homEquiv SL.adjunction
      ((scalarCompletion l E L ι Y).app (DerivedCategory.Q.obj P.obj))
      (SY.realization.hom.app (DerivedCategory.Q.obj P.obj)) (A.map eC.hom) t
  erw [hm, SL.adjunction.homEquiv_naturality_left]
  change (d ≫ (SL.adjunction.unit.app _ ≫ T.map eS.hom)) ≫ (r ≫ z) = _
  simp only [Category.assoc]
  erw [haug]
  erw [hSY]
  exact hχ.symm

end WeilConjectures.ScalarExtensionTower
