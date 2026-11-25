/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.SmoothPurity.Supporting.CoherentReferenceQuotientComparison
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackSuccessor
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorIntegralConstruction

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
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
open MonoidalCategory AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients
  pullbackTensorRestrictedTower
  referenceOrdinaryModel integralCoefficientSheaf integralCoefficientCommRingSheaf
  HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  integralOperationsGoodLocalization

attribute [local irreducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf
attribute [local irreducible] pullbackTensorCalculus integralDerivedPullback
  integralCompletedTensor coefficientTotalTensor SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory

private theorem direct_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f = integralComparisonSequenceDirectImage l E f := by
  unfold pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
  rw [WeilConjectures.pullbackTensorSequenceRing_eq]
  rfl

/-- Transport of a normalized adjunction mate across equality of chosen right adjoints.
Source: Mathlib adjunction mates, applied to quotient pullback evaluation.
(blueprint: lem-pur-completed-quotient-mate-transport).
Proof: substitute the equality of right adjoints. The direct comparison is then
unchanged, and the transported left-adjoint equality is reflexive. Apply the
adjunction Hom bijection to each component and use unit_mateEquiv_symm. -/
theorem completedQuotientMateTransport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R R' : B ⥤ A) [R.IsRightAdjoint] [R'.IsRightAdjoint]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (U : A ⥤ C) (V : B ⥤ D) (h : R = R')
    (hL : R.leftAdjoint = R'.leftAdjoint)
    (d : R ⋙ U ≅ V ⋙ G) (d' : R' ⋙ U ≅ V ⋙ G)
    (hd : Functor.isoWhiskerRight (eqToIso h) U ≪≫ d' = d)
    (a : U ⋙ F ≅ R.leftAdjoint ⋙ V)
    (ha : ∀ M, adj.homEquiv _ _ (a.hom.app M) =
      U.map ((Adjunction.ofIsRightAdjoint R).unit.app M) ≫ d.hom.app (R.leftAdjoint.obj M)) :
    (a ≪≫ Functor.isoWhiskerRight (eqToIso hL) V).hom =
      ((mateEquiv (Adjunction.ofIsRightAdjoint R') adj).symm d'.hom) := by
  subst R'
  have hd' : d' = d := by simpa using hd
  subst d'
  have he : (eqToIso hL : R.leftAdjoint ≅ R.leftAdjoint) = Iso.refl _ := by simp
  rw [he]
  apply NatTrans.ext
  funext M
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ (a.hom.app M ≫ V.map (𝟙 _)) = _
  rw [V.map_id]
  erw [Category.comp_id]
  exact (ha M).trans (unit_mateEquiv_symm
    (Adjunction.ofIsRightAdjoint R) adj d.hom M)

private theorem whisker_eq_sections
    {C D A : Type*} [Category C] [Category D] [Category A]
    {J : GrothendieckTopology A} {O : Sheaf J RingCat.{u}}
    (F G : C ⥤ D) (h : F = G) (V : D ⥤ SheafOfModules.{u} O)
    (M : C) (U : Aᵒᵖ) (x : (V.obj (F.obj M)).val.obj U) :
    HEq (((V.map ((eqToIso h).hom.app M)).val.app U) x) x := by
  subst G
  simp

private theorem inverse_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorSequenceInverseEvaluation l E f n ≪≫
      Functor.isoWhiskerRight (eqToIso (sequencePullback_eq l E f))
        (coefficientSequenceEvaluation l E X n) =
      OrdinaryTowerProof.inverseEvaluation l E f n := by
  have hd : Functor.isoWhiskerRight (eqToIso (direct_eq l E f))
        (coefficientSequenceEvaluation l E Y n) ≪≫
      OrdinaryTowerProof.directEvaluation l E f n =
      pullbackTensorSequenceDirectEvaluation l E f n := by
    apply (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).unique
    · intro M U x
      have h := OrdinaryTowerProof.directEvaluation_sections l E f n M U
      dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, SheafOfModules.comp_val]
      rw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
      exact (h _).trans (whisker_eq_sections _ _ (direct_eq l E f)
        (coefficientSequenceEvaluation l E Y n) M (op U) x)
    · exact (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec
  apply Iso.ext
  rw [OrdinaryTowerProof.inverseEvaluation_hom]
  exact completedQuotientMateTransport
    (pullbackTensorSequenceDirect l E f) (integralComparisonSequenceDirectImage l E f)
    (integralOperationsLevelPullback l E f n)
    (coefficientProEtaleModuleDirectImage f
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))
    (coefficientProEtaleModuleAdjunction f
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))
    (coefficientSequenceEvaluation l E Y n) (coefficientSequenceEvaluation l E X n)
    (direct_eq l E f) (sequencePullback_eq l E f)
    (pullbackTensorSequenceDirectEvaluation l E f n)
    (OrdinaryTowerProof.directEvaluation l E f n) hd
    (pullbackTensorSequenceInverseEvaluation l E f n)
    (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose_spec

private theorem tower_level_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : coefficientSequenceModules l E Y) (n : ℕ) :
    (coefficientSequenceRestriction l E X ⋙
      (evaluation ℕᵒᵖ (integralTowerModules l E X)).obj (op n)).map
        ((eqToIso (sequencePullback_eq l E f)).inv.app K) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app
        ((pullbackTensorSequenceInverse l E f).obj K) ≫
      (scalarReductionRestriction l E X n).map
        ((pullbackTensorSequenceInverseEvaluation l E f n).inv.app K) =
    (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app
      ((integralComparisonSequencePullback l E f).obj K) ≫
      (scalarReductionRestriction l E X n).map
        ((OrdinaryTowerProof.inverseEvaluation l E f n).inv.app K) := by
  have hi := congrArg (fun e ↦ e.inv.app K) (inverse_evaluation l E f n)
  change (coefficientSequenceEvaluation l E X n).map
      ((eqToIso (sequencePullback_eq l E f)).inv.app K) ≫
        (pullbackTensorSequenceInverseEvaluation l E f n).inv.app K =
    (OrdinaryTowerProof.inverseEvaluation l E f n).inv.app K at hi
  with_unfolding_all
    rw [← Category.assoc,
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.naturality,
      Category.assoc, Functor.comp_map, ← Functor.map_comp, hi]

private theorem restrictedLevel_hom_f (W : Scheme.{u})
    (C : StrictQuotient.Complex l E W) (n : ℕ) (i : ℤ) :
    (pullbackTensorRestrictedLevel l E W C n).hom.f i =
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (C.X i) := by
  simp only [pullbackTensorRestrictedLevel, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

private theorem ordinary_level_hom_f {X Y : Scheme.{u}} (f : X ⟶ Y)
    (O : CompletionUnit.OrdinaryModel l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) (i : ℤ) :
    (OrdinaryTowerProof.level l E f O P n).hom.f i =
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app
          ((integralComparisonSequencePullback l E f).obj (O.tensor.obj (P.X i))) ≫
        (scalarReductionRestriction l E X n).map
          ((OrdinaryTowerProof.inverseEvaluation l E f n).inv.app (O.tensor.obj (P.X i)) ≫
            (integralOperationsLevelPullback l E f n).map ((O.evaluation n).hom.app (P.X i))) := by
  change (OrdinaryTowerProof.moduleLevel l E f O n).hom.app (P.X i) = _
  dsimp only [OrdinaryTowerProof.moduleLevel, Iso.trans, Iso.symm, Iso.app,
    Functor.isoWhiskerLeft, Functor.isoWhiskerRight, Functor.whiskerLeft,
    Functor.whiskerRight, Functor.associator, whiskeringLeft, whiskeringRight, Functor.mapIso]
  simp only [NatTrans.comp_app, Category.id_comp, Functor.map_comp]
  rfl

-- Componentwise tower comparison includes the fixed sheaf and complex functor interfaces.
private theorem tower_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    let R := (pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)
    let U := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    U.mapIso ((pullBridge l E f).app (R.obj P)).symm ≪≫
      pullbackTensorPullbackTower l E f P =
        (OrdinaryTowerProof.comparison l E f (referenceOrdinaryModel l E Y)).app P := by
  dsimp only
  apply Iso.ext
  apply NatTrans.ext
  funext n
  have hn := (pullbackTensorPullbackTower_existsUnique l E f P).exists.choose_spec n.unop
  change (pullbackTensorPullbackTower l E f P).app (op n.unop) = _ at hn
  apply HomologicalComplex.hom_ext
  intro i
  have hh := congrArg (fun e ↦ e.hom.f i) hn
  dsimp only [Iso.app_hom] at hh
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom]
  simp only [HomologicalComplex.comp_f]
  erw [hh]
  simp only [Iso.app_hom]
  rw [OrdinaryTowerProof.comparison_hom_app_f, ordinary_level_hom_f]
  dsimp only [referenceOrdinaryModel]
  simp only [pullbackTensorPullbackTowerLevel, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, HomologicalComplex.comp_f,
    restrictedLevel_hom_f, Functor.mapHomologicalComplex_map_f,
    Functor.comp_map, HomologicalComplex.complexOfFunctorsToFunctorToComplex_map_app_f,
    pullBridge, NatIso.mapHomologicalComplex_inv_app_f]
  with_unfolding_all
    change (coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (integralTowerModules l E X)).obj (op n.unop)).map
          ((eqToIso (sequencePullback_eq l E f)).inv.app
            ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i))) ≫
        ((eqToIso (coefficientSequenceRestriction_evaluation l E X n.unop)).hom.app _ ≫
          (scalarReductionRestriction l E X n.unop).map
            ((pullbackTensorSequenceInverseEvaluation l E f n.unop).inv.app _)) ≫
        (scalarReductionRestriction l E X n.unop).map
          ((integralOperationsLevelPullback l E f n.unop).map
            ((pullbackTensorReductionEvaluation l E Y n.unop).inv.app (P.X i))) =
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n.unop)).hom.app _ ≫
        (scalarReductionRestriction l E X n.unop).map
          ((OrdinaryTowerProof.inverseEvaluation l E f n.unop).inv.app _ ≫
            (integralOperationsLevelPullback l E f n.unop).map
              ((pullbackTensorReductionEvaluation l E Y n.unop).inv.app (P.X i)))
  rw [← Category.assoc, tower_level_transport]
  with_unfolding_all
    rw [Functor.map_comp, Category.assoc]

end WeilConjectures.CompletedQuotient
