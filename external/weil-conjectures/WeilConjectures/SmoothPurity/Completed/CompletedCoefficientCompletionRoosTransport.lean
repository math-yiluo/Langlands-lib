/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.SmoothBaseChange.ActualCompletedReductionReconstruction
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulReductionRoosTriangle
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The normalized completion Roos triangle under coefficient transport

Source: Stacks Tags 099M, 099N and 06YY; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-pur-completed-coefficient-completion-roos-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open Opposite
open IntegralCoefficientPresentation
attribute [local instance 30000] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
attribute [local irreducible] completedReductionEvaluation
  pbcActualCompletion pbcActualCompletionUnit
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionDerivedExtension
  scalarReductionExtension scalarReductionCounit normalizedDVRResCompletedComp
  completedIntegralCoefficientSheafUnrestricted normalizedDVRKFlatComparison
  CategoryTheory.Limits.limit

private theorem normalizedCoordinate
    {C : Type*} [Category C] {X Y L S P V U B H : C}
    (α : X ⟶ Y) (u : X ⟶ L) (e : L ⟶ S) (v : S ⟶ P) (π : P ⟶ V)
    (q : Y ⟶ S) (z : Y ⟶ H) (t : V ≅ H)
    (ηX : X ⟶ B) (ηY : Y ⟶ U) (r : B ⟶ U) (b : B ⟶ V) (c : U ⟶ H)
    (he : u ≫ e = α ≫ q) (hv : q ≫ v ≫ π = z ≫ t.inv)
    (hb : b ≫ t.hom = r ≫ c) (hn : α ≫ ηY = ηX ≫ r)
    (hη : ηY ≫ c = z) :
    u ≫ (e ≫ v) ≫ π = ηX ≫ b := by
  apply (cancel_mono t.hom).1
  simp only [Category.assoc]
  rw [← Category.assoc u, he]
  simp only [Category.assoc]
  rw [reassoc_of% hv, Iso.inv_hom_id, Category.comp_id, hb, ← reassoc_of% hn, hη]

private theorem pbcNormalizedRoos
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) :
    ∃ hp : HasProduct (fun n ↦
        (IntegralCoefficientPresentation.reduction (pbcAdicProjection T d n)).obj K),
      letI := hp
      ∃ (p : (pbcActualCompletion d T).obj K ⟶ ∏ᶜ fun n ↦
          (IntegralCoefficientPresentation.reduction (pbcAdicProjection T d n)).obj K)
        (δ : (∏ᶜ fun n ↦
          (IntegralCoefficientPresentation.reduction (pbcAdicProjection T d n)).obj K) ⟶
            ((pbcActualCompletion d T).obj K)⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (fun n ↦ (reconstructionStep T d n).app K)
          ((pbcActualCompletion d T).obj K) p δ ∧
        ∀ n, (pbcActualCompletionUnit d T).app K ≫ p ≫ Pi.π _ n =
          (pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.app K := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} T
  let := derived_products T (pbcAdicCompletion T d)
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let G : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ :=
    DerivedCategory.Q.objPreimage K
  obtain ⟨C, q, hC, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (J := ProEt.topology T) (R := pbcAdicCompletion T d) G
  let : QuasiIso q := hq
  let real : DerivedCategory.Q.obj C ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let J := (completedReductionComplexTowerFunctor T d).obj C
  let V := fun n ↦ (IntegralCoefficientPresentation.reduction
    (pbcAdicProjection T d n)).obj K
  let W := completedTowerDerivedSequence T d (DerivedCategory.Q.obj J)
  let ε := completedReductionTowerComplexCounit T d C
  have : IsIso ε := towerCounit_isIso T d C hC
  let E (n : ℕ) := reductionTowerDerivedEvaluation T
    (reductionModuleRing T (pbcAdicCompletion T d)) n
  let F (n : ℕ) := reductionTowerEvaluation T
    (reductionModuleRing T (pbcAdicCompletion T d)) n
  let b (n : ℕ) : V n ≅ W n :=
    (IntegralCoefficientPresentation.reduction (pbcAdicProjection T d n)).mapIso real.symm ≪≫
      ((asIso (completedReductionEvaluation T d n)).app (DerivedCategory.Q.obj C)).symm ≪≫
      (E n).mapIso (asIso ε)
  have hb (n : ℕ) :
      (b n).hom ≫ (F n).mapDerivedCategoryFactors.hom.app J =
        (IntegralCoefficientPresentation.reduction (pbcAdicProjection T d n)).map real.inv ≫
          (pbcDerivedRestrict (pbcAdicProjection T d n)).map
            (pbcComplexCounit (pbcAdicProjection T d n) C) ≫
          (pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryFactors.hom.app
            (((pbcExtend (pbcAdicProjection T d n)).mapHomologicalComplex (.up ℤ)).obj C) := by
    as_aux_lemma =>
      let τ := (asIso (completedReductionEvaluation T d n)).app (DerivedCategory.Q.obj C)
      have he : τ.hom ≫
          (pbcDerivedRestrict (pbcAdicProjection T d n)).map
            (pbcComplexCounit (pbcAdicProjection T d n) C) ≫
          (pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryFactors.hom.app
            (((pbcExtend (pbcAdicProjection T d n)).mapHomologicalComplex (.up ℤ)).obj C) =
          (E n).map ε ≫ (F n).mapDerivedCategoryFactors.hom.app J := by
        simpa only [τ, Iso.app_hom, asIso_hom, completedReductionEvaluation,
          pbcAdicProjection, completedReductionProjection, pbcComplexCounit,
          reductionScalarComplexCounit, pbcExtensionCounit,
          pbcDerivedRestrict, reductionDerivedRestrict, pbcRestrict,
          proEtaleRingRestrictScalars, reductionRestrict,
          reductionChangeComplex, reductionComplexCounit, pbcExtend, pbcDerivedExtend,
          reductionCoefficientSystem, pbcAdicRings, completedReductionCoefficient,
          pbcAdicCompletion, AdicCoefficients.completedRing, E, F, ε, J] using
            (completedReductionEvaluation_exists T d n).choose_spec.1.2 C hC
      have he' := (Iso.inv_comp_eq τ).2 he.symm
      dsimp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
      simp only [Category.assoc]
      exact congrArg (fun f ↦
        (IntegralCoefficientPresentation.reduction (pbcAdicProjection T d n)).map real.inv ≫ f)
        he'
  have hstep (n : ℕ) :
      (reconstructionStep T d n).app K ≫ (b n).hom =
        (b (n + 1)).hom ≫ completedTowerDerivedStep T d (DerivedCategory.Q.obj J) n := by
    as_aux_lemma =>
      have hc := NatTrans.congr_app (reconstructionStep_comparison T d n)
        (DerivedCategory.Q.obj C)
      dsimp only [NatTrans.comp_app] at hc
      have hc' : (reconstructionStep T d n).app (DerivedCategory.Q.obj C) ≫
          (asIso (completedReductionEvaluation T d n)).inv.app (DerivedCategory.Q.obj C) =
        (asIso (completedReductionEvaluation T d (n + 1))).inv.app (DerivedCategory.Q.obj C) ≫
          completedTowerDerivedStep T d
            ((completedReductionTower T d).obj (DerivedCategory.Q.obj C)) n := by
        apply (cancel_epi ((completedReductionEvaluation T d (n + 1)).app
          (DerivedCategory.Q.obj C))).1
        rw [← Category.assoc, ← hc]
        simp only [Category.assoc]
        have hi (i : ℕ) := (asIso (completedReductionEvaluation T d i)).hom_inv_id_app
          (DerivedCategory.Q.obj C)
        dsimp only [asIso_hom] at hi
        rw [hi, Category.comp_id, reassoc_of% (hi (n + 1))]
        rfl
      dsimp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
      simp only [Category.assoc]
      erw [← reassoc_of% ((reconstructionStep T d n).naturality real.inv)]
      erw [reassoc_of% hc']
      have hn := (Localization.liftNatTrans DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ (E (n + 1)) (E n)
        (Functor.whiskerRight (NatTrans.mapHomologicalComplex
          (completedTowerEvaluationStep T (reductionModuleRing T (pbcAdicCompletion T d)) n)
            (.up ℤ)) DerivedCategory.Q)).naturality ε
      exact congrArg (fun f ↦
        (IntegralCoefficientPresentation.reduction
          (pbcAdicProjection T d (n + 1))).map real.inv ≫
        (asIso (completedReductionEvaluation T d (n + 1))).inv.app (DerivedCategory.Q.obj C) ≫ f)
        hn.symm
  obtain ⟨v, hv⟩ := actualFiberToStrict T d r a ha C hC
  obtain ⟨k, hk⟩ := completedKoszulQuotientComparison T d r a ha K C real
  obtain ⟨j, hj⟩ := actualCompletion_quotient d T
  let e : (pbcActualCompletion d T).obj K ≅
      DerivedCategory.Q.obj (intrinsicCompletionComplex T d r a C) :=
    j.app K ≪≫ k.symm
  have he : (pbcActualCompletionUnit d T).app K ≫ e.hom =
      real.inv ≫ DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a C) := by
    as_aux_lemma =>
      apply (cancel_mono k.hom).1
      dsimp only [e, Iso.trans_hom, Iso.symm_hom]
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact (hj K).trans hk.symm
  let : HasProductsOfShape ℕ
      (reductionDerivedCategory T (completedReductionCoefficient T d)) := by
    change HasProductsOfShape ℕ (DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    infer_instance
  obtain ⟨δ, hδ⟩ := completedRlim_roos T d (DerivedCategory.Q.obj J)
  refine ⟨inferInstance, ?_⟩
  apply reflectNormalizedRoos (𝟭 _) b
    (fun n ↦ (reconstructionStep T d n).app K)
    (completedTowerDerivedStep T d (DerivedCategory.Q.obj J)) hstep
    (e ≪≫ v) (completedRlimRoosProjection T d (DerivedCategory.Q.obj J)) δ hδ
    ((pbcActualCompletionUnit d T).app K)
    (fun n ↦ (pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.app K)
  intro n
  have hn := (pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.naturality real.inv
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hunit := (pbcDerivedScalarAdjunction_exists
    (pbcAdicProjection T d n)).exists.choose_spec C hC
  have hunit' : (pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.app
      (DerivedCategory.Q.obj C) ≫
      (pbcDerivedRestrict (pbcAdicProjection T d n)).map
        (pbcComplexCounit (pbcAdicProjection T d n) C) ≫
      (pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryFactors.hom.app
        (((pbcExtend (pbcAdicProjection T d n)).mapHomologicalComplex (.up ℤ)).obj C) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (pbcScalarAdjunction (pbcAdicProjection T d n)).unit (.up ℤ)).app C) := by
    simpa only [pbcDerivedScalarAdjunction] using hunit
  have hcoord := normalizedCoordinate real.inv
    ((pbcActualCompletionUnit d T).app K) e.hom v.hom
    ((completedRlimProjection T (pbcAdicCompletion T d) n).app
      (DerivedCategory.Q.obj J))
    (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a C))
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (pbcScalarAdjunction (pbcAdicProjection T d n)).unit (.up ℤ)).app C))
    ((F n).mapDerivedCategoryFactors.app J)
    ((pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.app K)
    ((pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.app
      (DerivedCategory.Q.obj C))
    ((IntegralCoefficientPresentation.reduction (pbcAdicProjection T d n)).map real.inv)
    (b n).hom
    ((pbcDerivedRestrict (pbcAdicProjection T d n)).map
        (pbcComplexCounit (pbcAdicProjection T d n) C) ≫
      (pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryFactors.hom.app
        (((pbcExtend (pbcAdicProjection T d n)).mapHomologicalComplex (.up ℤ)).obj C))
    he (hv n) (hb n) hn hunit'
  dsimp only [Functor.id_map, Iso.trans_hom, completedRlimRoosProjection]
  erw [Pi.lift_comp_π]
  exact hcoord

private def testDatum (p : ℕ) (hp : p.Prime) : FiniteFieldDatum.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

private theorem existsTestDatum (l : ℕ) : ∃ D : FiniteFieldDatum.{0}, l ≠ D.p := by
  by_cases h : l = 2
  · exact ⟨testDatum 3 (by decide), by simp [testDatum, h]⟩
  · exact ⟨testDatum 2 (by decide), h⟩

/-- The restricted adjoint of the smaller reduction unit. -/
private def adjointTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (T : B ⥤ A) (d : T ⋙ Rm ≅ Rn) :
    Lm ⋙ Rm ⟶ Ln ⋙ Rn where
  app M := Rm.map ((am.homEquiv M (T.obj (Ln.obj M))).symm
      (an.unit.app M ≫ d.inv.app (Ln.obj M))) ≫ d.hom.app (Ln.obj M)
  naturality {M N} f := by
    have h : Lm.map f ≫
        (am.homEquiv N (T.obj (Ln.obj N))).symm
          (an.unit.app N ≫ d.inv.app (Ln.obj N)) =
        (am.homEquiv M (T.obj (Ln.obj M))).symm
          (an.unit.app M ≫ d.inv.app (Ln.obj M)) ≫ T.map (Ln.map f) := by
      apply (am.homEquiv _ _).injective
      rw [am.homEquiv_naturality_left, Equiv.apply_symm_apply,
        am.homEquiv_naturality_right, Equiv.apply_symm_apply]
      dsimp only [Functor.comp_obj, Functor.comp_map]
      have hu := an.unit.naturality f
      dsimp only [Functor.id_map, Functor.comp_map] at hu
      rw [reassoc_of% hu]
      simpa only [Category.assoc, Functor.comp_map] using
        congrArg (fun k ↦ an.unit.app M ≫ k) (d.inv.naturality (Ln.map f))
    dsimp only [Functor.comp_map]
    rw [← Rm.map_comp_assoc, h, Rm.map_comp, Category.assoc]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun k ↦ Rm.map ((am.homEquiv M (T.obj (Ln.obj M))).symm
        (an.unit.app M ≫ d.inv.app (Ln.obj M))) ≫ k)
      (d.hom.naturality (Ln.map f))

private theorem normalizeRepresentativeTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (T : B ⥤ A) (d : T ⋙ Rm ≅ Rn)
    (P V W : C) (cm : Rm.obj (Lm.obj P) ⟶ V) (cn : Rn.obj (Ln.obj P) ⟶ W)
    (f : V ⟶ W)
    (h : Rm.map ((am.homEquiv P (T.obj (Ln.obj P))).symm
        (an.unit.app P ≫ d.inv.app (Ln.obj P))) ≫ d.hom.app (Ln.obj P) ≫
        Rn.map (Ln.map (Iso.refl P).inv) ≫ cn =
      Rm.map (Lm.map (Iso.refl P).inv) ≫ cm ≫ f) :
    (adjointTransition am an T d).app P ≫ cn = cm ≫ f := by
  simpa [adjointTransition] using h

attribute [local irreducible] Functor.mapDerivedCategory

private theorem sectionTransitionAdjoint
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    sfDerivedReductionTransition l E X n =
      adjointTransition
        (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
        (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
        (normalizedDVRRes.{u, u} l E X n.le_succ)
        (normalizedDVRResCompletedComp.{0, u, u} l E X D hl n.le_succ) := by
  apply (sfDerivedReductionTransition_existsUnique l E X n).unique
    (sfDerivedReductionTransition_existsUnique l E X n).exists.choose_spec
  intro P hP
  have h := normalizedDVR_kflat_transition.{0, u, u} l E X D hl P hP
    (DerivedCategory.Q.obj P) (Iso.refl _) n
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    (normalizedDVRKFlatUnit.{0, u, u} l E X D hl (n + 1) P hP)
    (normalizedDVRKFlatUnit.{0, u, u} l E X D hl n P hP)
  have h' := normalizeRepresentativeTransition
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    (normalizedDVRRes.{u, u} l E X n.le_succ)
    (normalizedDVRResCompletedComp.{0, u, u} l E X D hl n.le_succ)
    (DerivedCategory.Q.obj P) _ _
    (normalizedDVRKFlatComparison.{u, u} l E X (n + 1) P)
    (normalizedDVRKFlatComparison.{u, u} l E X n P)
    (DerivedCategory.Q.map (integralTowerTransition l E X D hl P n)) h
  have hf := congrArg (fun f ↦ DerivedCategory.Q.map f)
    (transition_eq l E X D hl P n)
  have hcmp (m : ℕ) : normalizedDVRKFlatComparison.{u, u} l E X m P =
      sfReductionRepresentativeComparison l E X m P := by
    have hfac := (scalarReductionRestriction l E X m).mapDerivedCategoryFactorsh_hom_app
      (unrestrictedTowerFiniteComplex l E X m P)
    change (scalarReductionRestriction l E X m).mapDerivedCategoryFactorsh.hom.app
        (((scalarReductionExtension l E X m).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) = _ at hfac
    unfold normalizedDVRKFlatComparison sfReductionRepresentativeComparison
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv] at hfac ⊢
    erw [(scalarReductionDerivedExtension l E X m).map_id, DerivedCategory.Qh.map_id,
      Category.id_comp, Category.comp_id]
    erw [(scalarReductionRestriction l E X m).mapDerivedCategory.map_id,
      DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id] at hfac
    dsimp only [DerivedCategory.Qh, HomologicalComplexUpToQuasiIso.Qh,
      Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift, Functor.comp_obj] at hfac ⊢
    erw [Category.comp_id] at hfac
    erw [Category.comp_id, cast_eq]
    exact congrArg (fun f ↦ (scalarReductionDerivedRestriction l E X m).map
      ((scalarReductionCounit l E X m).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ f) hfac.symm
  simpa only [hcmp] using
    h'.trans (congrArg
      (fun f ↦ normalizedDVRKFlatComparison.{u, u} l E X (n + 1) P ≫ f) hf)

attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

private theorem sameRestrictionTransition
    {C B₀ B₁ : Type*} [Category C] [Category B₀] [Category B₁]
    {L₀ L₀' : C ⥤ B₀} {L₁ L₁' : C ⥤ B₁}
    {U₀ : B₀ ⥤ C} {U₁ : B₁ ⥤ C}
    (a₀ : L₀ ⊣ U₀) (a₁ : L₁ ⊣ U₁) (a₀' : L₀' ⊣ U₀) (a₁' : L₁' ⊣ U₁)
    (V : B₀ ⥤ B₁) (c : V ⋙ U₁ ≅ U₀) (X : C) :
    let β₀ := a₀.leftAdjointUniq a₀'
    let β₁ := a₁.leftAdjointUniq a₁'
    let m := (a₁.homEquiv _ _).symm
      (a₀.unit.app X ≫ c.inv.app (L₀.obj X))
    let m' := (a₁'.homEquiv _ _).symm
      (a₀'.unit.app X ≫ c.inv.app (L₀'.obj X))
    (U₁.map m ≫ c.hom.app (L₀.obj X)) ≫ U₀.map (β₀.hom.app X) =
      U₁.map (β₁.hom.app X) ≫ U₁.map m' ≫ c.hom.app (L₀'.obj X) := by
  intro β₀ β₁ m m'
  have hm : a₁.unit.app X ≫ U₁.map m =
      a₀.unit.app X ≫ c.inv.app (L₀.obj X) :=
    (a₁.homEquiv _ _).apply_symm_apply _
  have hm' : a₁'.unit.app X ≫ U₁.map m' =
      a₀'.unit.app X ≫ c.inv.app (L₀'.obj X) :=
    (a₁'.homEquiv _ _).apply_symm_apply _
  have hu₀ := Adjunction.unit_leftAdjointUniq_hom_app a₀ a₀' X
  have hu₁ := Adjunction.unit_leftAdjointUniq_hom_app a₁ a₁' X
  have h : m ≫ V.map (β₀.hom.app X) = β₁.hom.app X ≫ m' := by
    apply (a₁.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.id_obj,
      ← Category.assoc]
    rw [hm, hu₁, hm']
    have hn := c.inv.naturality (β₀.hom.app X)
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, hu₀]
  rw [Category.assoc, ← c.hom.naturality]
  dsimp only [Functor.comp_map]
  rw [← Category.assoc, ← U₁.map_comp, h, U₁.map_comp, Category.assoc]

private def sfPbcComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (n : ℕ) :
    IntegralCoefficientPresentation.reduction
        (completedIntegralCommRingProjectionUnrestricted l E T n) ≅
      sfDerivedReductionRestricted l E T n :=
  Functor.isoWhiskerRight
    ((pbcDerivedScalarAdjunction
      (completedIntegralCommRingProjectionUnrestricted l E T n)).leftAdjointUniq
      (derivedScalarExtensionRestrictionAdjunction.{u, u} l E T n).choose)
    (scalarReductionDerivedRestriction.{u, u} l E T n)

private theorem sfPbcComparison_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) :
    (pbcDerivedScalarAdjunction
      (completedIntegralCommRingProjectionUnrestricted l E T n)).unit.app K ≫
      (sfPbcComparison l E T n).hom.app K = (sfDerivedReductionUnit l E T n).app K := by
  exact Adjunction.unit_leftAdjointUniq_hom_app _ _ K

private theorem sfPbcCompositor
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (f : R ⟶ S) (g : R ⟶ B) (q : S ⟶ B) (h : f ≫ q = g) :
    pbcRestrictComp f q g h = tensorRestrictionComp.{u + 1, u, u + 1} f g q h := by
  apply (pbcRestrictComp_exists f q g h).unique
    (pbcRestrictComp_exists f q g h).exists.choose_spec
  intro M U x
  subst g
  rfl

attribute [local irreducible] tensorRestrictionComp moduleRestrictionComp
  pbcDerivedScalarAdjunction reductionDerivedChange
  normalizedDVRQuotient integralCoefficientSheafTransition

private theorem exactDerived_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    F.mapDerivedCategory = G.mapDerivedCategory := by
  subst G
  rfl

private theorem exactDerivedComp_heq
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Abelian C] [Abelian D] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]
    (F F' : C ⥤ D) (G G' : D ⥤ B)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (hF : F = F') (hG : G = G') :
    HEq (F.mapDerivedCategoryCompIso G).symm (F'.mapDerivedCategoryCompIso G').symm := by
  subst F'
  subst G'
  rfl

private theorem adjointTransition_congr
    {C B₀ B₁ : Type*} [Category C] [Category B₀] [Category B₁]
    {L₀ : C ⥤ B₀} {L₁ : C ⥤ B₁} {U₀ : B₀ ⥤ C} {U₁ : B₁ ⥤ C}
    (a₀ : L₀ ⊣ U₀) (a₁ : L₁ ⊣ U₁) (V V' : B₀ ⥤ B₁)
    (c : V ⋙ U₁ ≅ U₀) (c' : V' ⋙ U₁ ≅ U₀)
    (hV : V = V') (h : HEq c c') (X : C) :
    U₁.map ((a₁.homEquiv X (V.obj (L₀.obj X))).symm
      (a₀.unit.app X ≫ c.inv.app (L₀.obj X))) ≫ c.hom.app (L₀.obj X) =
    U₁.map ((a₁.homEquiv X (V'.obj (L₀.obj X))).symm
      (a₀.unit.app X ≫ c'.inv.app (L₀.obj X))) ≫ c'.hom.app (L₀.obj X) := by
  subst V'
  cases h
  rfl

private theorem sfPbcComparison_step
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (n : ℕ)
    (h : completedIntegralCommRingProjectionUnrestricted l E T (n + 1) ≫
        (detailedSystem l E T).map (homOfLE n.le_succ).op =
      completedIntegralCommRingProjectionUnrestricted l E T n)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) :
    transition (completedIntegralCommRingProjectionUnrestricted l E T (n + 1))
        ((detailedSystem l E T).map (homOfLE n.le_succ).op)
        (completedIntegralCommRingProjectionUnrestricted l E T n) h K ≫
      (sfPbcComparison l E T n).hom.app K =
      (sfPbcComparison l E T (n + 1)).hom.app K ≫
        (sfDerivedReductionTransition l E T n).app K := by
  obtain ⟨D, hl⟩ :=
    existsTestDatum l
  rw [sectionTransitionAdjoint
    l E T D hl n]
  have h' := sameRestrictionTransition
    (pbcDerivedScalarAdjunction (completedIntegralCommRingProjectionUnrestricted l E T n))
    (pbcDerivedScalarAdjunction
      (completedIntegralCommRingProjectionUnrestricted l E T (n + 1)))
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E T n).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E T (n + 1)).choose
    (normalizedDVRRes.{u, u} l E T n.le_succ)
    (normalizedDVRResCompletedComp.{0, u, u} l E T D hl n.le_succ) K
  have hq : (detailedSystem l E T).map (homOfLE n.le_succ).op =
      coefficientStep.{u, u} l E T n := by
    rw [coefficientStep_eq]
    simpa only [detailedSystem, unrestrictedCoefficientStep] using
      Functor.ofOpSequence_map_homOfLE_succ
        (fun n ↦ unrestrictedCoefficientStep l E T n) n
  have hr : pbcRestrict (coefficientStep.{u, u} l E T n) =
      normalizedDVRModuleRes.{u, u} l E T n.le_succ := by
    apply congrArg (SheafOfModules.restrictScalars.{u + 1})
    ext U x
    rfl
  have ht := congrArg (fun e ↦
    (Functor.mapDerivedCategoryCompIso (pbcRestrict (coefficientStep.{u, u} l E T n))
      (pbcRestrict
        (completedIntegralCommRingProjectionUnrestricted l E T (n + 1)))) ≪≫
      Functor.mapDerivedCategoryNatIso e)
    (sfPbcCompositor
      (completedIntegralCommRingProjectionUnrestricted l E T (n + 1))
      (completedIntegralCommRingProjectionUnrestricted l E T n)
      (coefficientStep.{u, u} l E T n) (coefficientStep_comp.{u, u} l E T n))
  have ht' : pbcDerivedRestrictComp
      (completedIntegralCommRingProjectionUnrestricted l E T (n + 1))
      (coefficientStep.{u, u} l E T n)
      (completedIntegralCommRingProjectionUnrestricted l E T n)
      (coefficientStep_comp.{u, u} l E T n) =
      normalizedDVRResCompletedComp.{0, u, u} l E T D hl n.le_succ := by
    rw [completedComp_eq.{0, u, u} l E T D hl n]
    simp only [pbcDerivedRestrictComp, pbcDerivedRestrict, moduleRestrictionComp]
    convert ht using 2
    · congr 2
    · congr 1
    · let : PreservesFiniteLimits (pbcRestrict (coefficientStep.{u, u} l E T n)) :=
        pbcRestrict_limits _
      let : PreservesFiniteColimits (pbcRestrict (coefficientStep.{u, u} l E T n)) :=
        pbcRestrict_colimits _
      apply exactDerived_eq
      exact congrArg (fun V ↦ V ⋙ scalarReductionRestriction.{u, u} l E T (n + 1))
        hr.symm
    · let : PreservesFiniteLimits (pbcRestrict (coefficientStep.{u, u} l E T n)) :=
        pbcRestrict_limits _
      let : PreservesFiniteColimits (pbcRestrict (coefficientStep.{u, u} l E T n)) :=
        pbcRestrict_colimits _
      exact congrArg Iso.symm (eq_of_heq (exactDerivedComp_heq _ _ _ _ hr.symm rfl))
  have hd : pbcDerivedRestrict (coefficientStep.{u, u} l E T n) =
      normalizedDVRRes.{u, u} l E T n.le_succ := by
    let : PreservesFiniteLimits (pbcRestrict (coefficientStep.{u, u} l E T n)) :=
      pbcRestrict_limits _
    let : PreservesFiniteColimits (pbcRestrict (coefficientStep.{u, u} l E T n)) :=
      pbcRestrict_colimits _
    let := normalizedDVRModuleRes_limits.{u, u} l E T n.le_succ
    let := normalizedDVRModuleRes_colimits.{u, u} l E T n.le_succ
    exact exactDerived_eq _ _ hr
  have hchange := adjointTransition_congr
    (pbcDerivedScalarAdjunction (completedIntegralCommRingProjectionUnrestricted l E T n))
    (pbcDerivedScalarAdjunction
      (completedIntegralCommRingProjectionUnrestricted l E T (n + 1)))
    (pbcDerivedRestrict (coefficientStep.{u, u} l E T n))
    (normalizedDVRRes.{u, u} l E T n.le_succ) _ _ hd (heq_of_eq ht') K
  have hchange' := congrArg (fun f ↦ f ≫ (sfPbcComparison l E T n).hom.app K) hchange
  simp only [hq] at h ⊢
  exact hchange'.trans (by
    simpa only [sfPbcComparison, adjointTransition, Functor.id_obj,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight,
      sfDerivedReductionRestricted, Functor.comp_obj,
      scalarReductionDerivedRestriction, pbcDerivedRestrict] using h')

private theorem coefficientReductionComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (c : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E T)
    (hc : (adicLisseForget T).mapIso c = integralDetailedCoefficientComparison T l E) :
    ∃ γ : ∀ K n,
      (IntegralCoefficientPresentation.reduction
        (pbcAdicProjection T (pbcIntegralDatum l E) n)).obj
          ((pbcDerivedRestrict c.hom).obj K) ≅
        (pbcDerivedRestrict c.hom).obj ((sfDerivedReductionRestricted l E T n).obj K),
      (∀ K n, (pbcDerivedScalarAdjunction
        (pbcAdicProjection T (pbcIntegralDatum l E) n)).unit.app
          ((pbcDerivedRestrict c.hom).obj K) ≫ (γ K n).hom =
        (pbcDerivedRestrict c.hom).map ((sfDerivedReductionUnit l E T n).app K)) ∧
      ∀ K n, (reconstructionStep T (pbcIntegralDatum l E) n).app
          ((pbcDerivedRestrict c.hom).obj K) ≫ (γ K n).hom =
        (γ K (n + 1)).hom ≫
          (pbcDerivedRestrict c.hom).map ((sfDerivedReductionTransition l E T n).app K) := by
  classical
  let q := integralCoefficientULift l E
  have hq := fun n ↦ (integralCoefficientULift_exists l E n).exists.choose_spec
  obtain ⟨hρ, H⟩ := (IntegralCoefficientPresentation.comparison l E T).2.2.2
  obtain ⟨_, _, _, H⟩ := H q hq
  have hcn (n : ℕ) : c.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
      pbcAdicProjection T (pbcIntegralDatum l E) n ≫ (level l E T q n).hom := by
    apply (adicLisseForget T).map_injective
    simp only [Functor.map_comp]
    have hn := (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec n
    have hn' : (integralDetailedCoefficientComparison T l E).hom ≫
        limit.π (integralCoefficientSheafSystem l E T) (op n) =
        (adicLisseForget T).map (pbcAdicProjection T (pbcIntegralDatum l E) n) ≫
          (integralDetailedLevelComparison T l E n).hom := by
      simpa only [integralDetailedCoefficientComparison] using hn
    rw [← hc] at hn'
    exact hn'
  have Hc := H c hcn
  obtain ⟨r, hr, α, hα, ht, _⟩ := Hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let β (n : ℕ) := restrictedComparison c (level l E T q n)
    (pbcAdicProjection T (pbcIntegralDatum l E) n)
    (completedIntegralCommRingProjectionUnrestricted l E T n) (r n) (α n)
  let γ K n := β n K ≪≫
    (pbcDerivedRestrict c.hom).mapIso ((sfPbcComparison l E T n).app K)
  refine ⟨γ, ?_, ?_⟩
  · intro K n
    dsimp only [γ, Iso.trans_hom, Functor.mapIso_hom]
    erw [← Category.assoc, hα]
    rw [← Functor.map_comp]
    exact congrArg (pbcDerivedRestrict c.hom).map (sfPbcComparison_unit l E T n K)
  · intro K n
    dsimp only [γ, Iso.trans_hom, Functor.mapIso_hom]
    erw [← Category.assoc, ht K (n + 1) n n.le_succ]
    simp only [Category.assoc]
    rw [← Functor.map_comp]
    have hs := sfPbcComparison_step l E T n (hρ _ _ n.le_succ) K
    erw [hs]
    rw [Functor.map_comp]
    rfl

/-- Transport of the completion reflector, retaining its unit and the canonical
intrinsic reduction maps. This compares completion objects before imposing any
completeness, boundedness or constructibility condition on the input.

Source: Stacks Tags 099M, 099N and 06YY; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-pur-completed-coefficient-completion-roos-transport).

Proof: the equation on the coefficient isomorphism identifies its finite projections
with the already normalized integralDetailedLevelComparison. At each positive level,
the tensor/restriction adjunction therefore identifies reduction after inverse scalar
restriction with sfDerivedReductionRestricted. On flat K-flat representatives these
maps send a pure tensor to the same tensor with its coefficient transported. The
transition squares and augmentation squares follow on these tensors and descend by
the universal derived tensor counits. Thus this is an isomorphism of the augmented
reduction sequences, including their canonical units, rather than only levelwise
isomorphisms of their objects.

Apply completedKoszulQuotientComparison and completedKoszulReductionRoosTriangle to
an intrinsic completed-coefficient representative. The Koszul reflector and the
actual complete-subcategory reflector represent the same adjunction, so their unique
unit-compatible comparison identifies the first vertex with pbcActualCompletion K.
Exact restriction along the inverse ring isomorphism preserves products and
triangles. Transport the resulting Roos triangle through the preceding sequence
isomorphism. Its coordinate unit equations give the displayed product unit equation
by product extensionality. All comparisons use the positive quotient levels; the
argument also applies to the zero object, the empty scheme and residue level one. -/
theorem completedCoefficientCompletionRoosTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (c : pbcAdicCompletion W (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E W)
    (_hc : (adicLisseForget W).mapIso c = integralDetailedCoefficientComparison W l E)
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    ∃ hp : HasProduct (fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj
        ((pbcDerivedRestrict c.inv).obj K)),
      letI := hp
      ∃ (p : (pbcDerivedRestrict c.inv).obj
          ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) ⟶
          ∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj
            ((pbcDerivedRestrict c.inv).obj K))
        (δ : (∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj
            ((pbcDerivedRestrict c.inv).obj K)) ⟶
          ((pbcDerivedRestrict c.inv).obj
            ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K))⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle
          (fun n ↦ (sfDerivedReductionTransition l E W n).app
            ((pbcDerivedRestrict c.inv).obj K))
          ((pbcDerivedRestrict c.inv).obj
            ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)) p δ ∧
        (pbcDerivedRestrict c.inv).map
            ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K) ≫ p =
          Pi.lift (fun n ↦ (sfDerivedReductionUnit l E W n).app
            ((pbcDerivedRestrict c.inv).obj K)) := by
  classical
  let F := (pbcRestrict c.hom).mapDerivedCategory
  let H := (pbcRestrict c.inv).mapDerivedCategory
  let hF₀ : (pbcRestrict c.hom).IsEquivalence := (restrict_equivalence c).1
  let hH₀ : (pbcRestrict c.inv).IsEquivalence := (restrict_equivalence c).2.1
  let : F.IsEquivalence := by
    change (pbcRestrict c.hom).mapDerivedCategory.IsEquivalence
    infer_instance
  let : H.IsEquivalence := by
    change (pbcRestrict c.inv).mapDerivedCategory.IsEquivalence
    infer_instance
  let : F.CommShift ℤ := by dsimp only [F]; infer_instance
  let : F.IsTriangulated := by dsimp only [F]; infer_instance
  let : F.Additive := by dsimp only [F]; infer_instance
  let round : H ⋙ F ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso (pbcRestrict c.inv) (pbcRestrict c.hom)) ≪≫
      Functor.mapDerivedCategoryNatIso
        (pbcRestrictComp c.hom c.inv (𝟙 _) c.hom_inv_id ≪≫ restrictId _) ≪≫
      Functor.mapDerivedCategoryIdIso _
  let := derived_products W (completedIntegralCommRingSheafUnrestricted l E W)
  let := derived_products W (pbcAdicCompletion W (pbcIntegralDatum l E))
  obtain ⟨β, hβu, hβt⟩ := coefficientReductionComparison l E W c _hc
  dsimp only [pbcDerivedRestrict] at β hβu hβt
  let J := H.obj K
  let R n := IntegralCoefficientPresentation.reduction
    (pbcAdicProjection W (pbcIntegralDatum l E) n)
  let a (n : ℕ) : F.obj ((sfDerivedReductionRestricted l E W n).obj J) ≅ (R n).obj K :=
    (β J n).symm ≪≫ (R n).mapIso (round.app K)
  have ha (n : ℕ) :
      F.map ((sfDerivedReductionTransition l E W n).app J) ≫ (a n).hom =
        (a (n + 1)).hom ≫ (reconstructionStep W (pbcIntegralDatum l E) n).app K := by
    apply (cancel_epi (β J (n + 1)).hom).1
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hβt]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact ((reconstructionStep W (pbcIntegralDatum l E) n).naturality (round.hom.app K)).symm
  obtain ⟨hp, p, δ, hδ, hu⟩ := pbcNormalizedRoos W (pbcIntegralDatum l E) K
  let := hp
  refine ⟨inferInstance, ?_⟩
  have huv (n : ℕ) :
      F.map (H.map ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K)) ≫
        (round.app ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)).hom ≫
        p ≫ Pi.π _ n =
      F.map ((sfDerivedReductionUnit l E W n).app J) ≫ (a n).hom := by
    change (H ⋙ F).map _ ≫ round.hom.app _ ≫ p ≫ Pi.π _ n = _
    rw [round.hom.naturality_assoc]
    dsimp only [Functor.id_map, Functor.id_obj]
    erw [hu]
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← hβu]
    have hh := congrArg (fun f ↦
      (pbcDerivedScalarAdjunction (pbcAdicProjection W (pbcIntegralDatum l E) n)).unit.app
        (F.obj J) ≫ f) ((β J n).hom_inv_id_assoc ((R n).map (round.app K).hom))
    have hh' := (Category.assoc _ _ _).trans hh
    refine Eq.trans ?_ hh'.symm
    have hn := (pbcDerivedScalarAdjunction
      (pbcAdicProjection W (pbcIntegralDatum l E) n)).unit.naturality
        (round.hom.app K)
    simpa only [Functor.id_map, Functor.id_obj, Iso.app_hom, J, R,
      IntegralCoefficientPresentation.reduction, Functor.comp_obj, Functor.comp_map] using hn
  obtain ⟨p', δ', hδ', hu'⟩ := reflectNormalizedRoos F a
    (fun n ↦ (sfDerivedReductionTransition l E W n).app J)
    (fun n ↦ (reconstructionStep W (pbcIntegralDatum l E) n).app K) ha
    (round.app ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)) p δ hδ
    (H.map ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K))
    (fun n ↦ (sfDerivedReductionUnit l E W n).app J) huv
  refine ⟨p', δ', hδ', ?_⟩
  apply Pi.hom_ext
  intro n
  simpa only [Category.assoc, Pi.lift_comp_π, H, J, pbcDerivedRestrict] using hu' n

end WeilConjectures
