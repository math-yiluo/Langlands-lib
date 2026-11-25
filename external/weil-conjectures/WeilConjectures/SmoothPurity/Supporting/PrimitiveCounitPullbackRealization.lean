/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PrimitiveCounit.PrimitiveCounitComparisonModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackSuccessor
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import all WeilConjectures.AlgebraicGeometry.MilnorTower
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-! # Pullback realization on strict quotient models

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok, together with
strict quotient-system models and normalized Roos descent.
(blueprint: lem-pur-primitive-counit-pullback-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived

universe t u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard constantSheaf Functor.leftAdjoint
  integralPullbackDescent OrdinaryTowerProof.directEvaluation
  OrdinaryTowerProof.inverseEvaluation PrimitiveCounit.inverseEvaluation

attribute [local implicit_reducible]
  HomologicalComplex.asFunctor HomologicalComplex.complexOfFunctorsToFunctorToComplex
  integralOperationsGoodLocalization
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  PrimitiveCounit.direct PrimitiveCounit.inverse
  integralComparisonSequenceDirectImage integralComparisonSequencePullback
  PrimitiveCounit.base PrimitiveCounit.ringMap PrimitiveCounit.ringComponent
  integralComparisonSequenceBaseChange integralComparisonSequenceRingMap
  integralDerivedPullback integralDerivedPullbackComparison
  coefficientSequenceLimit PrimitiveCounit.pull
  integralOperationsPullbackTowerFunctor integralOperationsLevelPullback
  PrimitiveCounit.inverseComplexEvaluation PrimitiveCounit.restrictEvaluation
  PrimitiveCounit.pullRestrictionIso PrimitiveCounit.RoosComparison
  roosF roosConeFunctor integralOperationsRoosFunctor integralOperationsRoos

section
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem primitiveReductionEvaluationTransport (W : Scheme.{t})
    (S T : CoefficientDerivedSystemReduction l E W)
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).map
        ((S.adjunction.leftAdjointUniq T.adjunction).hom.app K) ≫
      (T.reductionEvaluation n).hom.app K = (S.reductionEvaluation n).hom.app K := by
  let V := coefficientSequenceDerivedEvaluation l E W n
  let R := coefficientFiniteDerivedRestriction l E W n
  let α := S.adjunction.leftAdjointUniq T.adjunction
  have he : (S.reductionEvaluation n).inv.app K ≫ V.map (α.hom.app K) =
      (T.reductionEvaluation n).inv.app K := by
    apply ((coefficientFiniteAdjunction l E W n).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R.map_comp,
      ← Category.assoc, ← S.unit_projection]
    have hp := (coefficientSequenceProjection l E W n).naturality (α.hom.app K)
    dsimp only [Functor.comp_map] at hp
    rw [Category.assoc, ← hp, ← Category.assoc]
    rw [Adjunction.unit_leftAdjointUniq_hom_app, T.unit_projection]
  apply (cancel_epi ((S.reductionEvaluation n).inv.app K)).1
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
    congrArg (fun a ↦ a ≫ (T.reductionEvaluation n).hom.app K) he

private theorem primitiveIsoEqOfSections
    {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}} {F G : D ⥤ SheafOfModules.{v} R}
    (e : F ≅ G) (h : F = G)
    (he : ∀ N U (x : (F.obj N).val.obj U), HEq ((e.hom.app N).val.app U x) x) :
    e = eqToIso h := by
  subst G
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact eq_of_heq (he N U x)

private theorem primitiveInverseMateUnit
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F : C ⥤ D} {G : D ⥤ C} {L : A ⥤ B} {R : B ⥤ A}
    {U : C ⥤ A} {V : D ⥤ B} (adj : F ⊣ G) (adjn : L ⊣ R)
    (d : G ⋙ U ≅ V ⋙ R) (e : U ⋙ L ≅ F ⋙ V)
    (he : e.hom = ((mateEquiv adj adjn).symm d.hom)) (M : C) :
    U.map (adj.unit.app M) ≫ d.hom.app (F.obj M) ≫ R.map (e.inv.app M) =
      adjn.unit.app (U.obj M) := by
  have hu := unit_mateEquiv_symm adj adjn d.hom M
  change U.map (adj.unit.app M) ≫ d.hom.app (F.obj M) =
    adjn.unit.app (U.obj M) ≫
      R.map (((mateEquiv adj adjn).symm d.hom).app M) at hu
  rw [← he] at hu
  rw [← Category.assoc, hu, Category.assoc, ← R.map_comp,
    e.hom_inv_id_app]
  erw [R.map_id, Category.comp_id]

-- Comparing the concrete ringed-site functors requires additional elaboration work.
attribute [local irreducible] coefficientSequenceEvaluation
  Scheme.coefficientProEtaleModuleDirectImage Scheme.coefficientProEtaleDirectRingMap in
private theorem primitiveOrdinaryDirectEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y)
    (n : ℕ) :
    OrdinaryTowerProof.directEvaluation l E f n =
      eqToIso (PrimitiveCounit.directEvaluation_eq l E f n) := by
  exact primitiveIsoEqOfSections (OrdinaryTowerProof.directEvaluation l E f n)
    (PrimitiveCounit.directEvaluation_eq l E f n)
    (fun N U x ↦ OrdinaryTowerProof.directEvaluation_sections l E f n N U.unop x)

section
attribute [local irreducible] Padic
  Scheme.coefficientProEtaleDirectRingMap coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf PrimitiveCounit.inverse PrimitiveCounit.direct
  coefficientSequenceEvaluation

private theorem primitiveInverseEvaluation_choice {X Y : Scheme.{t}} (f : X ⟶ Y)
    (n : ℕ) :
    PrimitiveCounit.inverseEvaluation l E f n =
      (PrimitiveCounit.inverseEvaluation_existsUnique l E f n).choose := by
  delta PrimitiveCounit.inverseEvaluation
  rfl

end

-- Identify the concrete functors once before applying their abstract mate equation.
attribute [local irreducible] coefficientSequenceEvaluation
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModuleDirectImage
  Scheme.coefficientProEtaleModulePullback Scheme.coefficientProEtaleDirectRingMap in
private theorem primitiveOrdinaryInverseEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y)
    (n : ℕ) :
    PrimitiveCounit.inverseEvaluation l E f n =
      (OrdinaryTowerProof.inverseEvaluation l E f n).symm := by
  let e : coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n ≅
      PrimitiveCounit.inverse l E f ⋙ coefficientSequenceEvaluation l E X n :=
    OrdinaryTowerProof.inverseEvaluation l E f n
  have he : e.hom = ((mateEquiv
      (Adjunction.ofIsRightAdjoint (PrimitiveCounit.direct l E f))
      (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
        (CommRingCat.of (ULift.{t + 1} (finiteCoefficientRing l E (n + 1)))))).symm
          (eqToIso (PrimitiveCounit.directEvaluation_eq l E f n)).hom) := by
    rw [← primitiveOrdinaryDirectEvaluation l E f n]
    exact OrdinaryTowerProof.inverseEvaluation_hom l E f n
  have hnorm := fun M ↦ primitiveInverseMateUnit
    (Adjunction.ofIsRightAdjoint (PrimitiveCounit.direct l E f))
    (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (finiteCoefficientRing l E (n + 1)))))
    (eqToIso (PrimitiveCounit.directEvaluation_eq l E f n)) e he M
  have h := (PrimitiveCounit.inverseEvaluation_existsUnique l E f n).choose_spec.2 e.symm hnorm
  calc
    PrimitiveCounit.inverseEvaluation l E f n =
        (PrimitiveCounit.inverseEvaluation_existsUnique l E f n).choose :=
      primitiveInverseEvaluation_choice l E f n
    _ = e.symm := h.symm

private theorem primitiveIsoTransHomApp
    {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (e : F ≅ G) (d : G ≅ H) (k : F ≅ H) (h : e ≪≫ d = k) (P : C) :
    e.hom.app P ≫ d.hom.app P = k.hom.app P := by
  exact congrArg (fun a : F ≅ H ↦ a.hom.app P) h

end

-- The strict quotient comparison carries the full independent-universe coefficient data.
attribute [local irreducible] coefficientSequenceEvaluation
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModuleDirectImage
  Scheme.coefficientProEtaleModulePullback Scheme.coefficientProEtaleDirectRingMap in
/-- Completed inverse image is the total limit of inverse image of coherent reduction,
with its prescribed comparison on every good representative.
Source: Stacks Tag 0941; steps 1--3 of the primitive comparison argument.
(blueprint: lem-pur-primitive-counit-pullback-realization).

Proof: represent the coherent reduction of a flat-term K-flat input by its actual
strict quotient system. Apply the exact sequence inverse image. Its unit-normalized
finite evaluation comparison identifies the resulting restricted tower with the
pullback tower of the integral operation, including every transition. Normalized
Roos descent and the integral operation's representative comparison give the
isomorphism on good representatives. The localization universal property descends
it to every derived input and gives the displayed model equation. The normalization
on K-injective resolutions makes the comparison agree with the prescribed Roos
realization. This includes identity maps, zero inputs and empty schemes. -/
theorem primitiveCounitPullbackRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y)
    (ρ : PrimitiveCounit.RoosRealization l E X) :
    ∃ r : integralDerivedPullback l E f ≅
      S.reduction ⋙ PrimitiveCounit.pull l E f ⋙ coefficientSequenceLimit l E X,
      PrimitiveCounit.PullModel l E f S ρ r := by
  classical
  obtain ⟨S₀, _⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  obtain ⟨M, ⟨D⟩⟩ := CompletionUnit.fixedCalculusModels l E Y S₀
  let α := S.adjunction.leftAdjointUniq S₀.adjunction
  let A := (integralOperationsGoodComplex l E Y).ι
  let R := M.quotient l E Y
  let F := PrimitiveCounit.inverse l E f
  let U := coefficientSequenceRestriction l E X
  let H : (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ) ⥤
      DerivedCategory (scalarReductionSource l E X) :=
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  let T := F.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let L := coefficientSequenceLimit l E X
  let V := PrimitiveCounit.pull l E f ⋙ L
  let bridge : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ H ≅
      roosF ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun Z ↦ DerivedCategory.Q.mapIso
      (PrimitiveCounit.roosBridge l E X Z)) (by
      intro Z Z' a
      change _ ≫ DerivedCategory.Q.map (𝟙 _) = DerivedCategory.Q.map (𝟙 _) ≫ _
      erw [DerivedCategory.Q.map_id, DerivedCategory.Q.map_id, Category.comp_id, Category.id_comp]
      change DerivedCategory.Q.map (integralOperationsRoosMap
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a)) =
          DerivedCategory.Q.map (roosF.map a)
      apply congrArg (fun k : integralOperationsRoosFunctor.obj Z.asFunctor ⟶
          integralOperationsRoosFunctor.obj Z'.asFunctor ↦ DerivedCategory.Q.map k)
      change integralOperationsRoosMap
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a) = roosF.map a
      rw [AlgebraicGeometry.Scheme.ProEt.roosMap_eq]
      rfl)
  let η : DerivedCategory.Q ⋙ V ≅ T ⋙ H :=
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors L ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (Functor.isoWhiskerRight U.mapDerivedCategoryFactors
            (coefficientConstantTowerLimit l E X) ≪≫
          Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ))
            (ρ.comparison.symm ≪≫ bridge.symm))
  let ε : DerivedCategory.Q ⋙ S.reduction ⟶ R ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q α.hom ≫ D.reductionComparison
  let d : integralOperationsGoodLocalization l E Y ⋙ S.reduction ≅
      A ⋙ R ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      haveI := D.reduction_isIso P.obj P.property.1 P.property.2
      exact α.app (DerivedCategory.Q.obj P.obj) ≪≫ asIso (D.reductionComparison.app P.obj))
      (by intro P Q a; exact ε.naturality a.hom)
  let θ : R ⋙ T ≅ integralOperationsPullbackTowerFunctor l E f :=
    OrdinaryTowerProof.comparison l E f M
  let δ : integralOperationsGoodLocalization l E Y ⋙ (S.reduction ⋙ V) ≅
      integralOperationsPullbackOnGood l E f :=
    Functor.isoWhiskerRight d V ≪≫ Functor.isoWhiskerLeft (A ⋙ R) η ≪≫
      Functor.isoWhiskerLeft A (Functor.isoWhiskerRight θ H)
  have huniq := (integralPullbackDescent l E f).universal
  obtain ⟨r, hr, _⟩ := huniq (S.reduction ⋙ V) δ
  change Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) r ≪≫ δ =
    integralDerivedPullbackComparison l E f at hr
  refine ⟨r, ?_⟩
  intro P
  let C : CochainComplex (coefficientSequenceModules l E Y) ℤ := R.obj P.obj
  let e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C := d.app P
  let κ (n : ℕ) :
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj :=
    (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P.obj
  let z := θ.app P.obj
  refine ⟨C, e, κ, z, ?_, ?_, ?_⟩
  · constructor
    · intro n
      change (coefficientSequenceDerivedEvaluation l E Y n).map
          (α.hom.app (DerivedCategory.Q.obj P.obj) ≫ D.reductionComparison.app P.obj) ≫
          (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map (κ n).hom = _
      dsimp only [C, κ, R]
      simp only [Iso.app_hom]
      rw [Functor.map_comp, Category.assoc,
        D.reduction_evaluation P.obj P.property.1 P.property.2 n,
        ← Category.assoc, primitiveReductionEvaluationTransport]
    · intro m n h
      apply HomologicalComplex.hom_ext
      intro i
      exact M.transition (P.obj.X i) h
  · intro n
    apply HomologicalComplex.hom_ext
    intro i
    change ((θ.hom.app P.obj).app (op n)).f i = _
    dsimp only [θ]
    rw [OrdinaryTowerProof.comparison_hom_app_f]
    simp only [κ, PrimitiveCounit.restrictEvaluation, PrimitiveCounit.inverseComplexEvaluation,
      primitiveOrdinaryInverseEvaluation, OrdinaryTowerProof.level,
      OrdinaryTowerProof.moduleLevel, Functor.mapHomologicalComplexCompIso,
      Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Iso.symm_inv,
      Iso.app_hom]
    dsimp only [HomologicalComplex.Hom.isoOfComponents,
      NatTrans.mapHomologicalComplex_app_f, NatIso.mapHomologicalComplex,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
      Functor.whiskerLeft_app]
    simp only [Functor.map_comp]
    rfl
  · have he := primitiveIsoTransHomApp
      (Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) r) δ
      (integralDerivedPullbackComparison l E f) hr P
    change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (V.map e.hom ≫ η.hom.app C ≫ H.map z.hom) =
      (integralDerivedPullbackComparison l E f).hom.app P at he
    rw [← he]
    have hη : V.map e.hom ≫ η.hom.app C ≫
        DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E X _).hom =
      (coefficientConstantTowerLimit l E X).map
        (PrimitiveCounit.pullRestrictionIso l E f S P.obj C e).hom ≫
          ρ.comparison.inv.app _ := by
      dsimp only [η, V, L, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.trans_hom,
        Iso.symm_hom, NatTrans.comp_app, Category.assoc]
      dsimp only [bridge, NatIso.ofComponents_inv_app, Functor.mapIso_inv]
      simp only [Category.assoc]
      erw [← DerivedCategory.Q.map_comp, Iso.inv_hom_id, DerivedCategory.Q.map_id,
        Category.comp_id]
      simp only [PrimitiveCounit.pullRestrictionIso, Iso.trans_hom, Functor.mapIso_hom,
        Iso.app_hom, coefficientSequenceLimit, coefficientSequenceDerivedRestriction,
        Functor.comp_map, Functor.map_comp, Category.assoc]
      rfl
    change (r.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (V.map e.hom ≫ η.hom.app C ≫ H.map z.hom)) ≫
        H.map z.inv ≫ DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E X _).hom = _
    simp only [Category.assoc]
    rw [← H.map_comp_assoc, z.hom_inv_id]
    erw [H.map_id, Category.id_comp]
    simpa only [Category.assoc] using
      congrArg (fun a ↦ r.hom.app (DerivedCategory.Q.obj P.obj) ≫ a) hη

end WeilConjectures
