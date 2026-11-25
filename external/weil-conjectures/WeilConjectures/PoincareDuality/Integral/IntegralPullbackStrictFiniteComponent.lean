/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # The finite component of a strict normalized pullback comparison

Source: Stacks Tags 03D3, 099N(5), and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Replaying sectionwise transport proofs for tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.mapDerivedCategoryNatIso
attribute [local implicit_reducible] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
attribute [local implicit_reducible] WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.coefficientFiniteDerivedRestriction
  WeilConjectures.coefficientConstantTowerEvaluation
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  CategoryTheory.NatIso.mapHomologicalComplex CategoryTheory.NatTrans.mapHomologicalComplex
  HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
attribute [local irreducible] CategoryTheory.constantSheaf CategoryTheory.presheafToSheaf
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Exact evaluation after scalar restriction, computed on a complex of strict systems.
Source: Stacks 0941 (blueprint: lem-pod-integral-pullback-strict-finite-component). -/
@[irreducible] def integralComparisonRestrictedEvaluationFactors (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (coefficientFiniteDerivedRestriction l E W n).obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj
        ((((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (.up ℤ)).obj C).asFunctor.obj (op n)) :=
  ((coefficientRestrictedEvaluationIso l E W n).app (DerivedCategory.Q.obj C)).symm ≪≫
    (coefficientConstantTowerEvaluation l E W n).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app C) ≪≫
    (coefficientConstantTowerEvaluationFactors l E W n).app
      (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)

section Generators

private theorem zeroOfFiniteLimits
    {A B : Type*} [Category A] [Category B] [HasZeroMorphisms A] [HasZeroMorphisms B]
    [HasZeroObject A] [HasZeroObject B] (F : A ⥤ B) [PreservesFiniteLimits F] :
    F.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_preserves_terminal_object (F := F)

attribute [local instance 30000] zeroOfFiniteLimits

private theorem additiveOfFiniteLimits
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [PreservesFiniteLimits F] : F.Additive :=
  Functor.additive_of_preserves_binary_products F

attribute [local instance 50] additiveOfFiniteLimits

private theorem iso_conjugate {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (a : F ≅ G) {M N : A} (b : M ⟶ N) :
    a.inv.app M ≫ F.map b ≫ a.hom.app N = G.map b := by
  rw [← a.inv.naturality_assoc, a.inv_hom_id_app, Category.comp_id]

private theorem mapped_square {A B : Type*} [Category A] [Category B]
    (R : A ⥤ B) {S : B} {M N P Q T : A}
    (q : S ⟶ R.obj P) (e : S ⟶ R.obj M) (α : S ⟶ R.obj N)
    (H : N ⟶ Q) (a : Q ⟶ M) (k : M ⟶ P) (b : P ⟶ T) (h : Q ⟶ T)
    (hq : q = e ≫ R.map k) (he : e = α ≫ R.map H ≫ R.map a)
    (hh : a ≫ k ≫ b = h) : q ≫ R.map b = α ≫ R.map (H ≫ h) := by
  rw [hq, he]
  simp only [Category.assoc, ← R.map_comp]
  rw [hh]

attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits
attribute [local irreducible] coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

private def restrictionEvaluation (W : Scheme.{u}) (n : ℕ) :
    coefficientSequenceRestriction l E W ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) ≅
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  eqToIso (coefficientSequenceRestriction_evaluation l E W n)

attribute [local irreducible] restrictionEvaluation

private theorem finitePullback_limits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteLimits
      (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f) :=
  proEtaleRingModulePullback_preservesFiniteLimits f _ _ _

private theorem finitePullback_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteColimits
      (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f) :=
  proEtaleRingModulePullback_preservesFiniteColimits f _ _ _

private theorem nativeFinitePullback_limits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteLimits (show normalizedDVRModules l E Y n ⥤
      normalizedDVRModules l E X n from
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f) :=
  finitePullback_limits l E f n

private theorem mixedFinitePullback_limits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteLimits (show normalizedDVRModules l E Y n ⥤
      X.proEtaleRingModules (X.proEtaleConstantRing
        (Padic.coefficientExtensionRing l E (n + 1))) from
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f) :=
  finitePullback_limits l E f n

private theorem mixedFinitePullback_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteColimits (show normalizedDVRModules l E Y n ⥤
      X.proEtaleRingModules (X.proEtaleConstantRing
        (Padic.coefficientExtensionRing l E (n + 1))) from
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f) :=
  finitePullback_colimits l E f n

private theorem nativeFinitePullback_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteColimits (show normalizedDVRModules l E Y n ⥤
      normalizedDVRModules l E X n from
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f) :=
  finitePullback_colimits l E f n

attribute [local instance] finitePullback_limits finitePullback_colimits
  nativeFinitePullback_limits nativeFinitePullback_colimits
  mixedFinitePullback_limits mixedFinitePullback_colimits

private theorem iso_section_inv {A : Type*} [Category A]
    {J : GrothendieckTopology A} {S : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} S} (a : M ≅ N) (U : Aᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U)
    (h : a.hom.val.app U x = y) : a.inv.val.app U y = x := by
  rw [← h]
  exact congrArg (fun b : M ⟶ M ↦ b.val.app U x) a.hom_inv_id

private theorem abEqToHom_cancel {A B : AddCommGrpCat.{u}} (h : A = B) (x : A) :
    (eqToHom h.symm) ((eqToHom h) x) = x := by
  subst B
  rfl

private theorem eqToHom_section {A : Type*} [Category A]
    {J : GrothendieckTopology A} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (h : M = N) (U : Aᵒᵖ) (x : M.val.obj U) :
    HEq ((eqToHom h).val.app U x) x := by
  subst N
  rfl

private theorem restrictionEvaluation_section {X : Scheme.{u}}
    (M : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    (((restrictionEvaluation l E X n).app M).hom.val.app U)
      (integralComparisonRestrictedSection l E X M n U x) =
        coefficientEvaluationSection l E X M n U x := by
  unfold restrictionEvaluation
  simp only [Iso.app_hom, eqToIso.hom, eqToHom_app]
  apply eq_of_heq
  have h := eqToHom_section
    (congrArg (fun F ↦ F.obj M) (coefficientSequenceRestriction_evaluation l E X n))
    U (integralComparisonRestrictedSection l E X M n U x)
  exact (h.trans (cast_heq _ _)).trans
    (show HEq (coefficientEvaluationSection l E X M n U x) x from by rfl).symm

private theorem pullbackLevel_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n)
    (N : integralOperationsFiniteModules l E X n)
    (a b : (SheafOfModules.restrictScalars
        (integralOperationsProjection l E X n)).obj
          ((integralOperationsLevelPullback l E f n).obj M) ⟶
      (SheafOfModules.restrictScalars (integralOperationsProjection l E X n)).obj N)
    (h : ∀ (U : Y.ProEt) (x : M.val.obj (op U)),
      a.val.app (op ((proEtaleBaseChange f).obj U))
          (integralOperationsPullbackGenerator l E f n M U x) =
        b.val.app (op ((proEtaleBaseChange f).obj U))
          (integralOperationsPullbackGenerator l E f n M U x)) : a = b := by
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      (integralOperationsProjection l E X n).hom :=
    completedProjection_locallySurjective l E X n
  apply SheafOfModules.IntegralPullbackProof.restricted_hom_ext
    (integralOperationsBaseChange f) (𝟙 _)
    (integralOperationsDirectRingMap l E f n)
    (integralOperationsPullbackAdjunction l E f n)
    (integralOperationsProjection l E X n) (integralOperationsProjection l E X n)
    (Category.comp_id _) M N a b
  intro U x
  exact h U.unop x

private def finiteEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙
        proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f :=
  finiteSystemPullbackEvaluation (integralSystemRings l E) (integralSystemTransition l E) f n

attribute [local irreducible] finiteEvaluation

private theorem finiteEvaluation_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E Y) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((finiteEvaluation l E f n).hom.app M).val.app
        (op ((proEtaleBaseChange f).obj U))
        (coefficientEvaluationSection l E X
          ((integralComparisonSequencePullback l E f).obj M) n
          (op ((proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f M n U x)) =
      ((integralFinitePullbackModel l E f n).hom.app
        ((coefficientSequenceEvaluation l E Y n).obj M)).val.app
          (op ((proEtaleBaseChange f).obj U))
          (integralOperationsPullbackGenerator l E f n
            ((coefficientSequenceEvaluation l E Y n).obj M) U
            (coefficientEvaluationSection l E Y M n (op U) x)) := by
  have h₁ := (finiteSystemPullbackEvaluation_existsUnique
    (integralSystemRings l E) (integralSystemTransition l E) f n).exists.choose_spec M U x
  have h₂ := (integralFinitePullbackModel_existsUnique l E f n).exists.choose_spec
    ((coefficientSequenceEvaluation l E Y n).obj M) U
    (coefficientEvaluationSection l E Y M n (op U) x)
  unfold finiteEvaluation finiteSystemPullbackEvaluation integralFinitePullbackModel
  exact h₁.trans h₂.symm

private def strictLevel {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralComparisonSequencePullback l E f ⋙ coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n) ≅
      coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n ⋙
        scalarReductionRestriction l E X n :=
  Functor.isoWhiskerLeft (integralComparisonSequencePullback l E f)
      (restrictionEvaluation l E X n) ≪≫
    Functor.isoWhiskerRight (finiteEvaluation l E f n) (scalarReductionRestriction l E X n) ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
      (Functor.isoWhiskerRight (integralFinitePullbackModel l E f n).symm
        (scalarReductionRestriction l E X n))

private theorem strictLevel_generator {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E Y) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((strictLevel l E f n).hom.app M).val.app
        (op ((proEtaleBaseChange f).obj U))
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj M) n
          (op ((proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f M n U x)) =
      integralOperationsPullbackGenerator l E f n
        ((coefficientSequenceEvaluation l E Y n).obj M) U
        (coefficientEvaluationSection l E Y M n (op U) x) := by
  have hr := restrictionEvaluation_section l E
    ((integralComparisonSequencePullback l E f).obj M) n
    (op ((proEtaleBaseChange f).obj U)) (integralComparisonSequenceGenerator l E f M n U x)
  have hf := finiteEvaluation_unit l E f n M U x
  dsimp only [strictLevel, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [hr, hf]
  exact congrArg (fun a ↦ a.val.app (op ((proEtaleBaseChange f).obj U))
    (integralOperationsPullbackGenerator l E f n
      ((coefficientSequenceEvaluation l E Y n).obj M) U
      (coefficientEvaluationSection l E Y M n (op U) x)))
    ((integralFinitePullbackModel l E f n).hom_inv_id_app _)

attribute [local irreducible] strictLevel

private theorem strictLevel_zero {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n ⋙
      scalarReductionRestriction l E X n).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (strictLevel l E f n)

private theorem finiteEvaluation_zero {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Functor.PreservesZeroMorphisms (coefficientSequenceEvaluation l E Y n ⋙
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f) :=
  by infer_instance

/-- A strict comparison normalized on inverse-image generators equals the canonical
ordinary comparison followed by inverse image of the finite representative isomorphism.
Source: Stacks Tags 03D3, 099N(5), and 0941.
(blueprint: lem-pod-integral-pullback-strict-finite-generators).

Proof: restricted evaluation, finite system evaluation, and the inverse finite pullback
presentation comparison give the canonical ordinary comparison. Their defining unit
identities give its generator formula. Precompose the given comparison with its inverse.
The completed-to-finite projection is locally surjective, so restricted finite-module
maps remain finite-linear. The inverse-image adjunction makes equality of these maps
follow from their equality on unit generators. The hypothesis and naturality of the
adjunction unit give that equality degreewise. Cancel the canonical comparison. No
flatness, nonzero section, or positive-degree hypothesis is used. -/
private theorem strictComponent_generators {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
      ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj U))
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj (C.X i)) n
          (op ((proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
          (((κ n).hom.f i).val.app (op U)
            (coefficientEvaluationSection l E Y (C.X i) n (op U) x))) (n : ℕ) :
    letI := strictLevel_zero l E f n
    let R := scalarReductionRestriction l E X n
    let e := (NatIso.mapHomologicalComplex (strictLevel l E f n) (.up ℤ)).app C
    q.hom.app (op n) = e.hom ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map
          (κ n).hom) := by
  have := strictLevel_zero l E f n
  have := finiteEvaluation_zero l E f n
  let R := scalarReductionRestriction l E X n
  let B : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  let F := integralComparisonSequencePullback l E f
  let Pn := (unrestrictedIntegralFiniteComplex l E Y n).obj P
  let Cn := ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C
  let D := (F.mapHomologicalComplex (.up ℤ)).obj C
  let e := (NatIso.mapHomologicalComplex (strictLevel l E f n) (.up ℤ)).app C
  have he : e.inv ≫ q.hom.app (op n) =
      (R.mapHomologicalComplex (.up ℤ)).map
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex
          (.up ℤ)).map (κ n).hom) := by
    apply HomologicalComplex.hom_ext
    intro i
    apply pullbackLevel_hom_ext l E f n ((coefficientSequenceEvaluation l E Y n).obj (C.X i))
      ((integralOperationsLevelPullback l E f n).obj (Pn.X i))
    intro U x
    let z := integralComparisonSequenceSection l E Y (C.X i) n (op U) x
    have hz : coefficientEvaluationSection l E Y (C.X i) n (op U) z = x := by
      unfold z integralComparisonSequenceSection coefficientEvaluationSection
      exact abEqToHom_cancel (coefficientSequenceEvaluationAb_eq l E Y (C.X i) n (op U)) x
    have hi := strictLevel_generator l E f n (C.X i) U z
    rw [hz] at hi
    have hinv : ((strictLevel l E f n).inv.app (C.X i)).val.app
        (op ((proEtaleBaseChange f).obj U))
        (integralOperationsPullbackGenerator l E f n
          ((coefficientSequenceEvaluation l E Y n).obj (C.X i)) U x) =
      integralComparisonRestrictedSection l E X (F.obj (C.X i)) n
        (op ((proEtaleBaseChange f).obj U))
        (integralComparisonSequenceGenerator l E f (C.X i) n U z) := by
      apply iso_section_inv ((strictLevel l E f n).app (C.X i))
      exact hi
    change ((q.hom.app (op n)).f i).val.app _
        (((strictLevel l E f n).inv.app (C.X i)).val.app _
          (integralOperationsPullbackGenerator l E f n
          ((coefficientSequenceEvaluation l E Y n).obj (C.X i)) U x)) = _
    erw [hinv, hq, hz]
    exact congrArg (fun a ↦ a.val.app (op U) x)
      ((coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).unit.naturality
            ((κ n).hom.f i))
  have hq' : q.hom.app (op n) = e.hom ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex
          (.up ℤ)).map (κ n).hom) := by
    erw [← he, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  exact hq'

private theorem strictComponent_complex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
      ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj U))
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj (C.X i)) n
          (op ((proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
          (((κ n).hom.f i).val.app (op U)
            (coefficientEvaluationSection l E Y (C.X i) n (op U) x))) (n : ℕ) :
    letI := strictLevel_zero l E f n
    letI := finiteEvaluation_zero l E f n
    let R := scalarReductionRestriction l E X n
    let B : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
    let Pn := (unrestrictedIntegralFiniteComplex l E Y n).obj P
    let D := ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C
    let H : ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D ⟶
      (B.mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) :=
      (NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C
    let γ := NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n) (.up ℤ)
    let α : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        D).asFunctor.obj (op n) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj
          (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D) :=
      (NatTrans.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom (.up ℤ)).app D
    q.hom.app (op n) ≫ (R.mapHomologicalComplex (.up ℤ)).map (γ.hom.app Pn) =
      α ≫ (R.mapHomologicalComplex (.up ℤ)).map
        (H ≫ (B.mapHomologicalComplex (.up ℤ)).map (κ n).hom) := by
  have := strictLevel_zero l E f n
  have := finiteEvaluation_zero l E f n
  let R := scalarReductionRestriction l E X n
  let B : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  let F := integralComparisonSequencePullback l E f
  let Pn := (unrestrictedIntegralFiniteComplex l E Y n).obj P
  let Cn := ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C
  let D := (F.mapHomologicalComplex (.up ℤ)).obj C
  let e := (NatIso.mapHomologicalComplex (strictLevel l E f n) (.up ℤ)).app C
  have hq' := strictComponent_generators l E f P C κ q hq n
  let H : ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D ⟶
      (B.mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) :=
      (NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C
  let γ := NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n) (.up ℤ)
  let α : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        D).asFunctor.obj (op n) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj
          (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D) :=
      (NatTrans.mapHomologicalComplex
    (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom (.up ℤ)).app D
  have he_formula : e.hom = α ≫
      (R.mapHomologicalComplex (.up ℤ)).map H ≫
      (R.mapHomologicalComplex (.up ℤ)).map (γ.inv.app Cn) := by
    unfold e strictLevel restrictionEvaluation
    dsimp only [α, H, γ]
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have hγ : γ.inv.app Cn ≫
      ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map
        (κ n).hom ≫ γ.hom.app Pn =
      (B.mapHomologicalComplex (.up ℤ)).map (κ n).hom := by
    exact iso_conjugate γ (κ n).hom
  have hc : q.hom.app (op n) ≫ (R.mapHomologicalComplex (.up ℤ)).map (γ.hom.app Pn) =
      α ≫ (R.mapHomologicalComplex (.up ℤ)).map
        (H ≫ (B.mapHomologicalComplex (.up ℤ)).map (κ n).hom) := by
    exact mapped_square
      (M := ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Cn)
      (N := ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D)
      (P := ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Pn)
      (Q := (B.mapHomologicalComplex (.up ℤ)).obj Cn)
      (T := (B.mapHomologicalComplex (.up ℤ)).obj Pn)
      (R.mapHomologicalComplex (.up ℤ)) (q.hom.app (op n)) e.hom α H
      (γ.inv.app Cn)
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map
        (κ n).hom) (γ.hom.app Pn)
      ((B.mapHomologicalComplex (.up ℤ)).map (κ n).hom) hq' he_formula hγ
  exact hc

end Generators

section FiniteEvaluationFactors
attribute [local instance 30000] zeroOfFiniteLimits
attribute [local instance 50] additiveOfFiniteLimits
attribute [local instance]
  finitePullback_limits finitePullback_colimits nativeFinitePullback_limits
  nativeFinitePullback_colimits mixedFinitePullback_limits mixedFinitePullback_colimits
attribute [local irreducible] restrictionEvaluation finiteEvaluation strictLevel
attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits
attribute [local irreducible] coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

private theorem finiteEvaluation_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ) :
    (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) f n).hom.app (DerivedCategory.Q.obj C) ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C) ≫
      (proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) =
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
      (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C) := by
  have hfac := Functor.exactSquare_fac (finiteEvaluation l E f n) C
  have hb : finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n =
      Functor.mapDerivedCategorySquareIso (finiteEvaluation l E f n) := by
    unfold finiteSystemDerivedPullbackEvaluation finiteEvaluation
    rfl
  erw [← hb] at hfac
  exact hfac


/-- The derived finite evaluation comparison, followed by an arbitrary map of finite
complexes, is computed by the ordinary evaluation comparison and the exact factors.
Source: Stacks Tag 015F; exact localization composition and naturality.
(blueprint: lem-pod-integral-pullback-finite-evaluation-factors).

Proof: the derived finite evaluation comparison is the composition of the inverse
factorization compositor, the derived ordinary evaluation isomorphism, and the other
compositor. Their factorization identities compute its value on Q(C). Naturality of
the finite pullback factor moves Q(k) across that factor. The inverse and forward
sequence pullback factors cancel, leaving Q of the ordinary comparison followed by
finite pullback of k. The argument applies to every finite target complex and every
chain map k, including zero maps, and uses neither a resolution nor flatness. -/
private theorem finiteEvaluation_fac_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ)
    (N : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (k : ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ⟶ N) :
  letI := finiteEvaluation_zero l E f n
  let B : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  let V := coefficientSequenceEvaluation l E X n
  let F := integralComparisonSequencePullback l E f
  let D := (F.mapHomologicalComplex (.up ℤ)).obj C
  let H : (V.mapHomologicalComplex (.up ℤ)).obj D ⟶
      (B.mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) :=
      (NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C
  let VD := coefficientSequenceDerivedEvaluation l E X n
  let BD := proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let β : F.mapDerivedCategory ⋙ VD ≅
      (coefficientSequenceEvaluation l E Y n).mapDerivedCategory ⋙ BD :=
    finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n
  VD.map (F.mapDerivedCategoryFactors.inv.app C) ≫
    β.hom.app (DerivedCategory.Q.obj C) ≫
    BD.map ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
      DerivedCategory.Q.map k) ≫ B.mapDerivedCategoryFactors.hom.app N =
  V.mapDerivedCategoryFactors.hom.app D ≫
    DerivedCategory.Q.map (H ≫ (B.mapHomologicalComplex (.up ℤ)).map k) := by
  have := finiteEvaluation_zero l E f n
  let B : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  let V := coefficientSequenceEvaluation l E X n
  let F := integralComparisonSequencePullback l E f
  let D := (F.mapHomologicalComplex (.up ℤ)).obj C
  let H : (V.mapHomologicalComplex (.up ℤ)).obj D ⟶
      (B.mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) :=
      (NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C
  let VD := coefficientSequenceDerivedEvaluation l E X n
  let BD := proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let β : F.mapDerivedCategory ⋙ VD ≅
      (coefficientSequenceEvaluation l E Y n).mapDerivedCategory ⋙ BD :=
    finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n
  have hfac := Functor.exactSquare_fac (finiteEvaluation l E f n) C
  have hβ : finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n =
      Functor.mapDerivedCategorySquareIso (finiteEvaluation l E f n) := by
    unfold finiteSystemDerivedPullbackEvaluation finiteEvaluation
    rfl
  erw [← hβ] at hfac
  dsimp only [BD, proEtaleConstantRingDerivedPullback]
  simp only [Functor.map_comp, Category.assoc]
  erw [B.mapDerivedCategoryFactors.hom.naturality k]
  erw [reassoc_of% hfac]
  dsimp only [Functor.comp_map]
  change VD.map (F.mapDerivedCategoryFactors.inv.app C) ≫
    VD.map (F.mapDerivedCategoryFactors.hom.app C) ≫
    V.mapDerivedCategoryFactors.hom.app D ≫ DerivedCategory.Q.map H ≫
    DerivedCategory.Q.map ((B.mapHomologicalComplex (.up ℤ)).map k) = _
  rw [← VD.map_comp_assoc, Iso.inv_hom_id_app, VD.map_id, Category.id_comp]

end FiniteEvaluationFactors

section Proof
attribute [local instance 30000] zeroOfFiniteLimits
attribute [local instance 50] additiveOfFiniteLimits
attribute [local instance]
  finitePullback_limits finitePullback_colimits nativeFinitePullback_limits
  nativeFinitePullback_colimits mixedFinitePullback_limits mixedFinitePullback_colimits
attribute [local irreducible] restrictionEvaluation finiteEvaluation strictLevel
attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits
attribute [local irreducible] coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

private theorem restrictedFactors_fac (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (integralComparisonRestrictedEvaluationFactors l E W C n).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom
            (.up ℤ)).app C) =
      (coefficientFiniteDerivedRestriction l E W n).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) := by
  have h := Functor.exactSquare_fac
    (R := coefficientSequenceRestriction l E W)
    (G := (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (L := coefficientSequenceEvaluation l E W n) (S := scalarReductionRestriction l E W n)
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) C
  change (coefficientRestrictedEvaluationIso l E W n).hom.app
      (DerivedCategory.Q.obj C) ≫ _ = _ at h
  unfold integralComparisonRestrictedEvaluationFactors
  change ((coefficientRestrictedEvaluationIso l E W n).inv.app (DerivedCategory.Q.obj C) ≫
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategory.map
        ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app C) ≫
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategoryFactors.hom.app
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app C) = _
  simp only [Category.assoc]
  rw [← h]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem restrictedFactors_square (W : Scheme.{u}) (n : ℕ)
    (D : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (A T : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (q : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
      D).asFunctor.obj (op n) ⟶
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj A)
    (b : A ⟶ T)
    (c : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ⟶ T)
    (h : q ≫ ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map b =
      (NatTrans.mapHomologicalComplex
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app D ≫
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map c) :
    (integralComparisonRestrictedEvaluationFactors l E W D n).hom ≫
      DerivedCategory.Q.map q ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app A ≫
      (coefficientFiniteDerivedRestriction l E W n).map (DerivedCategory.Q.map b) ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app T =
    (coefficientFiniteDerivedRestriction l E W n).map
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app D) ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D) ≫
      DerivedCategory.Q.map
        (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map c) := by
  erw [(scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.naturality b]
  erw [Iso.inv_hom_id_app_assoc]
  dsimp only [Functor.comp_map]
  erw [← DerivedCategory.Q.map_comp, h, DerivedCategory.Q.map_comp]
  erw [← Category.assoc, restrictedFactors_fac l E W D n]
  simp only [Category.assoc]

private theorem map_iso_cancel_assoc {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y Z : A} (f : X ⟶ Y) (e : Z ≅ Y)
    {T : B} (h : F.obj Y ⟶ T) :
    F.map (f ≫ e.inv) ≫ F.map e.hom ≫ h = F.map f ≫ h := by
  rw [← F.map_comp_assoc, Category.assoc, e.inv_hom_id, Category.comp_id]

end Proof

attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local irreducible] strictLevel restrictionEvaluation finiteEvaluation
  coefficientSequenceRestriction completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

/-- The finite component of a strict tower comparison is fixed by its values on
inverse-image unit generators. This is a statement about the strict comparison q;
it has no integral realization or reduction/limit counit as an input.
Source: Stacks 03D3 (inverse-image adjunction), 099N(5), and 0941;
step 1 of lem-pod-integral-pullback-counit-projection.
(blueprint: lem-pod-integral-pullback-strict-finite-component).

Proof: evaluate the system inverse-image unit at level n. The defining property of
finiteSystemPullbackEvaluation identifies it with the ordinary finite inverse-image
unit. The defining property of integralFinitePullbackModel identifies the other
presentation with this same unit. After transporting by kappa, the hypothesis says
that both maps have the same values on these unit sections. The completed-to-finite
coefficient projection is locally surjective; thus completed-linear maps between
these restricted quotient modules are already quotient-linear. The inverse-image
adjunction, or equivalently its locally generating unit sections and scalar multiples,
therefore makes the two maps equal in every degree. The degreewise equalities commute
with the differentials. Apply Q, and use the exact-functor factorization comparisons
for restriction, evaluation and inverse image. This gives precisely the displayed
identity. The proof uses no flatness of a transition map, no effectivity, and no
invertibility of a derived reduction counit. It also covers zero complexes, empty
schemes, and n=0, where the coefficient exponent is one. -/
theorem integralPullbackStrictFiniteComponent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
      ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj U))
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj (C.X i)) n
          (op ((proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
          (((κ n).hom.f i).val.app (op U)
            (coefficientEvaluationSection l E Y (C.X i) n (op U) x))) (n : ℕ) :
    (integralComparisonRestrictedEvaluationFactors l E X
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C)
      n).hom ≫
      DerivedCategory.Q.map (q.hom.app (op n)) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj
          ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
            (.up ℤ)).hom.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) ≫
          (proEtaleConstantRingPullback
            (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.inv.app
            ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) =
    (coefficientFiniteDerivedRestriction l E X n).map
      ((coefficientSequenceDerivedEvaluation l E X n).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.inv.app C) ≫
        (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) f n).hom.app (DerivedCategory.Q.obj C) ≫
        (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
            DerivedCategory.Q.map (κ n).hom)) := by
  have := finiteEvaluation_zero l E f n
  let R := scalarReductionRestriction l E X n
  let B := proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  let V := coefficientSequenceEvaluation l E X n
  let F := integralComparisonSequencePullback l E f
  let Pn := (unrestrictedIntegralFiniteComplex l E Y n).obj P
  let D := (F.mapHomologicalComplex (.up ℤ)).obj C
  let qn : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        D).asFunctor.obj (op n) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj
          (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Pn) :=
      q.hom.app (op n)
  let H : ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D ⟶
      (B.mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) :=
      (NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C
  let γ := NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n) (.up ℤ)
  have hc := strictComponent_complex l E f P C κ q hq n
  let RD := coefficientFiniteDerivedRestriction l E X n
  let VD := coefficientSequenceDerivedEvaluation l E X n
  let BD := proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let β : F.mapDerivedCategory ⋙ VD ≅
      (coefficientSequenceEvaluation l E Y n).mapDerivedCategory ⋙ BD :=
    finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n
  have hfinite := finiteEvaluation_fac_comp l E f C n Pn (κ n).hom
  have hl :
      (integralComparisonRestrictedEvaluationFactors l E X D n).hom ≫
        DerivedCategory.Q.map qn ≫
        R.mapDerivedCategoryFactors.inv.app
          (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Pn) ≫
        RD.map (DerivedCategory.Q.map (γ.hom.app Pn) ≫
          B.mapDerivedCategoryFactors.inv.app Pn) ≫
        RD.map (B.mapDerivedCategoryFactors.hom.app Pn) ≫
        R.mapDerivedCategoryFactors.hom.app
          ((B.mapHomologicalComplex (.up ℤ)).obj Pn) =
      RD.map (V.mapDerivedCategoryFactors.hom.app D) ≫
        R.mapDerivedCategoryFactors.hom.app
          ((V.mapHomologicalComplex (.up ℤ)).obj D) ≫
        DerivedCategory.Q.map
          ((R.mapHomologicalComplex (.up ℤ)).map
            (H ≫ (B.mapHomologicalComplex (.up ℤ)).map (κ n).hom)) := by
    erw [map_iso_cancel_assoc RD (DerivedCategory.Q.map (γ.hom.app Pn))
      (B.mapDerivedCategoryFactors.app Pn)]
    exact restrictedFactors_square l E X n D
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Pn)
      ((B.mapHomologicalComplex (.up ℤ)).obj Pn) qn (γ.hom.app Pn)
      (H ≫ (B.mapHomologicalComplex (.up ℤ)).map (κ n).hom) hc
  apply (cancel_mono (RD.map (B.mapDerivedCategoryFactors.hom.app Pn) ≫
    R.mapDerivedCategoryFactors.hom.app ((B.mapHomologicalComplex (.up ℤ)).obj Pn))).1
  change ((integralComparisonRestrictedEvaluationFactors l E X D n).hom ≫
    DerivedCategory.Q.map qn ≫
    R.mapDerivedCategoryFactors.inv.app
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Pn) ≫
    RD.map (DerivedCategory.Q.map (γ.hom.app Pn) ≫ B.mapDerivedCategoryFactors.inv.app Pn)) ≫
    (RD.map (B.mapDerivedCategoryFactors.hom.app Pn) ≫
      R.mapDerivedCategoryFactors.hom.app ((B.mapHomologicalComplex (.up ℤ)).obj Pn)) =
    RD.map (VD.map (F.mapDerivedCategoryFactors.inv.app C) ≫
      β.hom.app (DerivedCategory.Q.obj C) ≫
      BD.map ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map (κ n).hom)) ≫
      (RD.map (B.mapDerivedCategoryFactors.hom.app Pn) ≫
        R.mapDerivedCategoryFactors.hom.app ((B.mapHomologicalComplex (.up ℤ)).obj Pn))
  simp only [Category.assoc]
  erw [hl]
  erw [← RD.map_comp_assoc]
  simp only [Category.assoc]
  erw [hfinite]
  rw [RD.map_comp]
  simp only [Category.assoc]
  have hn := R.mapDerivedCategoryFactors.hom.naturality
    (H ≫ (B.mapHomologicalComplex (.up ℤ)).map (κ n).hom)
  dsimp only [Functor.comp_map] at hn
  erw [hn]

end WeilConjectures
