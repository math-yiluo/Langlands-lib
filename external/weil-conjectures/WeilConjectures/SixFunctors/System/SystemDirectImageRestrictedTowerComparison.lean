/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeDirectTransition
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SixFunctors.Compact.CompactSupportInputTowerCompatibility
import all WeilConjectures.SmoothPurity.Sf.SfDirectImageRestrictionPasting
import all WeilConjectures.SmoothPurity.Sf.SfDirectImageTransitionPresentation

/-! # The restricted tower of the actual system direct image

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Tag 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.IntegralPresentation
namespace WeilConjectures

section TowerComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] HasDerivedCategory.standard

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard constantSheaf sfCompletedModuleDirectImage
  Functor.ofSequence Functor.ofOpSequence presheafToSheaf Functor.leftAdjoint
  MorphismProperty.Over.pullback
  completedIntegralCoefficientSheafUnrestricted
  scalarReductionDerivedExtension scalarReductionExistence scalarReductionDerivedExistence
  compactSupportNativeDirectEvaluation

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  integralCoefficientSheafTransition compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  coefficientConstantTowerEvaluation scalarReductionDerivedRestriction
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  compactSupportLevelSheafQuotient
  NatTrans.mapHomologicalComplex HomologicalComplex.asFunctor
  SemilinearSections.evaluation SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

attribute [local implicit_reducible] ProEtale.lowerStar
  coefficientFiniteDerivedRestriction coefficientFiniteDerivedExtension

set_option linter.style.haveILetI false

attribute [local semireducible] Functor.ofSequence Functor.ofOpSequence

private def actualNativeDirectIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralComparisonSequenceDirectImage l E f ≅
      ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f := by
  apply SheafOfModules.pushforwardCongr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  dsimp only [integralComparisonSequenceRingMap,
    integralComparisonSequenceRingComponent, Functor.whiskerRight_app,
    ProEtale.VaryingRing.ringMap, ProEtale.VaryingRing.ringMapApp]
  congr 1

private theorem directRestriction_eq (W : Scheme.{u}) (n : ℕ) :
    proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E (n + 1) n n.le_succ) ⋙
      scalarReductionRestriction l E W (n + 1) = scalarReductionRestriction l E W n :=
  (congrArg (fun F ↦ F ⋙ scalarReductionRestriction l E W (n + 1))
    (compactSupportModuleRes_eq l E W n.le_succ)).symm.trans
      (coefficientRestrictionComp l E W n.le_succ)

private theorem directRestrictionComp_eq (W : Scheme.{u}) (n : ℕ) :
    compactSupportRestrictionComp l E W (n + 1) n n.le_succ =
      (Functor.mapDerivedCategoryCompIso
        (proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E (n + 1) n n.le_succ))
        (scalarReductionRestriction l E W (n + 1))) ≪≫
      Functor.mapDerivedCategoryNatIso (eqToIso (directRestriction_eq l E W n)) := by
  unfold compactSupportRestrictionComp pbcDerivedRestrictComp
  have h := scalarComp_eqToIso
    (completedIntegralCommRingProjectionUnrestricted l E W (n + 1))
    (compactSupportLevelSheafQuotient l E W (n + 1) n n.le_succ)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (compactSupportProjection_comp l E W (n + 1) n n.le_succ)
    (directRestriction_eq l E W n)
  rw [h]
  rfl

set_option linter.defProp false in
private def directDerivedBase {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  letI := proEtaleConstantModuleDirectImage_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  letI := proEtaleConstantModuleDirectImage_additive f
    (Padic.coefficientExtensionRing l E (n + 2))
  let q := compactSupportLevelQuotient l E (n + 1) n n.le_succ
  letI : Abelian.HasKInjectiveResolutions (scalarReductionTarget l E X n) :=
    proEtaleRingModules_hasKInjectiveResolutions X (integralCoefficientCommRingSheaf l E X n)
  letI : Abelian.HasKInjectiveResolutions (scalarReductionTarget l E X (n + 1)) :=
    proEtaleRingModules_hasKInjectiveResolutions X
      (integralCoefficientCommRingSheaf l E X (n + 1))
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits X q
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits X q
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits Y q
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits Y q
  letI := sfRestrictionLimits l E X n
  letI := sfRestrictionColimits l E X n
  letI := sfRestrictionLimits l E Y n
  letI := sfRestrictionColimits l E Y n
  letI := sfRestrictionLimits l E X (n + 1)
  letI := sfRestrictionColimits l E X (n + 1)
  letI := sfRestrictionLimits l E Y (n + 1)
  letI := sfRestrictionColimits l E Y (n + 1)
  let Fn := proEtaleConstantModuleDirectImage f
    (Padic.coefficientExtensionRing l E (n + 1))
  let Fm := proEtaleConstantModuleDirectImage f
    (Padic.coefficientExtensionRing l E (n + 2))
  let G := sfCompletedModuleDirectImage l E f
  let PX := scalarReductionRestriction l E X n
  let PY := scalarReductionRestriction l E Y n
  let QX := scalarReductionRestriction l E X (n + 1)
  let QY := scalarReductionRestriction l E Y (n + 1)
  let RX := proEtaleCoefficientRestrictScalars X q
  let RY := proEtaleCoefficientRestrictScalars Y q
  sheafDerivedTriangle
    (C0 := scalarReductionTarget l E X n)
    (C1 := scalarReductionTarget l E X (n + 1))
    (C2 := scalarReductionSource l E X)
    (D := Y.ProEt) (J := ProEt.topology Y)
    (S0 := integralCoefficientSheaf l E Y n)
    (S1 := integralCoefficientSheaf l E Y (n + 1))
    Fn Fm G PX RX QX PY RY QY

set_option linter.defProp false in
private def directPastingHead {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  let q := compactSupportLevelQuotient l E (n + 1) n n.le_succ
  directDerivedBase l E f n
    (directRestriction_eq l E X n) (directRestriction_eq l E Y n)
    (proEtaleCoefficientDirectImageComparison f q).symm
    (sfDirectImageRestrictionComparison l E f n)
    (sfDirectImageRestrictionComparison l E f (n + 1))
    (sfDerivedRestrictionComparison l E f (n + 1))
    (sfDerivedRestrictionComparison l E f n) (sfDerivedImageRestriction f q)

set_option linter.defProp false in
private def directPastingCompletedNormalized {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  directPastingHead l E f n
    (sfDerivedRestrictionComparison_existsUnique l E f (n + 1)).exists.choose_spec
    (sfDerivedRestrictionComparison_existsUnique l E f n).exists.choose_spec

set_option linter.defProp false in
private def directPastingFiniteNormalized {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  let q := compactSupportLevelQuotient l E (n + 1) n n.le_succ
  directPastingCompletedNormalized l E f n
    (by
      intro J hJ I hI r hr
      exact ((proEtaleDerivedDirectImage_restrictScalars f q).choose_spec J I r).2)

set_option linter.defProp false in
private def directPastingRestrictionSections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  directPastingFiniteNormalized l E f n (scalarRestriction_identity l E Y (n + 1))

private theorem inverseDirectSections
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (q : A →+* B)
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) (U : Y.ProEtᵒᵖ)
    (x : ((proEtaleCoefficientRestrictScalars X q ⋙
      proEtaleConstantModuleDirectImage f A).obj M).val.obj U) :
    HEq (((proEtaleCoefficientDirectImageComparison f q).inv.app M).val.app U x) x := by
  exact inverseSection ((proEtaleCoefficientDirectImageComparison f q).app M)
    (fun U x ↦ heq_of_eq
      ((proEtaleCoefficientDirectImageComparison_existsUnique f q).choose_spec.1 M U x)) U x

set_option linter.defProp false in
private def directPastingFiniteSections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  directPastingRestrictionSections l E f n
    (inverseDirectSections f (compactSupportLevelQuotient l E (n + 1) n n.le_succ))

set_option linter.defProp false in
private def completeDirectPasting {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  directPastingFiniteSections l E f n
    (completedComparison_identity l E f n)
    (completedComparison_identity l E f (n + 1))

private theorem directPasting {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (B : DerivedCategory (scalarReductionTarget l E X n)) :
    (sfDerivedRestrictionComparison l E f (n + 1)).hom.app
        ((proEtaleCoefficientRestrictScalars X
          (compactSupportLevelQuotient l E (n + 1) n n.le_succ)).mapDerivedCategory.obj B) ≫
      (scalarReductionDerivedRestriction l E Y (n + 1)).map
        ((sfDerivedImageRestriction f
          (compactSupportLevelQuotient l E (n + 1) n n.le_succ)).hom.app B) ≫
      (compactSupportRestrictionComp l E Y (n + 1) n n.le_succ).hom.app
        ((proEtaleConstantDerivedDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))).obj B) =
    (sfCompletedDerivedDirectImage l E f).map
        ((compactSupportRestrictionComp l E X (n + 1) n n.le_succ).hom.app B) ≫
      (sfDerivedRestrictionComparison l E f n).hom.app B := by
  have h := completeDirectPasting l E f n B
  rw [← directRestrictionComp_eq l E X n, ← directRestrictionComp_eq l E Y n] at h
  exact h

private theorem directPresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    sfDirectImageTransition l E f K n =
      (scalarReductionDerivedRestriction l E Y (n + 1)).map
        ((proEtaleConstantDerivedDirectImage f
          (Padic.coefficientExtensionRing l E (n + 2))).map
          (compactSupportReductionMap l E X (n + 1) n n.le_succ K) ≫
        (sfDerivedImageRestriction f
          (compactSupportLevelQuotient l E (n + 1) n n.le_succ)).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K)) ≫
      (compactSupportRestrictionComp l E Y (n + 1) n n.le_succ).hom.app
        (sfFiniteDerivedDirectImage l E f K n) := by
  have h := presentationOfPasting
    (scalarReductionDerivedRestriction l E X (n + 1))
    (scalarReductionDerivedRestriction l E X n)
    (proEtaleCoefficientRestrictScalars X
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ)).mapDerivedCategory
    (proEtaleCoefficientRestrictScalars Y
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ)).mapDerivedCategory
    (proEtaleConstantDerivedDirectImage f
      (Padic.coefficientExtensionRing l E (n + 2)))
    (proEtaleConstantDerivedDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1)))
    (scalarReductionDerivedRestriction l E Y (n + 1))
    (scalarReductionDerivedRestriction l E Y n)
    (sfCompletedDerivedDirectImage l E f)
    (compactSupportRestrictionComp l E X (n + 1) n n.le_succ)
    (compactSupportRestrictionComp l E Y (n + 1) n n.le_succ)
    (sfDerivedImageRestriction f (compactSupportLevelQuotient l E (n + 1) n n.le_succ))
    (sfDerivedRestrictionComparison l E f (n + 1))
    (sfDerivedRestrictionComparison l E f n)
    ((scalarReductionDerivedExtension l E X (n + 1)).obj K)
    ((scalarReductionDerivedExtension l E X n).obj K)
    (compactSupportReductionMap l E X (n + 1) n n.le_succ K)
    ((sfDerivedReductionTransition l E X n).app K)
    (inputAdjacent l E X K n) (directPasting l E f n _)
  exact h

private def representativeTowerIso (W : Scheme.{u})
    (T : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (M : coefficientSequenceRestrictedDerived l E W)
    (e : DerivedCategory.Q.obj T ≅ M) :
    T.asFunctor ⋙ DerivedCategory.Q ≅ inputNativeTower l E W M := by
  let b (n : ℕ) :=
    (coefficientConstantTowerEvaluationFactors l E W n).app T |>.symm
  let c (n : ℕ) := b n ≪≫
    (coefficientConstantTowerEvaluation l E W n).mapIso e
  let α : T.asFunctor ⋙ DerivedCategory.Q ⟶ inputNativeTower l E W M :=
    NatTrans.ofOpSequence (fun n ↦ (c n).hom) (by
      intro n
      have h := towerTransition_fac l E W (n + 1) n n.le_succ T
      change (pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W)
          (n + 1) n n.le_succ).app (DerivedCategory.Q.obj T) ≫
          (coefficientConstantTowerEvaluationFactors l E W n).hom.app T =
        (coefficientConstantTowerEvaluationFactors l E W (n + 1)).hom.app T ≫
          DerivedCategory.Q.map (T.asFunctor.map (homOfLE n.le_succ).op) at h
      have hn := (pbcTowerTransition W
        (completedIntegralCommRingSheafUnrestricted l E W) (n + 1) n n.le_succ).naturality
          e.hom
      dsimp only [c, b, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
      dsimp only [inputNativeTower]
      have hf : DerivedCategory.Q.map (T.asFunctor.map (homOfLE n.le_succ).op) ≫
          (coefficientConstantTowerEvaluationFactors l E W n).inv.app T =
        (coefficientConstantTowerEvaluationFactors l E W (n + 1)).inv.app T ≫
          (pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W)
            (n + 1) n n.le_succ).app (DerivedCategory.Q.obj T) := by
        apply (cancel_epi
          ((coefficientConstantTowerEvaluationFactors l E W (n + 1)).hom.app T)).1
        apply (cancel_mono
          ((coefficientConstantTowerEvaluationFactors l E W n).hom.app T)).1
        simp only [Category.assoc, Iso.inv_hom_id_app,
          Iso.hom_inv_id_app_assoc]
        erw [Category.comp_id]
        exact h.symm
      simp only [Category.assoc]
      erw [hn]
      simpa only [Category.assoc, Functor.comp_map, coefficientConstantTowerEvaluation]
        using congrArg (fun z ↦ z ≫
          (coefficientConstantTowerEvaluation l E W n).map e.hom) hf)
  haveI : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso (c n.unop).hom
    infer_instance
  letI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

private def nativeTowerIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    inputNativeTower l E Y ((coefficientSequenceDerivedRestriction l E Y).obj
      ((ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f).obj (S.reduction.obj K))) ≅
      Functor.ofOpSequence (sfDirectImageTransition l E f K) := by
  let M := S.reduction.obj K
  let N : coefficientSequenceDerived l E Y :=
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f).obj M
  let U := (coefficientSequenceDerivedRestriction l E Y).obj N
  let A := inputNativeTower l E Y U
  let b (n : ℕ) : (coefficientSequenceDerivedEvaluation l E Y n).obj N ≅
      sfFiniteDerivedDirectImage l E f K n :=
    (compactSupportNativeDirectEvaluation l E f n).app M ≪≫
    (proEtaleConstantDerivedDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))).mapIso
      ((S.reductionEvaluation n).app K)
  let c (n : ℕ) : A.obj (op n) ≅ sfDirectImageTerm l E f K n :=
    (coefficientRestrictedEvaluationIso l E Y n).app N ≪≫
      (scalarReductionDerivedRestriction l E Y n).mapIso (b n)
  have hb (n : ℕ) :
      (compactSupportCoefficientTransition l E Y n.le_succ).app N ≫
        (proEtaleCoefficientRestrictScalars Y
          (compactSupportLevelQuotient l E (n + 1) n n.le_succ)).mapDerivedCategory.map
          (b n).hom =
      (b (n + 1)).hom ≫
        (proEtaleConstantDerivedDirectImage f
          (Padic.coefficientExtensionRing l E (n + 2))).map
          (compactSupportReductionMap l E X (n + 1) n n.le_succ K) ≫
        (sfDerivedImageRestriction f
          (compactSupportLevelQuotient l E (n + 1) n n.le_succ)).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K) := by
    have ht := compactSupportNativeDirectTransition l E f n.le_succ M
    have hd := compactSupportReductionTransition l E X
      S.toCoefficientDerivedSystemReduction n.le_succ K
    have hn := (sfDerivedImageRestriction f
      (compactSupportLevelQuotient l E (n + 1) n n.le_succ)).hom.naturality
      ((S.reductionEvaluation n).hom.app K)
    dsimp only [Functor.comp_map] at hn
    dsimp only [b, Iso.trans_hom, Iso.app_hom, Functor.mapIso]
    rw [Functor.map_comp]
    erw [reassoc_of% ht]
    erw [← hn]
    rw [← Functor.map_comp_assoc, hd, Functor.map_comp]
    simp only [Category.assoc]
    rfl
  have hc (n : ℕ) : A.map (homOfLE n.le_succ).op ≫ (c n).hom =
      (c (n + 1)).hom ≫ sfDirectImageTransition l E f K n := by
    have ht := compactSupportCoefficientTransition_restricted l E Y n.le_succ N
    have hn := (compactSupportRestrictionComp l E Y (n + 1) n n.le_succ).hom.naturality
      (b n).hom
    dsimp only [Functor.comp_map] at hn
    dsimp only [c, A, U, inputNativeTower, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso]
    erw [reassoc_of% ht]
    erw [← hn]
    rw [← Functor.map_comp_assoc, hb, Functor.map_comp, Functor.map_comp]
    rw [directPresentation l E f K n]
    simp only [Category.assoc, Functor.map_comp]
  let α : A ⟶ Functor.ofOpSequence (sfDirectImageTransition l E f K) :=
    NatTrans.ofOpSequence (fun n ↦ (c n).hom) (by
      intro n
      change A.map (homOfLE n.le_succ).op ≫ (c n).hom = _
      simpa only [Functor.ofOpSequence_map_homOfLE_succ] using hc n)
  haveI : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso (c n.unop).hom
    infer_instance
  letI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- A representing complex of the restricted system direct image evaluates to the
finite-image tower, including its actual adjacent arrows. This comparison contains
no inverse-limit object, product, projection or distinguished-triangle assertion.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Tags 0D6E and 06YY.
(blueprint: stage3-weil-system-direct-image-restricted-tower-comparison).

Proof: choose a flat-term K-flat complex P representing K. The reductionModel field
of S supplies a strict quotient complex C and its simultaneous finite comparisons;
its transition equation identifies the quotient arrows with ordinary scalar reduction.
Resolve C once by a K-injective system J and apply the sequence direct image to J.
The ordinary evaluation/direct-image square is identity on sections. Derived
ringed-topos composition identifies its finite evaluations with the corresponding
finite derived direct images; its resolution normalization retains the same arrows.
Restrict to completed coefficients. On P, the quotient arrow is the map sending
s tensor x to rho(s) tensor x, hence is sfDerivedReductionTransition by its unique
representative characterization. The restriction/direct-image square is the
section-normalized sfDerivedRestrictionComparison, so transporting this arrow gives
exactly sfDirectImageTransition. These identifications yield an isomorphism of the
whole evaluated tower of this representative with Functor.ofOpSequence of those
arrows. Exact evaluation sends quasi-isomorphisms of strict towers to objectwise
isomorphisms after localization. Localization's factorization of simultaneous
evaluation therefore transports the comparison along e to any representing T.
This uses no boundedness, constructibility, completeness, or geometric hypothesis;
it applies also to zero complexes and empty schemes. -/
theorem systemDirectImage_restrictedTowerComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (T : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ)
    (e : DerivedCategory.Q.obj T ≅ (coefficientSequenceDerivedRestriction l E Y).obj
      ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
        (S.reduction.obj K))) :
    Nonempty (T.asFunctor ⋙ DerivedCategory.Q ≅
      Functor.ofOpSequence (sfDirectImageTransition l E f K)) := by
  let G : coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E Y :=
    ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f
  letI : G.Additive :=
    ProEtale.VaryingRing.push_additive (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f
  let a := Functor.rightDerivedFunctorNatIso
    (G := G) (actualNativeDirectIso l E f)
  let ee := e ≪≫ (coefficientSequenceDerivedRestriction l E Y).mapIso
    (a.app (S.reduction.obj K))
  exact ⟨representativeTowerIso l E Y T _ ee ≪≫ nativeTowerIso l E f S K⟩

end TowerComparison

end WeilConjectures
