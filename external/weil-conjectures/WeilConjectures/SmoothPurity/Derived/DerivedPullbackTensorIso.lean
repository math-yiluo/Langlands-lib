/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationBilinearComparison
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackTensorNaturality
import WeilConjectures.SmoothPurity.Rational.RationalPullbackTensorAssociatorNaturality
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCompositionCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorUnitCoherence

/-! # Derived pullback and derived tensor comparison

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso).

## Main definitions

* The four `canonical*PullbackTensor` families are the prescribed comparisons.
* The higher coherence predicates state equations on those same comparisons.

## Main statements

* `derivedPullbackTensorIso` packages naturality and the higher compatibilities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.privateModule false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v r

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Preserve the cached additive-group data while comparing stage Hom types.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

-- Match the category-wrapper proof context used by DerivedPullbackTensorHom.
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  integralCoefficientLinear integralScalarConstant sfIntegralCoefficientLinear
  sfIntegralConstructibleLinear
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  commonStageTensorComparison commonStagePullbackComparison
  operationStageTransitionIso commonStageDerivedTensor commonStageDerivedPullback

section HigherCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

attribute [local irreducible] pullbackTensorIntegralComposition
  pullbackTensorRationalComposition pullbackTensorCommonComposition

attribute [local irreducible] pullbackTensorIntegralReductionTensor
  pullbackTensorIntegralReductionPullback

attribute [local irreducible] pullbackTensorCommonLeft pullbackTensorCommonRight

attribute [local irreducible] pullbackTensorCommonAssociator

attribute [local irreducible] pullbackTensorIntegralUnitReduction

set_option allowUnsafeReducibility true in
attribute [local irreducible] instCategoryDerivedCategory DerivedCategory.instPreadditive
  SheafOfModules.instAbelian SheafOfModules.instCategory

attribute [local irreducible] pullbackTensorIntegralUnit pullbackTensorRationalUnit
  pullbackTensorIntegralLeftUnitor pullbackTensorIntegralRightUnitor
  pullbackTensorRationalLeftUnitor pullbackTensorRationalRightUnitor

attribute [local irreducible] pullbackTensorCommonUnitStage pullbackTensorCommonUnit

attribute [local irreducible] pullbackTensorIntegralAssociator
  pullbackTensorRationalAssociator canonicalIntegralPullbackTensor

section AssociativityNaturality

attribute [local irreducible] sfIntegralConstructible Linear.homModule Preadditive.homGroup

private theorem integralComparison_natural {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {M M' N N' : sfIntegralConstructibleCategory l E Y} (a : M ⟶ M') (b : N ⟶ N') :
    (constructibleIntegralPullback l E f).map
        ((constructibleIntegralTensor l E Y).map (Prod.mkHom a b)) ≫
        (canonicalIntegralPullbackTensor l E f M' N').hom =
      (canonicalIntegralPullbackTensor l E f M N).hom ≫
        (constructibleIntegralTensor l E X).map
          (Prod.mkHom ((constructibleIntegralPullback l E f).map a)
            ((constructibleIntegralPullback l E f).map b)) := by
  have := (coherentReduction_fullyFaithful l E X).2
  exact reducedComparison_natural (coherentReduction l E Y) (coherentReduction l E X)
    (constructibleIntegralPullback l E f) (pullbackTensorSequenceDerived l E f)
    (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
    (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (reduction_tensor l E Y) (reduction_tensor l E X) (reduction_pullback l E f)
    (pullbackTensorSystemComparison l E f) (canonicalIntegralPullbackTensor l E f)
    (integralComparison_reduction l E f) a b

private def integralComparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralTensor l E Y ⋙ constructibleIntegralPullback l E f ≅
      (constructibleIntegralPullback l E f).prod (constructibleIntegralPullback l E f) ⋙
        constructibleIntegralTensor l E X :=
  NatIso.ofComponents (fun MN ↦ canonicalIntegralPullbackTensor l E f MN.1 MN.2)
    (fun a ↦ integralComparison_natural l E f a.1 a.2)

private theorem rationalComparisonIso_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! e : rationalDerivedTensor l E Y ⋙ rationalDerivedPullback l E f ≅
        (rationalDerivedPullback l E f).prod (rationalDerivedPullback l E f) ⋙
          rationalDerivedTensor l E X,
      ∀ MN : sfRationalConstructibleCategory l E Y × sfRationalConstructibleCategory l E Y,
        HEq (e.app MN).hom ((sfRationalConstructibleLocalization l E X).map
          (canonicalIntegralPullbackTensor l E f MN.1.obj MN.2.obj).hom) := by
  have : (rationalDerivedPullback l E f).Additive := by
    simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
  exact (OperationsScalarLocalization.bilinearComparison_existsUnique _ _ (RingHom.id _)
    (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
    (constructibleIntegralPullback l E f) (rationalDerivedTensor l E Y)
    (rationalDerivedTensor l E X) (rationalDerivedPullback l E f)
    (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec.1
    (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1
    (fun M N a z ↦ (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 M N a z)
    (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec.2
    (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.2
    (integralComparisonIso l E f))

private def rationalComparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    rationalDerivedTensor l E Y ⋙ rationalDerivedPullback l E f ≅
      (rationalDerivedPullback l E f).prod (rationalDerivedPullback l E f) ⋙
        rationalDerivedTensor l E X :=
  (rationalComparisonIso_existsUnique l E f).exists.choose

private theorem rationalComparisonIso_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (M N : sfRationalConstructibleCategory l E Y) :
    (rationalComparisonIso l E f).app (M, N) = canonicalRationalPullbackTensor l E f M N := by
  apply (canonicalRationalPullbackTensor_existsUnique l E f M N).unique
  · exact (rationalComparisonIso_existsUnique l E f).exists.choose_spec (M, N)
  · exact (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec

private theorem rationalComparison_natural {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {M M' N N' : sfRationalConstructibleCategory l E Y} (a : M ⟶ M') (b : N ⟶ N') :
    (rationalDerivedPullback l E f).map
        ((rationalDerivedTensor l E Y).map (Prod.mkHom a b)) ≫
        (canonicalRationalPullbackTensor l E f M' N').hom =
      (canonicalRationalPullbackTensor l E f M N).hom ≫
        (rationalDerivedTensor l E X).map
          (Prod.mkHom ((rationalDerivedPullback l E f).map a)
            ((rationalDerivedPullback l E f).map b)) := by
  simpa only [← Iso.app_hom, rationalComparisonIso_app, Functor.comp_map,
    Functor.prod_map] using (rationalComparisonIso l E f).hom.naturality (Prod.mkHom a b)

-- Keep the category instances fixed when comparing the finite-stage representatives.
section CommonAssociativity
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized commonstage comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  associator. The system comparison associativity equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalCommonStagePullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalCommonStagePullbackTensor_associative l _ Ω _ _ _ X Y f hX hY) := by
  intro M N P
  let F := commonStageDerivedPullback l Ω f
  let TY := commonStageDerivedTensor l Ω Y
  let TX := commonStageDerivedTensor l Ω X
  let OY := commonStageTensorObject l Ω Y
  let OX := commonStageTensorObject l Ω X
  let PB := commonStagePullbackObject l Ω f
  have hoY (A B) : TY.obj (A, B) = OY A B := by
    dsimp only [TY, OY]
    unfold commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1 A B
  have hoX (A B) : TX.obj (A, B) = OX A B := by
    dsimp only [TX, OX]
    unfold commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 A B
  have hoF (A) : F.obj A = PB A := by
    dsimp only [F, PB]
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 A
  have hTYL := (hoY (TY.obj (M, N)) P).trans
    (congrArg (fun A ↦ OY A P) (hoY M N))
  have hTYR := (hoY M (TY.obj (N, P))).trans
    (congrArg (OY M) (hoY N P))
  have hFCL := (congrArg F.obj hTYL).trans (hoF (OY (OY M N) P))
  have hFCR := (congrArg F.obj hTYR).trans (hoF (OY M (OY N P)))
  have hFMN := (congrArg F.obj (hoY M N)).trans (hoF (OY M N))
  have hFNP := (congrArg F.obj (hoY N P)).trans (hoF (OY N P))
  have hTMN := (hoX (F.obj M) (F.obj N)).trans (congrArg₂ OX (hoF M) (hoF N))
  have hTNP := (hoX (F.obj N) (F.obj P)).trans (congrArg₂ OX (hoF N) (hoF P))
  have hML := (hoX (F.obj (TY.obj (M, N))) (F.obj P)).trans
    (congrArg₂ OX hFMN (hoF P))
  have hMR := (hoX (F.obj M) (F.obj (TY.obj (N, P)))).trans
    (congrArg₂ OX (hoF M) hFNP)
  have hFL := (hoX (TX.obj (F.obj M, F.obj N)) (F.obj P)).trans
    (congrArg₂ OX hTMN (hoF P))
  have hFR := (hoX (F.obj M) (TX.obj (F.obj N, F.obj P))).trans
    (congrArg₂ OX (hoF M) hTNP)
  obtain ⟨L₀, hCL, hCR⟩ := exists_ge_ge (OY (OY M N) P).stage (OY M (OY N P)).stage
  obtain ⟨L₁, h₀, hW⟩ := exists_ge_ge L₀ (OX (PB (OY M N)) (PB P)).stage
  obtain ⟨L₂, h₁, hZ⟩ := exists_ge_ge L₁ (OX (PB M) (PB (OY N P))).stage
  obtain ⟨L₃, h₂, hWL⟩ := exists_ge_ge L₂ (OX (OX (PB M) (PB N)) (PB P)).stage
  obtain ⟨L, h₃, hZR⟩ := exists_ge_ge L₃ (OX (PB M) (OX (PB N) (PB P))).stage
  have hCL := hCL.trans (h₀.trans (h₁.trans (h₂.trans h₃)))
  have hCR := hCR.trans (h₀.trans (h₁.trans (h₂.trans h₃)))
  have hW := hW.trans (h₁.trans (h₂.trans h₃))
  have hZ := hZ.trans (h₂.trans h₃)
  have hWL := hWL.trans h₃
  have hA : (OY M N).stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 (OY M N).stage P.stage).1.trans hCL
  have hB : (OY N P).stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage (OY N P).stage).2.trans hCR
  have hM : M.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans hA
  have hN : N.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans hA
  have hP : P.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 N.stage P.stage).2.trans hB
  have hmap {A B A' B' : generalAlgebraicallyClosedConstructibleCategory l Ω Y}
      (hA : A = A') (hB : B = B')
      (hA' : A'.stage ≤ L) (hB' : B'.stage ≤ L)
      (a : A ⟶ B) (b : A'.toStage hA' ⟶ B'.toStage hB')
      (hab : HEq a (ofHom A' B' L hA' hB' b)) :
      HEq (F.map a) (ofHom (PB A') (PB B') L hA' hB'
        ((commonStagePullbackComparison l Ω f A' L hA').hom ≫
          (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
            b ≫ (commonStagePullbackComparison l Ω f B' L hB').inv)) := by
    refine (cached_map_heq F hA hB hab).trans ?_
    dsimp only [F, PB]
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.2
      A' B' L hA' hB' b
  have htmap {A B C D A' B' C' D' : generalAlgebraicallyClosedConstructibleCategory l Ω X}
      (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D')
      (hs : (OX A' C').stage ≤ L) (ht : (OX B' D').stage ≤ L)
      (a : A ⟶ B) (b : C ⟶ D)
      (a' : A'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage C'.stage).1.trans hs) ⟶
        B'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 B'.stage D'.stage).1.trans ht))
      (b' : C'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage C'.stage).2.trans hs) ⟶
        D'.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 B'.stage D'.stage).2.trans ht))
      (ha : HEq a (ofHom A' B' L
        (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage C'.stage).1.trans hs)
        (((Padic.finiteCoefficientFields_properties l Ω).1 B'.stage D'.stage).1.trans ht) a'))
      (hb : HEq b (ofHom C' D' L
        (((Padic.finiteCoefficientFields_properties l Ω).1 A'.stage C'.stage).2.trans hs)
        (((Padic.finiteCoefficientFields_properties l Ω).1 B'.stage D'.stage).2.trans ht) b')) :
      HEq (TX.map (Prod.mkHom a b)) (ofHom (OX A' C') (OX B' D') L hs ht
        ((commonStageTensorComparison l Ω X A' C' L hs).hom ≫
          (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X).map
            (Prod.mkHom a' b') ≫
          (commonStageTensorComparison l Ω X B' D' L ht).inv)) := by
    refine (cached_bimap_heq TX hA hB hC hD ha hb).trans ?_
    dsimp only [TX, OX]
    unfold commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.2
      A' C' B' D' L hs ht a' b'
  have hid (A : generalAlgebraicallyClosedConstructibleCategory l Ω X) (h : A.stage ≤ L) :
      HEq (𝟙 A) (ofHom A A L h h (𝟙 (A.toStage h))) :=
    heq_of_eq (StageSystem.PairCategory.id_eq_mkHom A h)
  have hidM : HEq (𝟙 (F.obj M)) (ofHom (PB M) (PB M) L hM hM (𝟙 _)) := by
    exact (cached_id_heq (hoF M)).trans (hid (PB M) hM)
  have hidP : HEq (𝟙 (F.obj P)) (ofHom (PB P) (PB P) L hP hP (𝟙 _)) := by
    exact (cached_id_heq (hoF P)).trans (hid (PB P) hP)
  have haeq (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (A B C : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
      (pullbackTensorCommonAssociator_existsUnique l Ω W A B C).exists.choose =
        pullbackTensorCommonAssociator l Ω W A B C := by
    unfold pullbackTensorCommonAssociator
    rfl
  have hα := (pullbackTensorCommonAssociator_existsUnique l Ω Y M N P).exists.choose_spec
    L hCL hCR
  rw [haeq] at hα
  have hαmap := hmap hTYL hTYR hCL hCR _ _ hα
  have hμR := (canonicalCommonStagePullbackTensor_existsUnique l Ω f M (OY N P)).exists.choose_spec
    L hCR
  have hμL := (canonicalCommonStagePullbackTensor_existsUnique l Ω f (OY M N) P).exists.choose_spec
    L hCL
  change HEq (canonicalCommonStagePullbackTensor l Ω f M (OY N P)).hom _ at hμR
  change HEq (canonicalCommonStagePullbackTensor l Ω f (OY M N) P).hom _ at hμL
  have hcompR (A B B' : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
      (h : B = B') : HEq (canonicalCommonStagePullbackTensor l Ω f A B).hom
        (canonicalCommonStagePullbackTensor l Ω f A B').hom := by
    subst B'
    rfl
  have hcompL (A A' B : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
      (h : A = A') : HEq (canonicalCommonStagePullbackTensor l Ω f A B).hom
        (canonicalCommonStagePullbackTensor l Ω f A' B).hom := by
    subst A'
    rfl
  have hμR' := hcompR M _ _ (hoY N P)
  have hμL' := hcompL _ _ P (hoY M N)
  have hμNP := (canonicalCommonStagePullbackTensor_existsUnique l Ω f N P).exists.choose_spec L hB
  have hμMN := (canonicalCommonStagePullbackTensor_existsUnique l Ω f M N).exists.choose_spec L hA
  change HEq (canonicalCommonStagePullbackTensor l Ω f N P).hom _ at hμNP
  change HEq (canonicalCommonStagePullbackTensor l Ω f M N).hom _ at hμMN
  have hTR := htmap (hoF M) (hoF M) hFNP hTNP
    hZ hZR (𝟙 (F.obj M)) _ _ _ hidM hμNP
  have hTL := htmap hFMN hTMN (hoF P) (hoF P)
    hW hWL _ (𝟙 (F.obj P)) _ _ hμMN hidP
  have hαX := (pullbackTensorCommonAssociator_existsUnique l Ω X
    (PB M) (PB N) (PB P)).exists.choose_spec L hWL hZR
  rw [haeq] at hαX
  have hacongr {A B C A' B' C' : generalAlgebraicallyClosedConstructibleCategory l Ω X}
      (ha : A = A') (hb : B = B') (hc : C = C') :
      HEq (pullbackTensorCommonAssociator l Ω X A B C).hom
        (pullbackTensorCommonAssociator l Ω X A' B' C').hom := by
    subst A' B' C'
    rfl
  have hαX' := hacongr (hoF M) (hoF N) (hoF P)
  have hl₁ := heq_comp hFCL hFCR hMR hαmap (hμR'.trans hμR)
  have hl := heq_comp hFCL hMR hFR hl₁ hTR
  have hr₁ := heq_comp hFCL hML hFL (hμL'.trans hμL) hTL
  have hr := heq_comp hFCL hFL hFR hr₁ (hαX'.trans hαX)
  simp only [← Category.assoc]
  apply eq_of_heq
  refine hl.trans ((heq_of_eq ?_).trans hr.symm)
  have hthree {A B C D : generalAlgebraicallyClosedConstructibleCategory l Ω X}
      (hA : A.stage ≤ L) (hB : B.stage ≤ L) (hC : C.stage ≤ L) (hD : D.stage ≤ L)
      (a : A.toStage hA ⟶ B.toStage hB) (b : B.toStage hB ⟶ C.toStage hC)
      (c : C.toStage hC ⟶ D.toStage hD) :
      (ofHom A B L hA hB a ≫ ofHom B C L hB hC b) ≫ ofHom C D L hC hD c =
        ofHom A D L hA hD ((a ≫ b) ≫ c) := by
    exact (congrArg (fun t ↦ t ≫ ofHom C D L hC hD c)
      (StageSystem.PairCategory.mkHom_comp_mkHom a b)).trans
      (StageSystem.PairCategory.mkHom_comp_mkHom (a ≫ b) c)
  change (ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _) ≫ ofHom _ _ L _ _ _ =
    (ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _) ≫ ofHom _ _ L _ _ _
  refine (hthree _ _ _ _ _ _ _).trans
    ((congrArg (ofHom _ _ L _ _) ?_).trans (hthree _ _ _ _ _ _ _).symm)
  unfold pullbackTensorCommonLeft pullbackTensorCommonRight pullbackTensorAtCommonStage
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Iso.prod, Functor.mapIso]
  exact
    (@representative_associativity (Stage l Ω Y L) (Stage l Ω X L)
      (stageCategory l Ω Y L) (stageCategory l Ω X L)
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
      (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y)
      (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
      (canonicalRationalPullbackTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
      (rationalComparison_natural l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
      (pullbackTensorRationalAssociator l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y)
      (pullbackTensorRationalAssociator l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
      (canonicalRationalPullbackTensor_associative_spec l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
      (rationalAssociator_natural l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
      (M.toStage hM) (N.toStage hN) (P.toStage hP)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (commonStageTensorComparison l Ω Y M N L hA)
      (commonStageTensorComparison l Ω Y N P L hB)
      (commonStageTensorComparison l Ω Y (OY M N) P L hCL)
      (commonStageTensorComparison l Ω Y M (OY N P) L hCR)
      (commonStagePullbackComparison l Ω f (OY (OY M N) P) L hCL)
      (commonStagePullbackComparison l Ω f (OY M (OY N P)) L hCR)
      (commonStagePullbackComparison l Ω f M L hM)
      (commonStagePullbackComparison l Ω f N L hN)
      (commonStagePullbackComparison l Ω f P L hP)
      (commonStagePullbackComparison l Ω f (OY M N) L hA)
      (commonStagePullbackComparison l Ω f (OY N P) L hB)
      (commonStageTensorComparison l Ω X (PB M) (PB N) L hA)
      (commonStageTensorComparison l Ω X (PB N) (PB P) L hB)
      (commonStageTensorComparison l Ω X (PB (OY M N)) (PB P) L hW)
      (commonStageTensorComparison l Ω X (PB M) (PB (OY N P)) L hZ)
      (commonStageTensorComparison l Ω X (OX (PB M) (PB N)) (PB P) L hWL)
      (commonStageTensorComparison l Ω X (PB M) (OX (PB N) (PB P)) L hZR))

end CommonAssociativity

end AssociativityNaturality

attribute [local irreducible] pullbackTensorIntegralBraiding pullbackTensorRationalBraiding
  rationalDerivedTensor rationalDerivedPullback canonicalRationalPullbackTensor

private theorem integralBraiding_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M M' N N' : sfIntegralConstructibleCategory l E W)
    (f : M ⟶ M') (g : N ⟶ N') :
    (constructibleIntegralTensor l E W).map (Prod.mkHom f g) ≫
        (pullbackTensorIntegralBraiding l E W M' N').hom =
      (pullbackTensorIntegralBraiding l E W M N).hom ≫
        (constructibleIntegralTensor l E W).map (Prod.mkHom g f) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let Q := coherentReduction l E W
    let T := constructibleIntegralTensor l E W
    let S := (pullbackTensorCalculus l E W).systemClosed.tensor
    let b := reduction_tensor l E W
    let β := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
      (pullbackTensorCalculus l E W).systemClosed
      (pullbackTensorCalculus l E W).systemTensorModel
    have hb (A B) : Q.map (pullbackTensorIntegralBraiding l E W A B).hom ≫
        b.hom.app (B, A) = b.hom.app (A, B) ≫ β.hom.app (Q.obj A, Q.obj B) :=
      by
        unfold pullbackTensorIntegralBraiding
        exact (pullbackTensorIntegralBraiding_existsUnique l E W A B).exists.choose_spec
    have := (coherentReduction_fullyFaithful l E W).2
    exact reducedBraiding_natural Q T S b (fun A B ↦ β.hom.app (A, B))
      (fun _ _ _ _ a b ↦ β.hom.naturality (Prod.mkHom a b))
      (fun A B ↦ (pullbackTensorIntegralBraiding l E W A B).hom) hb M M' N N' f g

attribute [local irreducible] sfIntegralConstructible

private theorem rationalBraiding_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M M' N N' : sfRationalConstructibleCategory l E W) (f : M ⟶ M') (g : N ⟶ N') :
    (rationalDerivedTensor l E W).map (Prod.mkHom f g) ≫
        (pullbackTensorRationalBraiding l E W M' N').hom =
      (pullbackTensorRationalBraiding l E W M N).hom ≫
        (rationalDerivedTensor l E W).map (Prod.mkHom g f) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    exact localizedBraiding_natural
      (R := Padic.coefficientExtensionIntegers l E)
      (A := sfIntegralConstructibleCategory l E W) _ (constructibleIntegralTensor l E W)
      (pullbackTensorIntegralBraiding l E W) (integralBraiding_natural l E W)
      (rationalDerivedTensor l E W) (pullbackTensorRationalBraiding l E W)
      (by
        unfold rationalDerivedTensor
        exact (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1)
      (by
        unfold rationalDerivedTensor
        exact (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2)
      (by
        intro M N
        unfold pullbackTensorRationalBraiding
        exact (pullbackTensorRationalBraiding_existsUnique l E W M N).exists.choose_spec)
      M M' N N' f g

-- Keep cached category data while comparing representatives over one coefficient field.
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

/-- The normalized commonstage comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  braiding. The system comparison signed symmetry equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalCommonStagePullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalCommonStagePullbackTensor_braiding l _ Ω _ _ _ X Y f hX hY) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    intro M N
    let F := commonStageDerivedPullback l Ω f
    let OY := commonStageTensorObject l Ω Y
    let OX := commonStageTensorObject l Ω X
    let P := commonStagePullbackObject l Ω f
    have hoY (A B) : (commonStageDerivedTensor l Ω Y).obj (A, B) = OY A B := by
      unfold commonStageDerivedTensor
      exact (commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1 A B
    have hoX (A B) : (commonStageDerivedTensor l Ω X).obj (A, B) = OX A B := by
      unfold commonStageDerivedTensor
      exact (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 A B
    have hoF (A) : F.obj A = P A := by
      dsimp only [F]
      unfold commonStageDerivedPullback
      exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 A
    obtain ⟨L₁, hMN, hNM⟩ := exists_ge_ge (OY M N).stage (OY N M).stage
    obtain ⟨L₂, h₁, hPMN⟩ := exists_ge_ge L₁ (OX (P M) (P N)).stage
    obtain ⟨L, h₂, hPNM⟩ := exists_ge_ge L₂ (OX (P N) (P M)).stage
    have hMN := hMN.trans (h₁.trans h₂)
    have hNM := hNM.trans (h₁.trans h₂)
    have hPMN := hPMN.trans h₂
    have hM : M.stage ≤ L :=
      ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans hMN
    have hN : N.stage ≤ L :=
      ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans hMN
    have hmap {A B A' B' : generalAlgebraicallyClosedConstructibleCategory l Ω Y}
        (hA : A = A') (hB : B = B')
        (hA' : A'.stage ≤ L) (hB' : B'.stage ≤ L)
        (a : A ⟶ B) (b : A'.toStage hA' ⟶ B'.toStage hB')
        (hab : HEq a (ofHom A' B' L hA' hB' b)) :
        HEq (F.map a) (ofHom (P A') (P B') L hA' hB'
          ((commonStagePullbackComparison l Ω f A' L hA').hom ≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map b ≫
            (commonStagePullbackComparison l Ω f B' L hB').inv)) := by
      subst A B
      cases hab
      dsimp only [F, P]
      unfold commonStageDerivedPullback
      exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.2
        A' B' L hA' hB' b
    have hβ := (pullbackTensorCommonBraiding_existsUnique l Ω Y M N).exists.choose_spec
      L hMN hNM
    change HEq (pullbackTensorCommonBraiding l Ω Y M N).hom _ at hβ
    have hβmap := hmap (hoY M N) (hoY N M) hMN hNM
      (pullbackTensorCommonBraiding l Ω Y M N).hom _ hβ
    have hμ := (canonicalCommonStagePullbackTensor_existsUnique l Ω f M N).exists.choose_spec
      L hMN
    have hμ' := (canonicalCommonStagePullbackTensor_existsUnique l Ω f N M).exists.choose_spec
      L hNM
    change HEq (canonicalCommonStagePullbackTensor l Ω f M N).hom _ at hμ
    change HEq (canonicalCommonStagePullbackTensor l Ω f N M).hom _ at hμ'
    have hβX := (pullbackTensorCommonBraiding_existsUnique l Ω X (P M) (P N)).exists.choose_spec
      L hPMN hPNM
    change HEq (pullbackTensorCommonBraiding l Ω X (P M) (P N)).hom _ at hβX
    have hβeq : HEq (pullbackTensorCommonBraiding l Ω X (F.obj M) (F.obj N)).hom
        (pullbackTensorCommonBraiding l Ω X (P M) (P N)).hom := by
      rw [hoF M, hoF N]
    have hl := heq_comp
      (by rw [hoY, hoF]) (by rw [hoY, hoF])
      (by rw [hoX, hoF, hoF]) hβmap hμ'
    have hr := heq_comp
      (by rw [hoY, hoF]) (by rw [hoX, hoF, hoF])
      (by rw [hoX, hoF, hoF]) hμ (hβeq.trans hβX)
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _ =
      ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _
    refine (StageSystem.PairCategory.mkHom_comp_mkHom _ _).trans
      ((congrArg (ofHom _ _ L _ _) ?_).trans
        (StageSystem.PairCategory.mkHom_comp_mkHom _ _).symm)
    exact @representative_braiding (Stage l Ω Y L) (Stage l Ω X L)
        (stageCategory l Ω Y L) (stageCategory l Ω X L)
        (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
        (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y)
        (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
        (pullbackTensorRationalBraiding l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y)
        (pullbackTensorRationalBraiding l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
        (canonicalRationalPullbackTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
        (canonicalRationalPullbackTensor_braiding_spec l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
        (rationalBraiding_natural l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
        (M.toStage hM) (N.toStage hN) _ _ _ _ _ _ _ _
        (commonStageTensorComparison l Ω Y M N L hMN)
        (commonStageTensorComparison l Ω Y N M L hNM)
        (commonStagePullbackComparison l Ω f (OY M N) L hMN)
        (commonStagePullbackComparison l Ω f (OY N M) L hNM)
        (commonStagePullbackComparison l Ω f M L hM)
        (commonStagePullbackComparison l Ω f N L hN)
        (commonStageTensorComparison l Ω X (P M) (P N) L hPMN)
        (commonStageTensorComparison l Ω X (P N) (P M) L hPNM)

end HigherCoherence

-- Avoid unfolding completed interfaces while checking the assembly statement.
attribute [local irreducible]
  canonicalCommonStagePullbackTensor
  pullbackTensorIntegralComposition pullbackTensorRationalComposition
  pullbackTensorCommonComposition canonicalIntegralPullbackTensor_composition
  canonicalRationalPullbackTensor_composition canonicalCommonStagePullbackTensor_composition
  pullbackTensorIntegralReductionTensor pullbackTensorIntegralReductionPullback
  canonicalIntegralPullbackTensor_reduction pullbackTensorIntegralAssociator
  pullbackTensorRationalAssociator pullbackTensorIntegralBraiding pullbackTensorRationalBraiding
  pullbackTensorCommonLeft pullbackTensorCommonRight pullbackTensorCommonAssociator
  pullbackTensorCommonBraiding pullbackTensorIntegralUnit pullbackTensorIntegralUnitReduction
  pullbackTensorRationalUnit pullbackTensorIntegralLeftUnitor pullbackTensorRationalLeftUnitor
  pullbackTensorIntegralRightUnitor pullbackTensorRationalRightUnitor
  pullbackTensorRationalScalarUnit pullbackTensorCommonUnit pullbackTensorCommonUnitStage
  pullbackTensorCommonLeftUnitor pullbackTensorCommonRightUnitor
  canonicalIntegralPullbackTensor_unit canonicalRationalPullbackTensor_unit
  canonicalCommonStagePullbackTensor_unit canonicalIntegralPullbackTensor_associative
  canonicalRationalPullbackTensor_associative canonicalCommonStagePullbackTensor_associative
  canonicalIntegralPullbackTensor_braiding canonicalRationalPullbackTensor_braiding
  canonicalCommonStagePullbackTensor_braiding

/-- The canonical derived pullback/tensor comparison exists at every coefficient
level and is natural in both inputs.  At finite level this is the comparison for
the constant-coefficient morphism of ringed pro-etale topoi.  At integral level it
is the inverse-limit comparison on completed reductions; at rational level it is
its scalar localization; and at algebraically closed level it is the common-stage
comparison over a finite coefficient compositum.  The comparison is compatible
with the tensor unit, associativity, signed symmetry, coefficient reduction and
scalar extension, and with composition of pullbacks, as in the proof steps of
`lem-pur-derived-pullback-tensor-iso`.

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4 (Tag 07A4,
label `lemma-pullback-tensor-product`), for the morphism of ringed topoi
(X_proet, (A_{E,n})_X) -> (Y_proet, (A_{E,n})_Y); the integral, rational and Qlbar
levels follow the level-by-level definitions of the operations in
prose-03-02.

Proof plan (the node's numbered steps):

1. At finite level choose compatible small representatives of the pro-etale sites as in [def-weil-
   proetale-inverse-image]. The inverse image and its constant-ring map make $f_n$ a morphism of
   ringed topoi. By [prop-weil-pbc-proetale-constant-exact], module pullback is exact and agrees
   with inverse image with the coefficient action transported through
   $f^{-1}(A_{E,n})_Y\cong(A_{E,n})_X$. Thus its derived functor is precisely the finite operation
   in [prose-03-02]. Apply [lem-weil-pbc-ringed-topoi-derived-tensor-
   pullback] with $R=(A_{E,n})_Y$ and $S=(A_{E,n})_X$. Its displayed isomorphism, natural in both
   arguments, is $\mu_{f;M,N}$. That theorem is unbounded, so it applies to all the finite-level
   inputs claimed here; no finite Tor dimension of $A_{E,n}$ is assumed.

2. Choose flat-term K-flat resolutions $P,Q$ by [lem-pc-kflat-resolution]. The closure assertion
   [lem-pur-kflat-total-tensor-model] shows that $\operatorname{Tot}(P\otimes Q)$ is K-flat with
   flat terms, so all iterated tensors below compute derived tensors. On these models the
   comparison is totalized from the module map of [lem-weil-pbc-ringed-topoi-module-pullback-
   tensor], with the signed differential from [def-pc-tensor-complex-sheaves].

3. Use the chain maps of [lem-pur-cochain-pullback-tensor-coherence]. Their pure-tensor formula
   and inverse are the ordinary comparison of [lem-weil-pbc-ringed-topoi-module-pullback-tensor],
   and the chain lemma supplies associativity, signed symmetry, units, composition and
   coefficient-change equations. By [lem-weil-pbc-site-derived-tensor-descent] these maps and
   equations descend from the K-flat resolving class to arbitrary finite-level derived inputs.

4. For integral $M,N$, choose flat-term K-flat representatives $P,Q$ by [lem-pc-kflat-resolution].
   Set $P_n=P\otimes_{R_Y}B_{Y,n}$ and $Q_n=Q\otimes_{R_Y}B_{Y,n}$, with actual quotient
   transitions. Put $T_n=\operatorname{Tot}(P_n\otimes Q_n)$, $U_n=f_n^*P_n$, $V_n=f_n^*Q_n$, and
   $W_n=\operatorname{Tot}(U_n\otimes V_n)$. The quotient and pullback models are flat-term K-flat
   by [lem-pur-kflat-change-of-rings, lem-weil-pbc-ringed-pullback-preserves-kflat], and the
   tensor totals by step 2. The normalization and coherent reduction assertions of [lem-pur-
   completed-operation-tower-substitution] and [lemma-sp-tower-adjunction-foundation--2] identify
   these systems with the reductions of the completed operations in [def-pur-integral-derived-
   operations]. Here $B_{Y,n}=(A_{E,n})_Y$ and $R_Y=\varprojlim B_{Y,n}$, as in the normalized
   tower convention [def-coef-normalized-dvr-tower].

5. The cochain maps of [lem-pur-cochain-pullback-tensor-coherence] give the strict tower
   isomorphism $f_n^*T_n\to W_n$ and its strict inverse. Apply [lem-pur-integral-tower-limit-
   comparison] to the $T,U,V$ of step 4. With the substitution identifications of [lem-pur-
   completed-operation-tower-substitution], its actual derived-limit map is the required
   comparison between completed pullback of $M\widehat\otimes^L N$ and completed tensor of
   $Lf^*M,Lf^*N$. The functor is [lem-weil-pbc-ringed-strict-tower-homotopy-limit]; its naturality
   and the resolution comparisons of [lem-pur-integral-operations-well-defined] give naturality in
   $M,N$ and independence of the chosen representatives.

6. By [lem-pur-integral-operations-preserve-constructible], $M\widehat\otimes^L N$ is
   constructible on $Y$ and its pullback is constructible on $X$. The same lemma first puts
   $Lf^*M,Lf^*N$ in $D^b_c(X,\mathcal O_E)$ and then puts their completed tensor there. This is a
   full subcategory of the ambient derived category [def-weil-derived-complete-integral-detailed],
   so the ambient comparison and its inverse are morphisms of that subcategory.

7. The finite associativity, signed symmetry, unit and pullback-composition equations from [lem-
   pur-cochain-pullback-tensor-coherence] are compatible with every quotient transition. The
   tower-level assertion [lem-pur-integral-coherence-tower] therefore identifies them as
   equalities of strict normalized systems and gives their integral images after applying [lem-
   pur-completed-operation-tower-substitution] and [lem-weil-pbc-ringed-strict-tower-homotopy-
   limit].

8. The coherent counit comparisons of [lemma-sp-tower-adjunction-foundation--2], applied to the
source
   and target systems of the strict comparison, identify its reduction with the finite comparison.
   Their naturality applies to this actual map of systems, and [lem-pur-completed-operation-tower-
   substitution] carries the counits to the completed operations. No faithfulness assertion for
   individual finite-reduction functors is needed.

9. For $E\subset L$ put $B_m=\mathcal O_L/\varpi_L^m$. The strict quotient models of [def-weil-
   integral-scalar-extension] and the coherent reduction model [lem-pur-coefficient-extension-
   reduction-model] give the normalized $B_\bullet$-tower, including ramified extensions. The
   quotient K-flatness is [lem-pur-kflat-change-of-rings], and the scalar-association and
   transition equations are exactly [lem-pur-scalar-extension-tower-coherence].

10. Use the pullback and tensor scalar-extension isomorphisms of [lem-pur-integral-operations-
   scalar-extension] in their canonical quotient-model form. The tower coherence statement [lem-
   pur-scalar-extension-tower-coherence] says that both routes around the comparison square send
   $b\otimes(x\otimes y)$ to $(b\otimes x)\otimes(1\otimes y)$ and commute with every quotient and
   coefficient square. Applying [lem-weil-pbc-ringed-strict-tower-homotopy-limit] and [lem-pur-
   completed-operation-tower-substitution] gives the integral scalar-extension square.

11. By [def-weil-rationalization-karoubi], every rational object is an integral object and every
   morphism is a finite sum of $u\otimes a$, with $u$ integral and $a\in E$. Define $\mu^E$ to be
   the image $\mu^{\mathcal O_E}\otimes1$; its inverse is the image of the integral inverse. The
   operations on rational morphisms are the scalar extensions specified in [def-weil-derived-
   pullback-tensor-hom]. The integral naturality identity for $u,v$, multiplied by the
   corresponding scalars, gives rational naturality; add the resulting identities for sums. Every
   integral coherence equation remains an equality after tensoring Hom groups with $E$, so the
   rational associativity, symmetry, unit and composition equations follow. The scalar-extension
   square of the preceding scalar-extension steps likewise remains commutative, since the rational
   scalar-extension functor is the one induced from the integral scalar-extension functor.

12. For objects $(E,M),(E',N)$ at the algebraically closed level, choose a common finite
   coefficient field $L$ and form the rational comparison there, conjugated by the scalar-
   extension comparisons as prescribed in [prose-03-02]. Represent the
   inverse by the inverse rational comparison with the inverse conjugating comparisons. In [def-
   weil-algebraically-closed-coefficients], morphisms are classes over common finite fields, and
   two representatives agree if they agree after passage to a further common field. The scalar-
   extension calculation after rationalization says precisely that passing from $L$ to any larger
   field sends this comparison to the same comparison there; hence the class and its inverse are
   independent of $L$. Represent any finite naturality or coherence diagram over a single common
   finite field; the rational identity proved in the preceding rationalization step gives its
   equality in the colimit Hom group. This proves all the asserted compatibilities at $\Qlb$,
   including scalar extension into $\Qlb$.
(blueprint: lem-pur-derived-pullback-tensor-iso) -/
theorem derivedPullbackTensorIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
      [IsAlgClosure (Padic l) Ω] :
    ((∃ eF : (finiteIntrinsicDerivedTensor l E Y n) ⋙ (finiteDerivedPullback l E n f) ≅
        ((finiteDerivedPullback l E n f).prod (finiteDerivedPullback l E n f)) ⋙
          (finiteIntrinsicDerivedTensor l E X n),
        ∀ (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
          eF.app (M,N) = (@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N) ∧
      (@canonicalFinitePullbackTensor_associativity_condition l _ E _ _ _ X Y f n hX hY) ∧
      (@canonicalFinitePullbackTensor_unit_condition l _ E _ _ _ X Y f n hX hY) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)],
        (@canonicalFinitePullbackTensor_composition_condition l _ E _ _ _ X Y Z f h n hX hY hZ)) ∧
      (@canonicalFinitePullbackTensor_braiding_condition l _ E _ _ _ X Y f n hX hY) ∧
      (∃ eI : (@constructibleIntegralTensor l _ E _ _ _ Y hY) ⋙ (@constructibleIntegralPullback l _
        E _ _ _ X Y f hX hY) ≅
        ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY).prod
          (@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)) ⋙ (@constructibleIntegralTensor
          l _ E _ _ _ X hX),
        ∀ (M N : sfIntegralConstructibleCategory l E Y),
          eI.app (M,N) = (@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N) ∧
      (∃ eR : (@rationalDerivedTensor l _ E _ _ _ Y hY) ⋙ (@rationalDerivedPullback l _ E _ _ _ X Y
        f hX hY) ≅
        ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY).prod (@rationalDerivedPullback l _ E _ _
          _ X Y f hX hY)) ⋙ (@rationalDerivedTensor l _ E _ _ _ X hX),
        ∀ (M N : sfRationalConstructibleCategory l E Y),
          eR.app (M,N) = (@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N) ∧
      (∃ eC : (@commonStageDerivedTensor l _ Ω _ _ _ Y hY) ⋙ (@commonStageDerivedPullback l _ Ω _ _
        _ X Y f hX hY) ≅
        ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY).prod (@commonStageDerivedPullback l _
          Ω _ _ _ X Y f hX hY)) ⋙ (@commonStageDerivedTensor l _ Ω _ _ _ X hX),
        ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
          eC.app (M,N) = (@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N) ∧
      (∀ M N : sfRationalConstructibleCategory l E Y,
        HEq ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom
          ((sfRationalConstructibleLocalization l E X).map
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M.obj N.obj).hom)) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (M N : sfIntegralConstructibleCategory l E Y),
        (@canonicalIntegralPullbackTensor_composition l _ E _ _ _ X Y Z f h hX hY hZ) M N) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (M N : sfRationalConstructibleCategory l E Y),
        (@canonicalRationalPullbackTensor_composition l _ E _ _ _ X Y Z f h hX hY hZ) M N) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
        (@canonicalCommonStagePullbackTensor_composition l _ Ω _ _ _ X Y Z f h hX hY hZ) M N) ∧
      (∀ M N, (@canonicalIntegralPullbackTensor_reduction l _ E _ _ _ X Y f hX hY) M N) ∧
      (@canonicalIntegralPullbackTensor_associative l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalRationalPullbackTensor_associative l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalCommonStagePullbackTensor_associative l _ Ω _ _ _ X Y f hX hY) ∧
      (@canonicalIntegralPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalRationalPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalCommonStagePullbackTensor_braiding l _ Ω _ _ _ X Y f hX hY) ∧
      (@canonicalIntegralPullbackTensor_unit l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalRationalPullbackTensor_unit l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalCommonStagePullbackTensor_unit l _ Ω _ _ _ X Y f hX hY) ∧
      (∀ {m q : ℕ} (hq : q ≤ m)
        (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))),
        (canonicalFinitePullbackTensor_quotient_condition l E f (hX := hX) (hY := hY)
          (m := m) (n := q) hq M N)) ∧
      (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
        (M N : sfIntegralConstructibleCategory l E Y),
        (canonicalIntegralPullbackTensor_scalar_condition l E L ι f
          (hX := hX) (hY := hY) M N)) ∧
      (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
        (M N : sfRationalConstructibleCategory l E Y),
        (canonicalRationalPullbackTensor_scalar_condition l E L ι f
          (hX := hX) (hY := hY) M N)) ∧
      (∀ (n : ℕ) (M N : coefficientSequenceDerived l E Y),
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSystemComparison l E f).hom.app (M,N)) ≫
          ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
            ((pullbackTensorSequenceDerived l E f).obj M,
              (pullbackTensorSequenceDerived l E f).obj N) ≫
          (finiteIntrinsicDerivedTensor l E X n).map
            (Prod.mkHom ((pullbackTensorDerivedEvaluation l E f n).hom.app M)
              ((pullbackTensorDerivedEvaluation l E f n).hom.app N)) =
        (pullbackTensorDerivedEvaluation l E f n).hom.app
          ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N)) ≫
          (finiteDerivedPullback l E n f).map
            (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M,N)) ≫
          ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
            ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
            ((coefficientSequenceDerivedEvaluation l E Y n).obj N)).hom)) := by
  have hcomposition {Z : Scheme.{u}} (h : Z ⟶ X)
      [∀ z : Z, Invertible (l : Z.residueField z)] :=
    pullbackTensorCompositionCoherence l E Ω f h
  obtain ⟨hunitI, hunitR, hunitC⟩ := pullbackTensorUnitCoherence l E Ω f
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hunitI, hunitR, hunitC, ?_, ?_, ?_, ?_⟩
  · refine ⟨finitePullbackTensorConstructionIso l E f n, ?_⟩
    intro M N
    rfl
  · exact canonicalFinitePullbackTensor_associativity l E f n
  · exact canonicalFinitePullbackTensor_unit l E f n
  · intro Z h hZ
    exact canonicalFinitePullbackTensor_composition l E f h n
  · exact canonicalFinitePullbackTensor_braiding l E f n
  · exact ⟨integralComparisonIso l E f, fun _ _ ↦ rfl⟩
  · exact ⟨rationalComparisonIso l E f, rationalComparisonIso_app l E f⟩
  · refine ⟨NatIso.ofComponents
      (fun MN ↦ canonicalCommonStagePullbackTensor l Ω f MN.1 MN.2) ?_, ?_⟩
    · intro MN MN' a
      exact commonStagePullbackTensor_naturality l Ω f
        (fun E _ _ _ ↦ rationalComparison_natural l E f) a.1 a.2
    · intro M N
      rfl
  · intro M N
    exact (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec
  · intro Z h hZ M N
    exact (hcomposition h).1 M N
  · intro Z h hZ M N
    exact (hcomposition h).2.1 M N
  · intro Z h hZ M N
    exact (hcomposition h).2.2 M N
  · exact integralComparison_reduction l E f
  · exact canonicalIntegralPullbackTensor_associative_spec l E f
  · exact canonicalRationalPullbackTensor_associative_spec l E f
  · exact canonicalCommonStagePullbackTensor_associative_spec l Ω f
  · exact canonicalIntegralPullbackTensor_braiding_spec l E f
  · exact canonicalRationalPullbackTensor_braiding_spec l E f
  · exact canonicalCommonStagePullbackTensor_braiding_spec l Ω f
  · intro m q hq M N
    exact canonicalFinitePullbackTensor_quotient l E f hq M N
  · intro L _ _ _ ι M N
    exact canonicalIntegralPullbackTensor_scalar l E L ι f M N
  · intro L _ _ _ ι M N
    exact canonicalRationalPullbackTensor_scalar l E L ι f M N
  · intro q M N
    exact pullbackTensorSystemComparison_evaluation l E f q M N

end WeilConjectures
