/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionComparison
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! # Compact-support system evaluation diagram

Source: Weil conjectures blueprint, `prop-trf-rational-frobenius-integral-model.proof.md`,
clause (3), second paragraph (blueprint: def-trf-compact-support-system-evaluation-diagram).
The canonical system operations are supplied by the ordinary semilinear derived-sections
calculus and the coefficient sequence site.  This module records the comparison before any
inverse limit is taken.

## Main definitions

- `CompactSupportSystemEvaluationData` records the exact open-extension and direct-image
  functors together with their canonical level evaluations.
- `compactSupportSystemSourceLevel` and `compactSupportSystemTargetLevel` are the two
  levelwise functors compared by the theorem.

## Transition definitions

- `compactSupportSystemSourceTransition` evaluates the actual completed tower.
- `compactSupportSystemCoefficientMate` and `compactSupportSystemTargetTransition`
  construct the specified coefficient mate and its scalar-adjunction transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor

universe t u c₁ c₂ d₁ d₂ v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual finite-coefficient sectionwise direct image along `p`.
Source: the node's proof step 2, Stacks 03D2 and Zheng 4.10
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
abbrev compactSupportLevelDirectImage
    {Z Y : Scheme.{t}} (p : Z ⟶ Y) (n : ℕ) :
    normalizedDVRModules l E Z n ⥤ normalizedDVRModules l E Y n :=
  Scheme.coefficientProEtaleModuleDirectImage.{t, u} p
    (CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1))))

/-- The inherited ordinary adjunction for the canonical finite direct image.
Source: node proof step 2, Stacks 03D2
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
instance compactSupportLevelDirectImageRightAdjoint {Z Y : Scheme.{t}} (p : Z ⟶ Y) (n : ℕ) :
    (compactSupportLevelDirectImage l E p n).IsRightAdjoint :=
  Scheme.coefficientProEtaleModuleDirectImage_isRightAdjoint.{t, u} p
    (CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1))))

/-- The actual coefficient inverse image adjoint to the sectionwise direct image.
Source: the node's proof step 2, Stacks 03D2
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
abbrev compactSupportLevelPullback
    {Z Y : Scheme.{t}} (p : Z ⟶ Y) (n : ℕ) :
    normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E Z n :=
  Scheme.coefficientProEtaleModulePullback.{t, u} p
    (CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1))))

/-- Normalization of a derived evaluation square on arbitrary K-injective resolutions.
It specifies the actual localization of the underived comparison, without assuming that
an exact evaluation or scalar restriction preserves K-injectives.
Source: node proof step 2, Stacks 0D6E and Zheng 4.10
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def CompactSupportDerivedSquareNormalization
    {C : Type c₁} {C' : Type c₂} {A : Type d₁} {A' : Type d₂}
    [Category.{v} C] [Category.{v} C'] [Category.{v} A] [Category.{v} A']
    [Abelian C] [Abelian C'] [Abelian A] [Abelian A']
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} C']
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} A']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (G : C ⥤ A) (G' : C' ⥤ A') (H : C ⥤ C') (K : A ⥤ A')
    [G.Additive] [G'.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (a : H ⋙ G' ≅ G ⋙ K)
    (d : H.mapDerivedCategory ⋙ G'.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ K.mapDerivedCategory) : Prop :=
  ∀ (J : CochainComplex C ℤ) [J.IsKInjective]
    (I : CochainComplex C' ℤ) [I.IsKInjective]
    (r : (H.mapHomologicalComplex (.up ℤ)).obj J ⟶ I) [QuasiIso r],
    d.hom.app (DerivedCategory.Q.obj J) ≫
      K.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso J).hom ≫
      K.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).inv.app J) ≫
      DerivedCategory.Q.map ((G'.mapHomologicalComplex (.up ℤ)).map r) =
    G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app J) ≫
      G'.rightDerivedFunctor.map (DerivedCategory.Q.map r) ≫
      (G'.rightDerivedFunctorObjQIso I).hom

/-- The canonical derived system adjunction of the actual ordinary inverse/direct image.
Source: node proof step 2, Stacks 03D2, 07A4
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportCanonicalPAdjunction {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    [(integralComparisonSequenceDirectImage l E p).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E Z)] :
    integralComparisonDerivedSequencePullback l E p ⊣
      (integralComparisonSequenceDirectImage l E p).rightDerivedFunctor :=
  letI : (integralComparisonSequenceDirectImage l E p).leftAdjoint.Additive :=
    integralComparisonSequencePullbackAdditive l E p
  letI : PreservesFiniteLimits (integralComparisonSequenceDirectImage l E p).leftAdjoint :=
    integralComparisonSequencePullbackLimits l E p
  letI : PreservesFiniteColimits (integralComparisonSequenceDirectImage l E p).leftAdjoint :=
    integralComparisonSequencePullbackColimits l E p
  (Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E p)).mapDerivedCategoryRightDerivedAdjunction

/-- The canonical derived finite inverse/direct-image adjunction, with its ordinary units.
Source: node proof step 2, Stacks 03D2, 07A4
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportCanonicalPLevelAdjunction {Z Y : Scheme.{t}} (p : Z ⟶ Y) (n : ℕ)
    [(compactSupportLevelDirectImage l E p n).Additive]
    [Abelian.HasKInjectiveResolutions (normalizedDVRModules l E Z n)]
    [ha : (compactSupportLevelPullback l E p n).Additive]
    [hl : PreservesFiniteLimits (compactSupportLevelPullback l E p n)]
    [hc : PreservesFiniteColimits (compactSupportLevelPullback l E p n)] :
    (compactSupportLevelPullback l E p n).mapDerivedCategory ⊣
      (compactSupportLevelDirectImage l E p n).rightDerivedFunctor :=
  letI : (compactSupportLevelDirectImage l E p n).leftAdjoint.Additive := ha
  letI : PreservesFiniteLimits (compactSupportLevelDirectImage l E p n).leftAdjoint := hl
  letI : PreservesFiniteColimits (compactSupportLevelDirectImage l E p n).leftAdjoint := hc
  (Adjunction.ofIsRightAdjoint
    (compactSupportLevelDirectImage l E p n)).mapDerivedCategoryRightDerivedAdjunction

/-- Presentation data for the actual operations, with no independent geometric functors.
All fields of this package are existentially supplied by the main theorem. The ordinary
coefficient comparison is the identity on sections, and its derived comparison is fixed
on every K-injective resolution. Thus its scalar-adjunction mate is the actual `b`.
Source: the node's proof steps 1--3, Zheng 4.1 and 4.10
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
class CompactSupportSystemOperationInstances
    {X Z Y : Scheme.{t}} (j : X ⟶ Z) (p : Z ⟶ Y) [IsOpenImmersion j] where
  jOperations : IntegralOpenReduction.Operations l E j
  [pAdditive : (integralComparisonSequenceDirectImage l E p).Additive]
  [pKInjective : Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E Z)]
  [levelAdditive : ∀ n : ℕ, (compactSupportLevelDirectImage l E p n).Additive]
  [levelKInjective : ∀ n : ℕ,
    Abelian.HasKInjectiveResolutions (normalizedDVRModules l E Z n)]
  [pullAdditive : ∀ n : ℕ, (compactSupportLevelPullback l E p n).Additive]
  [pullLimits : ∀ n : ℕ, PreservesFiniteLimits (compactSupportLevelPullback l E p n)]
  [pullColimits : ∀ n : ℕ, PreservesFiniteColimits (compactSupportLevelPullback l E p n)]

attribute [instance] CompactSupportSystemOperationInstances.pAdditive
  CompactSupportSystemOperationInstances.pKInjective
  CompactSupportSystemOperationInstances.levelAdditive
  CompactSupportSystemOperationInstances.levelKInjective
  CompactSupportSystemOperationInstances.pullAdditive
  CompactSupportSystemOperationInstances.pullLimits
  CompactSupportSystemOperationInstances.pullColimits

/-- The actual quotient adjunctions and ordinary/derived direct-image coefficient squares.
Their section and resolution normalizations are asserted in the main witness conclusion.
Source: node statement, coefficient mate b; Zheng 4.10
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
class CompactSupportSystemCanonicalOperations
    {X Z Y : Scheme.{t}} (j : X ⟶ Z) (p : Z ⟶ Y) [IsOpenImmersion j] where
  [instances : CompactSupportSystemOperationInstances l E j p]
  scalarZ : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientFiniteQuotientDerived l E Z h ⊣ normalizedDVRRes l E Z h
  scalarY : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientFiniteQuotientDerived l E Y h ⊣ normalizedDVRRes l E Y h
  ordinaryCoefficientComparison : ∀ {m n : ℕ} (h : n ≤ m),
    normalizedDVRModuleRes l E Z h ⋙ compactSupportLevelDirectImage l E p m ≅
      compactSupportLevelDirectImage l E p n ⋙ normalizedDVRModuleRes l E Y h
  derivedCoefficientComparison : ∀ {m n : ℕ} (h : n ≤ m),
    normalizedDVRRes l E Z h ⋙
        (compactSupportLevelDirectImage l E p m).rightDerivedFunctor ≅
      (compactSupportLevelDirectImage l E p n).rightDerivedFunctor ⋙
        normalizedDVRRes l E Y h

attribute [instance_reducible, instance] CompactSupportSystemCanonicalOperations.instances

/-- The inherited exactness component for the actual finite open operation.
Source: node proof step 3, Stacks 03DI--03DJ
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
instance compactSupportFiniteExtensionPreservesFiniteLimits
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    PreservesFiniteLimits (IntegralOpenReduction.finiteExtension l E j o n) :=
  letI := o.finiteAdditive n
  letI := SheafOfModules.localizedSystemExtensionLimits.{t+1, t, max u (t+1)}
    (integralCoefficientCommRingSheaf l E Z n) (IntegralOpenReduction.openObject j)
  inferInstance

/-- The inherited exactness component for the actual finite open operation.
Source: node proof step 3, Stacks 03DI--03DJ
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
instance compactSupportFiniteExtensionPreservesFiniteColimits
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    PreservesFiniteColimits (IntegralOpenReduction.finiteExtension l E j o n) :=
  letI := o.finiteAdditive n
  letI := SheafOfModules.localizedSystemExtensionColimits.{t+1, t, max u (t+1)}
    (integralCoefficientCommRingSheaf l E Z n) (IntegralOpenReduction.openObject j)
  inferInstance

/-- The inherited exactness component for the actual finite open operation.
Source: node proof step 3, Stacks 03DI--03DJ
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
instance compactSupportFiniteRestrictionAdditive
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    (IntegralOpenReduction.finiteRestriction l E j o n).Additive :=
  letI := o.finiteAdditive n
  letI := SheafOfModules.localizedSystemRestrictionAdditive.{t+1, t, max u (t+1)}
    (integralCoefficientCommRingSheaf l E Z n) (IntegralOpenReduction.openObject j)
  inferInstance

/-- The inherited exactness component for the actual finite open operation.
Source: node proof step 3, Stacks 03DI--03DJ
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
instance compactSupportFiniteRestrictionPreservesFiniteLimits
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    PreservesFiniteLimits (IntegralOpenReduction.finiteRestriction l E j o n) :=
  letI := o.finiteAdditive n
  letI := SheafOfModules.localizedSystemRestrictionLimits.{t+1, t, max u (t+1)}
    (integralCoefficientCommRingSheaf l E Z n) (IntegralOpenReduction.openObject j)
  inferInstance

/-- The inherited exactness component for the actual finite open operation.
Source: node proof step 3, Stacks 03DI--03DJ
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
instance compactSupportFiniteRestrictionPreservesFiniteColimits
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    PreservesFiniteColimits (IntegralOpenReduction.finiteRestriction l E j o n) :=
  letI := o.finiteAdditive n
  letI := SheafOfModules.localizedSystemRestrictionColimits.{t+1, t, max u (t+1)}
    (integralCoefficientCommRingSheaf l E Z n) (IntegralOpenReduction.openObject j)
  inferInstance

/-- The exact open extension at a finite level, from the actual slice presentation.
Source: node proof step 3, Stacks 03DI
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportCanonicalJLevel
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    normalizedDVRDerived l E X n ⥤ normalizedDVRDerived l E Z n :=
  (IntegralOpenReduction.finiteExtension l E j o n).mapDerivedCategory

/-- The finite open adjunction is the descent of the section-normalized slice adjunction.
Source: node proof step 3, Stacks 03DI, 015F
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportCanonicalJLevelAdjunction
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    compactSupportCanonicalJLevel l E j o n ⊣
      (IntegralOpenReduction.finiteRestriction l E j o n).mapDerivedCategory :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    ((o.finite n).toAdjunction.comp
      (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
        (integralCoefficientCommRingSheaf l E Z n) (IntegralOpenReduction.openObject j)))

/-- Exact open extension on whole systems.
Source: node proof step 3, Stacks 03DI, 0941
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportCanonicalJSystem
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Z :=
  IntegralOpenReduction.J l E j o

/-- The canonical localization of the actual ordinary extension evaluation.
Source: node proof step 3, Stacks 015F, 0941
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportCanonicalJEvaluation {X Z : Scheme.{t}} (j : X ⟶ Z)
    [IsOpenImmersion j] (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    compactSupportCanonicalJSystem l E j o ⋙ coefficientSequenceDerivedEvaluation l E Z n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙ compactSupportCanonicalJLevel l E j o n :=
  letI := coefficientSequenceEvaluation_additiveInstance l E X n
  letI := coefficientSequenceEvaluation_additiveInstance l E Z n
  letI := IntegralOpenReduction.systemExtensionAdditive l E j o
  letI := IntegralOpenReduction.finiteExtensionAdditive l E j o n
  letI := coefficientSequenceEvaluation_limits l E X n
  letI := coefficientSequenceEvaluation_colimits l E X n
  letI := coefficientSequenceEvaluation_limits l E Z n
  letI := coefficientSequenceEvaluation_colimits l E Z n
  letI := IntegralOpenReduction.systemExtensionLimits l E j o
  letI := IntegralOpenReduction.systemExtensionColimits l E j o
  letI := compactSupportFiniteExtensionPreservesFiniteLimits l E j o n
  letI := compactSupportFiniteExtensionPreservesFiniteColimits l E j o n
  Functor.mapDerivedCategoryCompIso (IntegralOpenReduction.systemExtension l E j o)
    (coefficientSequenceEvaluation l E Z n) ≪≫
  Functor.mapDerivedCategoryNatIso (IntegralOpenReduction.extensionEvaluation l E j o n) ≪≫
  (Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E X n)
    (IntegralOpenReduction.finiteExtension l E j o n)).symm

/-- Evaluation presentations for the canonical geometric functors. The right direct-image
comparison is normalized on arbitrary K-injective resolutions of evaluated systems;
evaluation itself is not assumed to preserve K-injectivity.
Source: node proof steps 2--3, Zheng 4.10
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
class CompactSupportSystemEvaluationData
    (X Z Y : Scheme.{t}) (j : X ⟶ Z) (p : Z ⟶ Y) [IsOpenImmersion j] where
  [operations : CompactSupportSystemCanonicalOperations l E j p]
  jLeftEvaluation : ∀ n : ℕ,
    compactSupportCanonicalJSystem l E j operations.instances.jOperations ⋙
        coefficientSequenceDerivedEvaluation l E Z n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙
        compactSupportCanonicalJLevel l E j operations.instances.jOperations n
  jRightEvaluation : ∀ n : ℕ,
    IntegralOpenReduction.P l E j operations.instances.jOperations ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Z n ⋙
        (IntegralOpenReduction.finiteRestriction l E j
          operations.instances.jOperations n).mapDerivedCategory
  pLeftEvaluation : ∀ n : ℕ,
    integralComparisonDerivedSequencePullback l E p ⋙
        coefficientSequenceDerivedEvaluation l E Z n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙
        (compactSupportLevelPullback l E p n).mapDerivedCategory
  pRightEvaluation : ∀ n : ℕ,
    (integralComparisonSequenceDirectImage l E p).rightDerivedFunctor ⋙
        coefficientSequenceDerivedEvaluation l E Y n ≅
      coefficientSequenceDerivedEvaluation l E Z n ⋙
        (compactSupportLevelDirectImage l E p n).rightDerivedFunctor
  pOrdinaryEvaluation : ∀ n : ℕ,
    integralComparisonSequenceDirectImage l E p ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E Z n ⋙ compactSupportLevelDirectImage l E p n

attribute [instance_reducible, instance] CompactSupportSystemEvaluationData.operations

/-- Evaluation of the real restricted compact-support system.
Source: node statement, `ev_n U_Y S_p J_j`
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportSystemSourceLevel
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] (n : ℕ) :
    coefficientSequenceDerived l E X ⥤ DerivedCategory (scalarReductionSource l E Y) :=
  (compactSupportCanonicalJSystem l E j D.operations.instances.jOperations ⋙
    (integralComparisonSequenceDirectImage l E p).rightDerivedFunctor) ⋙
      (coefficientSequenceDerivedRestriction l E Y ⋙ coefficientConstantTowerEvaluation l E Y n)

/-- The finite-level compact-support functor followed by the actual completed restriction.
Source: node statement, `T_n`
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportSystemTargetLevel
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] (n : ℕ) :
    coefficientSequenceDerived l E X ⥤ DerivedCategory (scalarReductionSource l E Y) :=
  (coefficientSequenceDerivedEvaluation l E X n ⋙
    compactSupportCanonicalJLevel l E j D.operations.instances.jOperations n) ⋙
      ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor ⋙
        coefficientFiniteDerivedRestriction l E Y n)

/-- The canonical composite `ev_n U = Res_n e_n`, direct-image evaluation, open evaluation.
Source: node statement, definition of `Theta`
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportSystemEvaluationIso
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] (n : ℕ) :
    compactSupportSystemSourceLevel l E (D := D) n ≅
      compactSupportSystemTargetLevel l E (D := D) n :=
by
  let i₁ := Functor.isoWhiskerLeft
    (compactSupportCanonicalJSystem l E j D.operations.instances.jOperations ⋙
      (integralComparisonSequenceDirectImage l E p).rightDerivedFunctor)
    (coefficientRestrictedEvaluationIso l E Y n)
  let i₂ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft
      (compactSupportCanonicalJSystem l E j D.operations.instances.jOperations)
      (D.pRightEvaluation n)) (coefficientFiniteDerivedRestriction l E Y n)
  let i₃ := Functor.isoWhiskerRight (D.jLeftEvaluation n)
    ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor ⋙
      coefficientFiniteDerivedRestriction l E Y n)
  simpa only [compactSupportSystemSourceLevel, compactSupportSystemTargetLevel,
    Functor.comp_assoc] using i₁ ≪≫ i₂ ≪≫ i₃

/-- The actual transition of a strict completed-coefficient tower, descended termwise.
Source: node statement, evaluation of the `ℕᵒᵖ` tower
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportConstantTowerTransition (W : Scheme.{t}) {m n : ℕ} (h : n ≤ m) :
    coefficientConstantTowerEvaluation l E W m ⟶ coefficientConstantTowerEvaluation l E W n :=
by
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  letI := HasDerivedCategory.standard (scalarReductionSource l E W)
  change ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op m)).mapDerivedCategory ⟶
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategory
  exact Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (ComplexShape.up ℤ)) _ _
    _ _
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE h).op)
        (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The source transition is evaluation of the actual restricted-system tower.
Source: node statement, tower `U_Y S_p J_j M`
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportSystemSourceTransition
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceDerived l E X) :
    (compactSupportSystemSourceLevel l E (D := D) m).obj M ⟶
      (compactSupportSystemSourceLevel l E (D := D) n).obj M :=
  (compactSupportConstantTowerTransition l E Y h).app
    ((coefficientSequenceDerivedRestriction l E Y).obj
      ((integralComparisonSequenceDirectImage l E p).rightDerivedFunctor.obj
        ((compactSupportCanonicalJSystem l E j D.operations.instances.jOperations).obj M)))

/-- The coefficient arrow `b` is the adjunction mate of the normalized actual restriction
square. This is the transpose of the inverse-image coefficient square of Zheng 4.10.
Source: node statement, `b_(m,n)` and proof step 2
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportSystemCoefficientMate
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] {m n : ℕ} (h : n ≤ m) :
    (compactSupportLevelDirectImage l E p m).rightDerivedFunctor ⋙
        coefficientFiniteQuotientDerived l E Y h ⟶
      coefficientFiniteQuotientDerived l E Z h ⋙
        (compactSupportLevelDirectImage l E p n).rightDerivedFunctor :=
  ((mateEquiv (D.operations.scalarZ h) (D.operations.scalarY h)).symm
    (TwoSquare.mk _ _ _ _ (D.operations.derivedCoefficientComparison h).hom))

/-- Successive restrictions equal restriction along the actual limit projection.
Source: node statement, `Res_m Res_(m,n) = Res_n`, proof step 5
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportSystemRestrictionComp (W : Scheme.{t}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E W h ⋙ coefficientFiniteDerivedRestriction l E W m ≅
      coefficientFiniteDerivedRestriction l E W n :=
  Functor.mapDerivedCategoryCompIso (normalizedDVRModuleRes l E W h)
    (scalarReductionRestriction l E W m) ≪≫
  Functor.mapDerivedCategoryNatIso (eqToIso (coefficientRestrictionComp l E W h))

/-- The extension-form transition `Rp_n(t^N) ∘ b`, for the actual system `N = J_j M`.
Its `t^N` is the adjunct of `coefficientSequenceDerivedTransition`, not a free map.
Source: node statement, displayed transition formula
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportSystemExtensionTransition
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceDerived l E X) :
    (coefficientFiniteQuotientDerived l E Y h).obj
      ((compactSupportLevelDirectImage l E p m).rightDerivedFunctor.obj
        ((coefficientSequenceDerivedEvaluation l E Z m).obj
          ((compactSupportCanonicalJSystem l E j D.operations.instances.jOperations).obj M))) ⟶
    (compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj
      ((coefficientSequenceDerivedEvaluation l E Z n).obj
        ((compactSupportCanonicalJSystem l E j D.operations.instances.jOperations).obj M)) :=
  (compactSupportSystemCoefficientMate l E (D := D) h).app
    ((coefficientSequenceDerivedEvaluation l E Z m).obj
      ((compactSupportCanonicalJSystem l E j D.operations.instances.jOperations).obj M)) ≫
  (compactSupportLevelDirectImage l E p n).rightDerivedFunctor.map
    (((D.operations.scalarZ h).homEquiv _ _).symm
      ((coefficientSequenceDerivedTransition l E Z h).app
        ((compactSupportCanonicalJSystem l E j D.operations.instances.jOperations).obj M)))

/-- The target transition is `Res_m` of the scalar-adjunction transpose of
`Rp_n(t^N) ∘ b`. The two open-evaluation maps only identify `e_n N` with `j_! e_n M`.
Source: node statement, displayed transition formula and proof step 4
(blueprint: def-trf-compact-support-system-evaluation-diagram). -/
def compactSupportSystemTargetTransition
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceDerived l E X) :
    (compactSupportSystemTargetLevel l E (D := D) m).obj M ⟶
      (compactSupportSystemTargetLevel l E (D := D) n).obj M :=
  (coefficientFiniteDerivedRestriction l E Y m).map
    ((compactSupportLevelDirectImage l E p m).rightDerivedFunctor.map
      ((D.jLeftEvaluation m).inv.app M) ≫
      ((D.operations.scalarY h).homEquiv _ _)
        (compactSupportSystemExtensionTransition l E (D := D) h M)) ≫
  (compactSupportSystemRestrictionComp l E Y h).hom.app
    ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj
      ((coefficientSequenceDerivedEvaluation l E Z n).obj
        ((compactSupportCanonicalJSystem l E j D.operations.instances.jOperations).obj M))) ≫
  (coefficientFiniteDerivedRestriction l E Y n).map
    ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.map
      ((D.jLeftEvaluation n).hom.app M))

end WeilConjectures
