/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
public import WeilConjectures.SmoothPurity.PrimitiveCounit.PrimitiveCounitEvaluation

/-! # Quotient-limit realization and primitive coherent-counit comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok,
with the strict Roos normalization and the coherent coefficient-system adjunction
(blueprint: lem-pur-completed-primitive-counit-comparison).

Natural number n means positive coefficient exponent n+1. All systems are derived
before evaluation, and the site has independent object and morphism universes t+1 and t.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived

universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [local irreducible] Padic constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
namespace WeilConjectures
attribute [local irreducible] integralCompletedTensor integralCompletedTensorComparison
  integralDerivedPullback integralDerivedPullbackComparison
namespace PrimitiveCounit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.leftAdjoint inverseEvaluation inverse direct

/-- Termwise scalar restriction of a whole complex of systems.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
abbrev restrictComplex (W : Scheme.{t}) :=
  (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)

/-- Restriction evaluation on complexes through the recorded functor equality.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
def restrictEvaluation (W : Scheme.{t})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    ((restrictComplex l E W).obj C).asFunctor.obj (op n) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) :=
  (NatIso.mapHomologicalComplex
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ)).app C

/-- The actual termwise-limit identification for a complex of strict towers.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
def limitComplexIso (W : Scheme.{t})
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    limit I.asFunctor ≅
      (Functor.mapHomologicalComplex
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
        (.up ℤ)).obj I :=
  limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
    HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩

/-- The two existing Roos presentations are the same shifted product cone.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
def roosBridge (W : Scheme.{t})
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    integralOperationsRoosFunctor.obj Z.asFunctor ≅ roosF.obj Z := Iso.refl _

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted

attribute [local irreducible] roosF roosEval roosι limitComplexIso
  Functor.rightDerivedFunctorObjQIso

attribute [local implicit_reducible] SheafOfModules.instAbelian
  abelianOfAdjunction Abelian.ofCoimageImageComparisonIsIso
  scalarReductionSourceDerived scalarReductionTargetDerived
  coefficientConstantTowerDerived integralOperationsCommHasDerivedCategory
  integralTowerHasDerivedCategory integralCompletedRingHasDerivedCategory

attribute [local instance 5000] scalarReductionSourceDerived coefficientConstantTowerDerived

attribute [local irreducible] coefficientConstantTowerProjection
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence

/-- The natural Roos comparison type, kept folded in the realization record.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
def RoosComparison (W : Scheme.{t}) :=
  (roosF (A := scalarReductionSource l E W)) ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W

/-- The precise K-injective normalization of a proposed Roos comparison.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
def RoosResolution (W : Scheme.{t})
    (comparison : RoosComparison l E W) : Prop :=
  ∀ (Z I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (q : Z ⟶ I) [QuasiIso q] [I.IsKInjective],
    ∃ ι : DerivedCategory.Q.obj (limit I.asFunctor) ≅ DerivedCategory.Q.obj (roosF.obj I),
      ι.hom = DerivedCategory.Q.map (roosι I) ∧
      comparison.hom.app Z ≫
          (coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q) =
        DerivedCategory.Q.map (roosF.map q) ≫ ι.inv ≫
          DerivedCategory.Q.map (limitComplexIso l E W I).hom ≫
          (Functor.rightDerivedFunctorObjQIso
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) I).inv

/-- Compatibility with every actual finite limit projection.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
def RoosProjection (W : Scheme.{t}) (comparison : RoosComparison l E W) : Prop :=
  ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ),
    comparison.hom.app Z ≫
        (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj Z) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app Z =
      DerivedCategory.Q.map (roosEval Z n)

attribute [local irreducible] RoosResolution RoosProjection RoosComparison
  coefficientConstantTowerLimit

/-- A comparison with its two proof-valued normalization conditions. -/
structure NormalizedComparison (T : Type v) (P Q : T → Prop) where
  comparison : T
  projection : P comparison
  resolution : Q comparison

/-- One natural projection-compatible Roos realization, normalized on every resolution.
The actual inclusion roosι has zero shifted coordinate, as defined in StrictRoosModel.
Source: Stacks 0941 and lem-weil-strict-roos-comparison
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
abbrev RoosRealization (W : Scheme.{t}) : Type _ :=
  NormalizedComparison (RoosComparison l E W)
    (RoosProjection l E W) (RoosResolution l E W)

namespace RoosRealization
variable {l E}
abbrev mk {W : Scheme.{t}} (comparison : RoosComparison l E W)
    (projection : RoosProjection l E W comparison)
    (resolution : RoosResolution l E W comparison) : RoosRealization l E W :=
  ⟨comparison, projection, resolution⟩
abbrev comparison {W : Scheme.{t}} (ρ : RoosRealization l E W) :
    RoosComparison l E W := NormalizedComparison.comparison ρ
abbrev projection {W : Scheme.{t}} (ρ : RoosRealization l E W) :
    RoosProjection l E W ρ.comparison := NormalizedComparison.projection ρ
abbrev resolution {W : Scheme.{t}} (ρ : RoosRealization l E W) :
    RoosResolution l E W ρ.comparison := NormalizedComparison.resolution ρ
end RoosRealization

attribute [local semireducible] RoosComparison coefficientConstantTowerLimit

/-- The tensor primitive arrow is realization followed by the image of both counits.
Source: the beta_T formula of the node; Stacks 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def tensorBeta (W : Scheme.{t}) (S : CoefficientDerivedSystemReduction l E W)
    (r : integralCompletedTensor l E W ≅
      S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W)
    (A N : coefficientSequenceDerived l E W) :=
  r.hom.app ((coefficientSequenceLimit l E W).obj A,
    (coefficientSequenceLimit l E W).obj N) ≫
      (coefficientSequenceLimit l E W).map
        (S.systemClosed.tensor.map (Prod.mkHom (S.adjunction.counit.app A)
          (S.adjunction.counit.app N)))

/-- The geometric primitive arrow is realization followed by the image of the counit.
Source: the beta_F formula of the node; Stacks 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def pullBeta {X Y : Scheme.{t}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y)
    (r : integralDerivedPullback l E f ≅
      S.reduction ⋙ pull l E f ⋙ coefficientSequenceLimit l E X)
    (A : coefficientSequenceDerived l E Y) :=
  r.hom.app ((coefficientSequenceLimit l E Y).obj A) ≫
    (coefficientSequenceLimit l E X).map
      ((pull l E f).map (S.adjunction.counit.app A))

/-- The tensor representative comparison in the derived category of restricted towers.
Source: Stacks 07A4, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def tensorRestrictionIso (W : Scheme.{t}) (S : CoefficientDerivedSystemReduction l E W)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (C D : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) D)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj D) :
    (coefficientSequenceDerivedRestriction l E W).obj
        (S.systemClosed.tensor.obj (S.reduction.obj (DerivedCategory.Q.obj P),
          S.reduction.obj (DerivedCategory.Q.obj Q))) ≅
      DerivedCategory.Q.obj ((restrictComplex l E W).obj
        ((coefficientTotalTensor.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (C, D))) :=
  (coefficientSequenceDerivedRestriction l E W).mapIso
      (S.systemClosed.tensor.mapIso (eC.prod eD) ≪≫
        (S.systemTensorModel.iso (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) S.systemClosed C D hC hD).symm) ≪≫
    (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app _

/-- The geometric representative comparison in the derived category of restricted towers.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def pullRestrictionIso {X Y : Scheme.{t}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C) :
    (coefficientSequenceDerivedRestriction l E X).obj
        ((pull l E f).obj (S.reduction.obj (DerivedCategory.Q.obj P))) ≅
      DerivedCategory.Q.obj ((restrictComplex l E X).obj
        (((inverse l E f).mapHomologicalComplex (.up ℤ)).obj C)) :=
  (coefficientSequenceDerivedRestriction l E X).mapIso
      ((pull l E f).mapIso eC ≪≫ (inverse l E f).mapDerivedCategoryFactors.app C) ≪≫
    (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.app _

/-- The finite tensor presentation is the actual scalar restriction of the total tensor.
The map is the identity, retaining the recorded scalar extension and its quotient maps.
Source: Stacks 06YY, 07A4, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def finiteTensorBridge (W : Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n) :=
  by
    change ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
          (((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
            (.up ℤ)).obj P,
            ((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
              (.up ℤ)).obj Q))
    have h : unrestrictedIntegralReductionFunctor l E W n =
        scalarReductionExtension l E W n := by
      unfold unrestrictedIntegralReductionFunctor
      rfl
    let e := NatIso.mapHomologicalComplex (eqToIso h) (.up ℤ)
    exact ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).mapIso
          ((e.app P).symm.prod (e.app Q).symm))

attribute [local irreducible] integralOperationsTensorLevel coefficientTotalTensor
  integralOperationsRoosFunctor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The complex inverse-image evaluation induced by the unit-normalized ordinary one.
Source: Stacks 03D3, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def inverseComplexEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    (inverse l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ) ≅
    (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ) ⋙
      (integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ) :=
  by
    letI : (integralOperationsLevelPullback l E f n).Additive :=
      integralOperationsLevelPullback_additive l E f n
    exact (Functor.mapHomologicalComplexCompIso
      (F := inverse l E f) (G := coefficientSequenceEvaluation l E X n)
      (Iso.refl _) (.up ℤ)) ≪≫
      NatIso.mapHomologicalComplex (inverseEvaluation l E f n) (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (F := coefficientSequenceEvaluation l E Y n)
          (G := integralOperationsLevelPullback l E f n) (Iso.refl _) (.up ℤ)).symm

attribute [local irreducible] finiteTensorBridge restrictEvaluation inverseComplexEvaluation
  tensorRestrictionIso pullRestrictionIso roosBridge

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Tensor realization on every good pair uses the prescribed strict quotient tower.
The component formula for z pins its pure tensors through the existing ordinary
coefficient evaluation comparison and the canonical finite tensor presentation.
Source: Stacks 0941, proof steps 1--3 of the node
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def TensorModel (W : Scheme.{t}) (S : CoefficientDerivedSystemReduction l E W)
    (ρ : RoosRealization l E W)
    (r : integralCompletedTensor l E W ≅
      S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W) :
    Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
    ∃ (C D : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) C)
      (hD : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) D)
      (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
      (eD : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q.obj)
      (z : ((restrictComplex l E W).obj
        ((coefficientTotalTensor.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (C, D))).asFunctor ≅
        (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)),
      CoefficientReductionPresentation l E W S P.obj P.property.1 C eC κC ∧
      CoefficientReductionPresentation l E W S Q.obj Q.property.1 D eD κD ∧
      (∀ n : ℕ, z.hom.app (op n) =
        (restrictEvaluation l E W _ n).hom ≫
          ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
            ((coefficientEvaluationTensorIso l E W n C D).hom ≫
              (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
                (integralCoefficientCommRingSheaf l E W n)).map
                  (Prod.mkHom (κC n).hom (κD n).hom)) ≫
          (finiteTensorBridge l E W n P.obj Q.obj).hom) ∧
      (integralCompletedTensorComparison l E W).hom.app (P, Q) ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.mapIso z.symm).hom ≫
          DerivedCategory.Q.map (roosBridge l E W _).hom =
        r.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (coefficientConstantTowerLimit l E W).map
            (tensorRestrictionIso l E W S P.obj Q.obj C D hC hD eC eD).hom ≫
          ρ.comparison.inv.app _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Geometric realization on good representatives uses the actual pullback transitions.
Its strict tower comparison is fixed by the ordinary unit-normalized component maps.
Source: Stacks 0941, proof steps 1--3 of the node
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def PullModel {X Y : Scheme.{t}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y) (ρ : RoosRealization l E X)
    (r : integralDerivedPullback l E f ≅
      S.reduction ⋙ pull l E f ⋙ coefficientSequenceLimit l E X) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
    ∃ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj)
      (z : ((restrictComplex l E X).obj
        (((inverse l E f).mapHomologicalComplex (.up ℤ)).obj C)).asFunctor ≅
          (integralOperationsPullbackTowerFunctor l E f).obj P.obj),
      CoefficientReductionPresentation l E Y S P.obj P.property.1 C eC κC ∧
      (∀ n : ℕ, z.hom.app (op n) =
        (restrictEvaluation l E X _ n).hom ≫
          ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
            ((inverseComplexEvaluation l E f n).hom.app C ≫
              ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map
                (κC n).hom)) ∧
      (integralDerivedPullbackComparison l E f).hom.app P ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.mapIso z.symm).hom ≫
          DerivedCategory.Q.map (roosBridge l E X _).hom =
        r.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientConstantTowerLimit l E X).map
            (pullRestrictionIso l E f S P.obj C eC).hom ≫ ρ.comparison.inv.app _

attribute [local irreducible] TensorModel PullModel tensorBeta pullBeta

attribute [local instance 5000] SemilinearSections.hasDerived scalarReductionTargetDerived
attribute [local semireducible] constantSheaf

end PrimitiveCounit
end WeilConjectures
