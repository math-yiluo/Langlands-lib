/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionComparison
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerFunctorSpec

/-! # Primitive integral realization with strict coefficient towers

Source: blueprint main-20261015, fix-prop-coherence.proof.md, primitive coefficient
comparisons; the five-step refinement in the DAG
(blueprint: def-sf-integral-basic-realization-data).

Only primitive operations occur here. Each domain below is the specialization of
Expression.domain to one operation and its inputs. Natural number n denotes the
positive exponent n+1 throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The input and output conditions of Expression.domain for one unary operation.
Source: fix-prop-coherence, intermediate-domain paragraph
(blueprint: def-sf-integral-basic-realization-data). -/
def basicUnaryDomain (X Y : Scheme.{u}) (A : System l E X ⥤ System l E Y) :
    ObjectProperty (Integral l E X) := fun K ↦
  sfIntegralConstructible l E X K ∧
    Good l E X ((calculus l E X).reduction.obj K) ∧
    Good l E Y (A.obj ((calculus l E X).reduction.obj K))

/-- Both inputs and the tensor output satisfy the recorded intermediate domain.
Source: fix-prop-coherence, two-input tensor clause
(blueprint: def-sf-integral-basic-realization-data). -/
def basicTensorDomain (W : Scheme.{u}) : ObjectProperty (Integral l E W × Integral l E W) :=
  fun K ↦ sfIntegralConstructible l E W K.1 ∧ sfIntegralConstructible l E W K.2 ∧
    Good l E W ((calculus l E W).reduction.obj K.1) ∧
    Good l E W ((calculus l E W).reduction.obj K.2) ∧
    Good l E W ((calculus l E W).systemClosed.tensor.obj
      ((calculus l E W).reduction.obj K.1, (calculus l E W).reduction.obj K.2))

/-- The compactification domain also retains the intermediate open-extension bound.
Source: fix-prop-coherence, chosen compactification paragraph
(blueprint: def-sf-integral-basic-realization-data). -/
def basicSupportDomain (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : ObjectProperty (Integral l E X) := fun K ↦
  basicUnaryDomain l E X Y (Operations.shriek l E o c.i ⋙ Operations.push l E o c.g) K ∧
    Good l E c.Z ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K))

/-- Inclusion of the primitive support domain into the recorded integral category.
Source: fix-prop-coherence, compact-support comparison domain
(blueprint: def-sf-integral-basic-realization-data). -/
def basicSupportInput (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (basicSupportDomain l E o c).FullSubcategory ⥤ sfIntegralConstructibleCategory l E X :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.1.1)

/-- Restrict a primitive operation's actual reduction/system/limit composite.
Source: fix-prop-coherence, displayed d_A
(blueprint: def-sf-integral-basic-realization-data). -/
def basicUnarySource (X Y : Scheme.{u}) (A : System l E X ⥤ System l E Y) :=
  (basicUnaryDomain l E X Y A).ι ⋙ (calculus l E X).reduction ⋙ A ⋙
    coefficientSequenceLimit l E Y

/-- Restrict the prescribed integral operation to the same full input domain.
Source: fix-prop-coherence, displayed d_A
(blueprint: def-sf-integral-basic-realization-data). -/
def basicUnaryTarget (X Y : Scheme.{u}) (A : System l E X ⥤ System l E Y)
    (B : Integral l E X ⥤ Integral l E Y) := (basicUnaryDomain l E X Y A).ι ⋙ B

end WeilConjectures.IntegralSystemRealization
