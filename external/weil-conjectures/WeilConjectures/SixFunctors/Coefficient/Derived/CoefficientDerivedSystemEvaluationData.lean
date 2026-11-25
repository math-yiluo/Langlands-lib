/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.Coefficient.CoefficientReductionUnitPresentation
public import WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteQuotientModels
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTower
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import WeilConjectures.SixFunctors.Coefficient.CoefficientTotalTensorEvaluation
import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair
import WeilConjectures.CategoryTheory.ScalarHomTensor.PrescribedScalarTensorComparison
import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearEvaluationAcyclicLift
import all WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
/-! # Interfaces and representative calculations for coefficient-system evaluation

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 0A95 and 0941;
Injectives, Tag 079P (blueprint: def-coef-derived-system-calculus-data).

This file contains the existing calculus interfaces and their representative lemmas.
The existence theorem is assembled in `CoefDerivedSystemEvaluationCalculus` from
resolution models and projection comparisons. The final closed-adjunction lemmas
identify the existing evaluation-defined map with the five-bijection comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 128
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Use coefficient-universe sheafification: the generic instance requires a successor.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v a b r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive

section StandardCoefficientInstances

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] preadditiveCoyoneda SheafOfModules.unit
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
attribute [local irreducible] coefficientOrdinaryScalarAdjunction
attribute [local irreducible] coefficientOrdinaryQuotientNaturalTransformation
attribute [local irreducible] scalarReductionExtension
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] coefficientLocalizedCounitModel
attribute [local irreducible] coefficientFiniteReductionModel
attribute [local irreducible] CoefficientComparisonEquation CoefficientTransitionEquation
attribute [local irreducible] coefficientComplexCompositeTransformation
attribute [local irreducible] coefficientComplexCompositeSourceTransformation
attribute [local irreducible] coefficientActualScalarDerivedPair
attribute [local irreducible] coefficientUniqueComparisonChoice

/-- Evaluation on sections, including the canonical coefficient-ring transport.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientEvaluationSection
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    ((coefficientSequenceEvaluation l E W n).obj M).val.obj U :=
  (eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U).symm) x

set_option backward.defeqAttrib.useBackward false in
/-- Ordinary tensor evaluation is uniquely fixed on the actual sectionwise tensor generators.
Source: Stacks 03EK, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: restrict the tensor presheaf to the vertical slice and send x tensor y to
x tensor y. Vertical sheafification is the original site's sheafification, so this
gives an isomorphism of sheaf tensors. Evaluation preserves coproducts and is exact;
the comparisons assemble over total-degree summands, with the same signs in both
differentials. Generators before sheafification determine every component uniquely. -/
theorem coefficientEvaluationTensorIso_exists (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    ∃! e : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((coefficientTotalTensor.{u, t+1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      ∀ (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
        (x : (P.X p).val.obj (op (n, U.unop)))
        (y : (Q.X q).val.obj (op (n, U.unop))),
      (e.hom.f k).val.app U
        (coefficientEvaluationSection l E W _ n U
          (coefficientTensorGenerator.{u, t+1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) P Q p q k h
            (op (n, U.unop)) x y)) =
        coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q k h U
          (coefficientEvaluationSection l E W (P.X p) n U x)
          (coefficientEvaluationSection l E W (Q.X q) n U y) := by
  -- Supply the already elaborated theorem to the kernel with its local arguments.
  -- Re-elaborating this application expands the coefficient site's large instances.
  run_tac Lean.Elab.Tactic.withMainContext do
    let get (n : Lean.Name) : Lean.Elab.Tactic.TacticM Lean.Expr := do
      return (← Lean.Meta.getLocalDeclFromUserName n).toExpr
    let l ← get `l
    let E ← get `E
    let W ← get `W
    let n ← get `n
    let P ← get `P
    let Q ← get `Q
    let getInst (head : Lean.Name) : Lean.Elab.Tactic.TacticM Lean.Expr := do
      for decl in ← Lean.getLCtx do
        if decl.type.isAppOf head then return decl.toExpr
      Lean.throwError "missing local instance {head}"
    let as ← getInst ``Fact
    let fs ← getInst ``Field
    let alg ← getInst ``Algebra
    let fd ← getInst ``FiniteDimensional
    let .sort (.succ u) ← Lean.Meta.inferType E | Lean.throwError "field universe absent"
    let .const _ (t :: _) := (← Lean.Meta.inferType W).getAppFn |
      Lean.throwError "scheme universe absent"
    let info ← Lean.getConstInfo ``coefficientTotalTensorEvaluation_existsUnique
    let levels := info.levelParams.map fun name ↦ if name == `t then t else u
    let th := Lean.mkConst ``coefficientTotalTensorEvaluation_existsUnique levels
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN th #[l, as, E, fs, alg, fd, W, n, P, Q])
    Lean.Elab.Tactic.replaceMainGoal []

/-- The unique ordinary evaluation tensor comparison, fixed before deriving.
Source: Stacks 03EK, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientEvaluationTensorIso (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  coefficientUniqueComparisonChoice (coefficientEvaluationTensorIso_exists l E W n P Q)

attribute [local irreducible] coefficientScalarTensorIso coefficientEvaluationTensorIso

attribute [local semireducible] coefficientTotalTensor in
/-- Evaluation and finite scalar extension preserve the K-flat models in use.
Source: Stacks 06YN, 07A4, 0941
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: scalar extension carries a flat-term K-flat complex to a flat-term K-flat
complex by the tensor/restriction adjunction and associativity. For evaluation,
test acyclicity using induction from a level on the ringed sequence site; the
finite-prefix induction formula and exactness of evaluation give the K-flat test.
The same sheafified tensor computation preserves flatness term by term. -/
theorem coefficientTensorModelPreservation :
    (∀ (P : CochainComplex (scalarReductionSource l E W) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P →
      ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ∧
    (∀ (P : CochainComplex (coefficientSequenceModules l E W) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) P →
      ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) := by
  constructor
  · intro P hP n
    let (R : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}) :
        HasDerivedCategory.{max (t + 2) (u + 1)} (SheafOfModules.scalarModules
          (Scheme.ProEt.topology W) R) := HasDerivedCategory.standard _
    let : (show SheafOfModules.scalarModules (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⥤
          SheafOfModules.scalarModules (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)
        from scalarReductionExtension l E W n).Additive :=
      coefficientFiniteExtensionAdditive l E W n
    exact CategoryTheory.ScalarHomTensor.pair_preservesKFlat_with_extension.{t+1, t, u,
      max (t+2) (u+1)}
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (coefficientActualScalarDerivedPair l E W n)
      (scalarReductionExtension l E W n)
      (coefficientActualScalarDerivedPair_extension l E W n) P hP
  · intro P hP n
    let J := Scheme.ProEt.topology W
    let A := integralCoefficientCommRingSheaf l E W
    let R := coefficientSequenceCommRingSheaf l E W
    let B := A n
    let F := coefficientSequenceEvaluation l E W n
    intro Z hZ
    have hLift : ∃ L : CochainComplex (coefficientSequenceModules l E W) ℤ,
        L.Acyclic ∧ Nonempty (((F.mapHomologicalComplex (.up ℤ)).obj L) ≅ Z) := by
      apply SheafOfModules.semilinearEvaluation_acyclicLift.{t+1, t, max u (t+1)}
      exact hZ
    obtain ⟨L, hL, ⟨eL⟩⟩ := hLift
    have hT := hP L hL
    have hE : ((F.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t+1, t} (coefficientSequenceTopology J) R).obj
          (L, P))).Acyclic := by
      intro i
      exact (hT i).map F
    let e := coefficientEvaluationTensorIso l E W n L P
    have hS : ((coefficientTotalTensor.{u, t+1, t} J B).obj
        (((F.mapHomologicalComplex (.up ℤ)).obj L),
          ((F.mapHomologicalComplex (.up ℤ)).obj P))).Acyclic := by
      intro i
      exact (hE i).of_iso e
    let e' := (coefficientTotalTensor.{u, t+1, t} J B).mapIso
      (eL.prod (Iso.refl ((F.mapHomologicalComplex (.up ℤ)).obj P)))
    intro i
    exact (hS i).of_iso e'

set_option backward.defeqAttrib.useBackward false

attribute [local irreducible] coefficientKFlatInclusion
  CoefficientTensorModels.iso coefficientBaseChangeHom coefficientEnrichedAdjunctionMap
  CoefficientClosedStructure.tensor CoefficientClosedStructure.transpose
  CoefficientClosedStructure.evaluation CoefficientClosedStructure.composition
  CoefficientReductionModels CoefficientScalarTensorGenerators

attribute [local irreducible] coefficientOrdinaryQuotient
  coefficientOrdinaryQuotientComponent

attribute [local irreducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.instCategory HomologicalComplex.instCategory
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite
  SheafOfModules.siteSheafTensorRight
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex.mapBifunctorMap
  HomologicalComplex₂.total HomologicalComplex.single

set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

/-- Full data and identities of the coherent coefficient evaluation calculus.
The fields spell out each conclusion of the node. The normalized-system hypotheses
occur only where the node uses them; reduction and beta allow arbitrary ambient inputs.
Source: Stacks 06YS, 0A95, 0941, 079P and the agent-formulated enriched adjunction
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemTensors where
  /-- Closed derived tensor-Hom on completed coefficients. -/
  integralClosed : CoefficientClosedStructure (coefficientIntegralInternalHom l E W)
  /-- The tensor here is the ordinary K-flat derived tensor. -/
  integralTensorModel : CoefficientTensorModels.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) integralClosed
  /-- Closed derived tensor-Hom on the actual strict system category. -/
  systemClosed : CoefficientClosedStructure (coefficientSequenceInternalHom l E W)
  /-- The system tensor is derived before taking finite evaluations. -/
  systemTensorModel : CoefficientTensorModels.{u, t+1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) systemClosed
  /-- Closed derived tensor-Hom at every positive finite level. -/
  finiteClosed : ∀ n : ℕ, CoefficientClosedStructure (coefficientFiniteInternalHom l E W n)
  /-- Each finite tensor is the recorded total tensor on K-flat representatives. -/
  finiteTensorModel : ∀ n : ℕ, CoefficientTensorModels.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n) (finiteClosed n)

section ModelInterfaceCache

/-- Integral K-flat tensor comparison in the displayed coefficient category.
Source: Stacks 06YU (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientIntegralTensorModelIso
    (S : CoefficientDerivedSystemTensors l E W)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q) :
    DerivedCategory.Q.obj (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj ((P), (Q)))) ≅
      S.integralClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  CoefficientTensorModels.iso (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed
    S.integralTensorModel P Q hP hQ

/-- System K-flat tensor comparison in the displayed coefficient category.
Source: Stacks 06YU (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientSystemTensorModelIso
    (S : CoefficientDerivedSystemTensors l E W)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) Q) :
    DerivedCategory.Q.obj (((coefficientTotalTensor.{u, t+1, t} (coefficientSequenceTopology
      (Scheme.ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)).obj ((P), (Q)))) ≅
      S.systemClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  CoefficientTensorModels.iso (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) S.systemClosed S.systemTensorModel P Q hP hQ

attribute [local instance 2000] HasDerivedCategory.standard in
/-- Finite K-flat tensor comparison in the displayed coefficient category.
Source: Stacks 06YU (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteTensorModelIso
    (S : CoefficientDerivedSystemTensors l E W) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n) Q) :
    DerivedCategory.Q.obj (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).obj ((P), (Q)))) ≅
      (S.finiteClosed n).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  CoefficientTensorModels.iso (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n)
    (S.finiteTensorModel n) P Q hP hQ

end ModelInterfaceCache
attribute [local irreducible] coefficientIntegralTensorModelIso
  coefficientSystemTensorModelIso coefficientFiniteTensorModelIso

-- The finite-quotient models are re-exported from their independent scalar module.
attribute [local irreducible] coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerivedExistence coefficientFiniteQuotientModel

/-- Finite-quotient adjunction and tensor data, with both normalizations on representatives.
The ordinary unit is the actual sheafified 1 tensor x. The derived unit uses the
universal counit, and the tensor comparison preserves the same local pure tensors.
Source: Stacks 03CZ, 06YY, 07A4, 07A6, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientFiniteQuotientData (S : CoefficientDerivedSystemTensors l E W) where
  /-- Ordinary quotient extension is adjoint to the recorded exact scalar restriction. -/
  ordinaryAdjunction : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientFiniteQuotientExtension l E W h ⊣ normalizedDVRModuleRes l E W h
  /-- The derived quotient adjunction uses that same scalar restriction. -/
  adjunction : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientFiniteQuotientDerived l E W h ⊣ normalizedDVRRes l E W h
  /-- Quotient extension preserves K-flat representatives, without quotient-flatness. -/
  preservesKFlat : ∀ {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
      (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)
  /-- Strong tensor comparison used to reduce finite evaluation before transposing. -/
  tensor : ∀ {m n : ℕ} (h : n ≤ m),
    (S.finiteClosed m).tensor ⋙ coefficientFiniteQuotientDerived l E W h ≅
      (coefficientFiniteQuotientDerived l E W h).prod
        (coefficientFiniteQuotientDerived l E W h) ⋙ (S.finiteClosed n).tensor
attribute [local semireducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier in
/-- The ordinary scalar-unit section is sheafification of the module element 1 tensor x.
This general formula keeps coefficient constructions out of the sectionwise calculation.
Source: Stacks 03CZ, 03EK (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientChangeOfRingsUnitSection
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A B : Sheaf J CommRingCat.{max c v u}) (φ : A ⟶ B)
    (M : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (SheafOfModules.changeOfRings.{v, c, max c v u} φ M).val.obj V :=
  (toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v u} φ M).presheaf).app V
    ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app V).hom).unit.app (M.val.obj V) x)

attribute [local semireducible] SheafOfModules.instCategory in
/-- The actual finite-quotient tensor unit on a local section, with its scalar action displayed.
Source: Stacks 03CZ, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientUnitSection {m n : ℕ} (h : n ≤ m)
    (M : normalizedDVRModules l E W m) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((coefficientFiniteQuotientExtension l E W h).obj M).val.obj V :=
  (eqToHom (coefficientFiniteQuotientExtension_obj l E W h M).symm).val.app V
    (coefficientChangeOfRingsUnitSection.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W m) (integralCoefficientCommRingSheaf l E W n)
      (coefficientFiniteQuotient l E W h) M V x)

attribute [local semireducible] SheafOfModules.instCategory in
/-- The ordinary finite-quotient unit is actual sheafification of 1 tensor x.
Source: Stacks 03CZ, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteQuotientOrdinaryUnit (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientData l E W S) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m) (M : normalizedDVRModules l E W m)
    (V : W.ProEtᵒᵖ) (x : M.val.obj V),
    coefficientRestrictionSection (normalizedDVRQuotient l E W h)
      ((coefficientFiniteQuotientExtension l E W h).obj M) V
      (((D.ordinaryAdjunction h).unit.app M).val.app V x) =
        coefficientFiniteQuotientUnitSection l E W h M V x

/-- The derived finite-quotient unit is the localized ordinary unit through its counit.
Source: Stacks 06YY, 07A6, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteQuotientDerivedUnit (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientData l E W S) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P),
    (D.adjunction h).unit.app (DerivedCategory.Q.obj P) ≫
      (normalizedDVRRes l E W h).map (coefficientFiniteQuotientModel l E W h P hP).hom ≫
      (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.hom.app
        (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) =
    DerivedCategory.Q.map (((D.ordinaryAdjunction h).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app P)

/-- The representative tensor comparison square, for arbitrary coefficient categories.
Source: Stacks 07A4 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientTensorComparisonSquare
    {A : Type a} {B : Type b} {K : Type c}
    [Category.{v} A] [Category.{w} B] [Category.{r} K]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (F : A ⥤ B) (Q : K ⥤ B)
    {X Y Z : A} {X' Y' Z' N : K}
    (s : Z ⟶ T.obj (X, Y)) (μ : T ⋙ F ⟶ F.prod F ⋙ T')
    (p : F.obj X ⟶ Q.obj X') (q : F.obj Y ⟶ Q.obj Y')
    (z : F.obj Z ⟶ Q.obj Z') (e : Z' ⟶ N)
    (t : Q.obj N ⟶ T'.obj (Q.obj X', Q.obj Y')) : Prop :=
  F.map s ≫ μ.app (X, Y) ≫ T'.map (Prod.mkHom p q) = z ≫ Q.map e ≫ t

attribute [local irreducible] CoefficientTensorComparisonSquare

/-- The exact K-flat quotient tensor normalization, packaged once as a proposition.
Source: Stacks 06YY, 07A4, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteQuotientTensorNormalization (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientData l E W S) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
    (P Q : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) Q),
    ∃ e : ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W m)).obj ((P), (Q)))) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      CoefficientScalarTensorGenerators.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W m) (integralCoefficientCommRingSheaf l E W n)
        (coefficientFiniteQuotientExtension l E W h)
        (hF := coefficientFiniteQuotientExtensionAdditive l E W h)
        (coefficientFiniteQuotientUnitSection l E W h) P Q e ∧
      CoefficientTensorComparisonSquare (S.finiteClosed m).tensor
        (S.finiteClosed n).tensor (coefficientFiniteQuotientDerived l E W h) DerivedCategory.Q
        (coefficientFiniteTensorModelIso l E W S m P Q hP hQ).hom
        (D.tensor h).hom
        (coefficientFiniteQuotientModel l E W h P hP).hom
        (coefficientFiniteQuotientModel l E W h Q hQ).hom
        (coefficientFiniteQuotientModel l E W h _
          (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W m) P Q hP hQ)).hom e.hom
        (coefficientFiniteTensorModelIso l E W S n _ _
          (D.preservesKFlat h P hP) (D.preservesKFlat h Q hQ)).hom

attribute [local irreducible] CoefficientFiniteQuotientOrdinaryUnit
  CoefficientFiniteQuotientDerivedUnit CoefficientFiniteQuotientTensorNormalization

/-- Finite-quotient data together with its actual pure-tensor K-flat normalization.
Source: Stacks 06YY, 07A4, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientFiniteQuotientCalculus (S : CoefficientDerivedSystemTensors l E W)
    extends CoefficientFiniteQuotientData l E W S where
  /-- The ordinary unit is the actual image of 1 tensor x under sheafification. -/
  ordinary_unit : CoefficientFiniteQuotientOrdinaryUnit l E W S toCoefficientFiniteQuotientData
  /-- The derived unit is the localized ordinary unit under the universal counit. -/
  unit_model : CoefficientFiniteQuotientDerivedUnit l E W S toCoefficientFiniteQuotientData
  /-- On K-flat representatives this is the ordinary pure-tensor chain isomorphism. -/
  tensor_model : CoefficientFiniteQuotientTensorNormalization l E W S
    toCoefficientFiniteQuotientData

/-- The actual transition-adjoint under the normalized finite-quotient adjunction.
Source: Stacks 07A6, 0941, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientSequenceTransitionAdjoint (_S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W _S) {m n : ℕ} (h : n ≤ m)
    (N : coefficientSequenceDerived l E W) :
    (coefficientFiniteQuotientDerived l E W h).obj
        ((coefficientSequenceDerivedEvaluation l E W m).obj N) ⟶
      (coefficientSequenceDerivedEvaluation l E W n).obj N :=
  ((D.adjunction h).homEquiv _ _).symm ((coefficientSequenceDerivedTransition l E W h).app N)

/-- The normalization criterion makes precisely this transition-adjoint invertible.
Source: Stacks 07A6, 0941, node proof steps 5 and 10
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: under the finite-quotient adjunction, precomposition by this adjunct is the
map f ↦ tau ≫ Res(f). The recorded normalization makes that map bijective for every
target. Yoneda therefore makes the adjunct an isomorphism, including m = n. -/
theorem coefficientSequenceTransitionAdjoint_isIso (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    IsIso (coefficientSequenceTransitionAdjoint l E W S D h N) := by
  apply isIso_of_coyoneda_map_bijective
  intro P
  apply Function.Bijective.of_comp_left
    (f := (D.adjunction h).homEquiv _ P)
  · simpa only [Function.comp_def, coefficientSequenceTransitionAdjoint,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] using hN h P
  · exact ((D.adjunction h).homEquiv _ P).injective

/-- The normalization isomorphism alpha is the actual transition-adjoint.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientSequenceNormalizationIso (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    (coefficientFiniteQuotientDerived l E W h).obj
        ((coefficientSequenceDerivedEvaluation l E W m).obj N) ≅
      (coefficientSequenceDerivedEvaluation l E W n).obj N :=
  letI := coefficientSequenceTransitionAdjoint_isIso l E W S D h N hN
  asIso (coefficientSequenceTransitionAdjoint l E W S D h N)

attribute [local irreducible] coefficientSequenceNormalizationIso

/-- The comparison c_(m,n) is reduced finite evaluation followed by tensor-Hom transpose.
Its tensor comparison is pinned to ordinary pure tensors by D.tensor_model.
Source: Stacks 08J9, 06YY, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientHomComparison (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    (P Q : normalizedDVRDerived l E W m) :
    (coefficientFiniteQuotientDerived l E W h).obj
        ((coefficientFiniteInternalHom l E W m).obj (op P, Q)) ⟶
      (coefficientFiniteInternalHom l E W n).obj
        (op ((coefficientFiniteQuotientDerived l E W h).obj P),
          (coefficientFiniteQuotientDerived l E W h).obj Q) :=
  coefficientBaseChangeHom (S.finiteClosed m) (S.finiteClosed n)
    (coefficientFiniteQuotientDerived l E W h) (D.tensor h) P Q

attribute [local irreducible] coefficientFiniteQuotientHomComparison

/-- Reduction and its normalized adjunction on the actual derived coefficient categories.
Source: Stacks 06YY, 07A6, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemReductionModel extends CoefficientDerivedSystemTensors l E W where
  /-- The reduction is a functor on the ordinary unbounded derived category. -/
  reduction : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W
  /-- Adjunction to the specified total limit, including both triangle identities. -/
  adjunction : reduction ⊣ coefficientSequenceLimit l E W
  /-- Finite evaluation is actual derived scalar extension. -/
  reductionEvaluation : ∀ n : ℕ,
    reduction ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n
  /-- Computation on a single flat-term K-flat representative with strict quotient maps. -/
  reductionModel : CoefficientReductionModels l E W reduction reductionEvaluation
  /-- Every ambient complex reduces to a normalized system. -/
  reduction_normalized : ∀ P, IsNormalizedCoefficientSequence l E W (reduction.obj P)
/-- The actual unit/counit projections and monoidal comparisons of reduction.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemReduction
    extends CoefficientDerivedSystemReductionModel l E W where
  /-- The reconstruction unit projects to the actual derived reduction map. -/
  unit_projection : ∀ (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    adjunction.unit.app P ≫ (coefficientSequenceProjection l E W n).app (reduction.obj P) =
      (coefficientFiniteAdjunction l E W n).unit.app P ≫
        (coefficientFiniteDerivedRestriction l E W n).map ((reductionEvaluation n).inv.app P)
  /-- The evaluated counit is exactly the adjunct of the total-limit projection. -/
  counit_projection : ∀ (N : coefficientSequenceDerived l E W) (n : ℕ),
    (coefficientFiniteAdjunction l E W n).homEquiv _ _
      ((reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj N) ≫
        (coefficientSequenceDerivedEvaluation l E W n).map (adjunction.counit.app N)) =
      (coefficientSequenceProjection l E W n).app N
  /-- Tensor reduction comparison in the derived system category itself. -/
  reductionTensor : integralClosed.tensor ⋙ reduction ≅
    reduction.prod reduction ⋙ systemClosed.tensor
  /-- Tensor comparison for actual finite scalar extension. -/
  finiteTensor : ∀ n : ℕ,
    integralClosed.tensor ⋙ coefficientFiniteDerivedExtension l E W n ≅
      (coefficientFiniteDerivedExtension l E W n).prod
        (coefficientFiniteDerivedExtension l E W n) ⋙ (finiteClosed n).tensor
  /-- Exact coefficient evaluation commutes with the derived system tensor. -/
  evaluationTensor : ∀ n : ℕ,
    systemClosed.tensor ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      (coefficientSequenceDerivedEvaluation l E W n).prod
        (coefficientSequenceDerivedEvaluation l E W n) ⋙ (finiteClosed n).tensor
/-- Finite scalar tensor comparison is the localization of the uniquely normalized
ordinary comparison. The square includes all representative identifications.
Source: Stacks 07A4, 06YU (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteTensorNormalization (S : CoefficientDerivedSystemReduction l E W) : Prop :=
  ∀ (n : ℕ) (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    CoefficientTensorComparisonSquare S.integralClosed.tensor (S.finiteClosed n).tensor
      (coefficientFiniteDerivedExtension l E W n) DerivedCategory.Q
      (coefficientIntegralTensorModelIso l E W
        S.toCoefficientDerivedSystemTensors P Q hP hQ).hom
      (S.finiteTensor n).hom
      (coefficientFiniteReductionModel l E W P hP n).hom
      (coefficientFiniteReductionModel l E W Q hQ n).hom
      (coefficientFiniteReductionModel l E W _
        (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ) n).hom
      (coefficientScalarTensorIso l E W n P Q).hom
      (coefficientFiniteTensorModelIso l E W
        S.toCoefficientDerivedSystemTensors n _ _
        ((coefficientTensorModelPreservation l E W).1 P hP n)
        ((coefficientTensorModelPreservation l E W).1 Q hQ n)).hom

/-- Evaluation tensor comparison is induced on simultaneous K-flat representatives
by the uniquely characterized ordinary evaluation comparison.
Source: Stacks 07A4, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientEvaluationTensorNormalization (S : CoefficientDerivedSystemReduction l E W) :
    Prop :=
  ∀ (n : ℕ) (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) Q),
    CoefficientTensorComparisonSquare S.systemClosed.tensor (S.finiteClosed n).tensor
      (coefficientSequenceDerivedEvaluation l E W n) DerivedCategory.Q
      (coefficientSystemTensorModelIso l E W
        S.toCoefficientDerivedSystemTensors P Q hP hQ).hom
      (S.evaluationTensor n).hom
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P)
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app Q)
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app _)
      (coefficientEvaluationTensorIso l E W n P Q).hom
      (coefficientFiniteTensorModelIso l E W
        S.toCoefficientDerivedSystemTensors n _ _
        ((coefficientTensorModelPreservation l E W).2 P hP n)
        ((coefficientTensorModelPreservation l E W).2 Q hQ n)).hom

/-- Reduction tensor comparison evaluates to the same normalized scalar-extension
comparison, with the actual reduction and tensor-evaluation identifications.
Source: Stacks 07A4, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientReductionTensorEvaluation (S : CoefficientDerivedSystemReduction l E W) : Prop :=
  ∀ (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    CoefficientComparisonEquation
      ((coefficientSequenceDerivedEvaluation l E W n).map
        (S.reductionTensor.hom.app (P, Q)))
      ((S.evaluationTensor n).hom.app (S.reduction.obj P, S.reduction.obj Q))
      ((S.finiteClosed n).tensor.map
        (Prod.mkHom ((S.reductionEvaluation n).hom.app P)
          ((S.reductionEvaluation n).hom.app Q)))
      ((S.reductionEvaluation n).hom.app (S.integralClosed.tensor.obj (P, Q)))
      ((S.finiteTensor n).hom.app (P, Q))

attribute [local semireducible] CategoryTheory.Functor.mapHomologicalComplex
  SheafOfModules.instCategory in
/-- A single strict reduction presentation with all finite and horizontal identifications.
This is the presentation already required in CoefficientReductionModels, exposed so
that the tensor comparison can be specified on the very same presentations.
Source: Stacks 06YS, 06YY, 0941
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientReductionPresentation
    (S : CoefficientDerivedSystemReduction l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :
    Prop :=
  (∀ n : ℕ,
    CoefficientComparisonEquation
      ((coefficientSequenceDerivedEvaluation l E W n).map e.hom)
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C)
      (DerivedCategory.Q.map (κ n).hom)
      ((S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P))
      ((coefficientFiniteReductionModel l E W P hP n).hom)) ∧
  (∀ (m n : ℕ) (h : n ≤ m),
    CoefficientTransitionEquation
      (coefficientComplexCompositeTransformation
        (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientSequenceTransition l E W h) C)
      (((normalizedDVRModuleRes l E W h).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (κ n).hom)
      ((κ m).hom)
      (coefficientComplexCompositeTransformation
        (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientOrdinaryQuotient l E W h) P))

/-- Tensor representatives retain finite, horizontal and strict adjunction equations.
Source: Stacks 06YS, 06YY, 07A6, 0941
(blueprint: def-coef-derived-system-calculus-data). -/
abbrev CoefficientReductionTensorPresentation
    (S : CoefficientDerivedSystemReduction l E W) :=
  CoefficientStrictReductionTensorPresentation l E W S.reduction S.adjunction
    S.reductionEvaluation

/-- The reduction tensor map is induced by one strict chain map whose finite components
are the ordinary normalized scalar tensor maps. Its square is an equality in the
system derived category, before evaluation or taking a limit.
Source: Stacks 07A4, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientReductionTensorNormalization (S : CoefficientDerivedSystemReduction l E W) :
    Prop :=
  ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)) →
    ∃ (C D Z : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) C)
      (hD : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) D)
      (eC : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
      (eD : S.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj D)
      (eZ : S.reduction.obj (DerivedCategory.Q.obj
        (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj ((P), (Q))))) ≅
        DerivedCategory.Q.obj Z)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          D ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            Q)
      (κZ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          Z ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj ((P), (Q)))))
      (ψ : Z ⟶ (coefficientTotalTensor.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (C, D)),
      CoefficientReductionTensorPresentation l E W S P hP C eC κC ∧
      CoefficientReductionTensorPresentation l E W S Q hQ D eD κD ∧
      CoefficientReductionTensorPresentation l E W S _
        (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ) Z eZ κZ ∧
      (∀ n : ℕ,
        CoefficientComparisonEquation
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ)
          (coefficientEvaluationTensorIso l E W n C D).hom
          ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
              (Prod.mkHom (κC n).hom (κD n).hom))
          (κZ n).hom (coefficientScalarTensorIso l E W n P Q).hom) ∧
      CoefficientTensorComparisonSquare S.integralClosed.tensor S.systemClosed.tensor
        S.reduction DerivedCategory.Q
        (coefficientIntegralTensorModelIso l E W
          S.toCoefficientDerivedSystemTensors P Q hP hQ).hom
        S.reductionTensor.hom eC.hom eD.hom eZ.hom ψ
        (coefficientSystemTensorModelIso l E W
          S.toCoefficientDerivedSystemTensors C D hC hD).hom

/-- The actual internal-Hom transition under its fiber identifications.
This is the transition-adjoint formula for normalized inputs, using the finite quotient
comparison obtained by transposing reduced evaluation with its K-flat tensor normalization.
Source: Stacks 06YY, 07A6, 0941, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiberTransition (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S)
    (fiberHom : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)) : Prop :=
  ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) {m n : ℕ} (h : n ≤ m),
    coefficientSequenceTransitionAdjoint l E W S
        D h ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≫
      (fiberHom M N hM hN n).hom =
    (coefficientFiniteQuotientDerived l E W h).map ((fiberHom M N hM hN m).hom) ≫
      coefficientFiniteQuotientHomComparison l E W S
        D h ((coefficientSequenceDerivedEvaluation l E W m).obj M)
          ((coefficientSequenceDerivedEvaluation l E W m).obj N) ≫
      (coefficientFiniteInternalHom l E W n).map
        (Prod.mkHom ((coefficientSequenceNormalizationIso l E W
          S D h M hM).inv.op)
          (coefficientSequenceNormalizationIso l E W
            S D h N hN).hom)

attribute [local irreducible] CoefficientReductionTensorNormalization
  CoefficientReductionPresentation CoefficientReductionTensorEvaluation
  CoefficientFiniteTensorNormalization CoefficientEvaluationTensorNormalization
  CoefficientFiberTransition

/-- Coherent fibers and evaluation on the canonical reduction data.
Source: Stacks 0A95, 0941 and node proof steps 6--11
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemFibers extends CoefficientDerivedSystemReduction l E W where
  /-- Retain the finite constraint witnesses used to construct the tensor models. -/
  finite_tensor_coherence : ∀ n : ℕ,
    ∃ β : @SymmetricCategory (normalizedDVRDerived l E W n) _ (finiteClosed n).monoidal,
      Nonempty (RingedDerivedTensorCoherence.{t+1, t, u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (finiteClosed n) (finiteTensorModel n) β)
  /-- Reduction's tensor comparison has the simultaneous strict representative formula. -/
  reductionTensor_normalization : CoefficientReductionTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Finite tensor comparisons have their ordinary generator normalization. -/
  finiteTensor_normalization : CoefficientFiniteTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Evaluation tensor comparisons have their simultaneous representative normalization. -/
  evaluationTensor_normalization : CoefficientEvaluationTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Reduction uses precisely the normalized finite tensor comparisons at each level. -/
  reductionTensor_evaluation : CoefficientReductionTensorEvaluation l E W
    toCoefficientDerivedSystemReduction

  /-- Actual quotient scalar extension with its adjunction and K-flat tensor normalization. -/
  quotientCalculus : CoefficientFiniteQuotientCalculus l E W toCoefficientDerivedSystemTensors

  /-- Beta preserves evaluation, transposes and internal composition as system maps. -/
  reduction_compatible : CoefficientEvaluationCompatible integralClosed systemClosed
    reduction reductionTensor
  /-- Finite comparisons use the same evaluation-defined tensor-Hom calculus. -/
  finite_compatible : ∀ n : ℕ, CoefficientEvaluationCompatible integralClosed (finiteClosed n)
    (coefficientFiniteDerivedExtension l E W n) (finiteTensor n)
  /-- Internal Hom on normalized inputs has exactly the finite internal-Hom fibers. -/
  fiberHom : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- The fiber identification is induced by simultaneous system evaluation. -/
  fiber_evaluation : ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ),
    (evaluationTensor n).inv.app
        ((coefficientSequenceInternalHom l E W).obj (op M, N), M) ≫
      (coefficientSequenceDerivedEvaluation l E W n).map (systemClosed.evaluation M N) =
    (finiteClosed n).tensor.map
        (Prod.mkHom ((fiberHom M N hM hN n).hom) (𝟙 _)) ≫
      (finiteClosed n).evaluation
        ((coefficientSequenceDerivedEvaluation l E W n).obj M)
        ((coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- Fiberwise internal Hom is natural for input derived morphisms. -/
  fiber_naturality : ∀ (M N M' N' : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N)
    (hM' : IsNormalizedCoefficientSequence l E W M')
    (hN' : IsNormalizedCoefficientSequence l E W N') (f : M' ⟶ M) (g : N ⟶ N') (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        ((coefficientSequenceInternalHom l E W).map
        (Prod.mkHom (f.op) (g))) ≫
      (fiberHom M' N' hM' hN' n).hom =
    (fiberHom M N hM hN n).hom ≫ (coefficientFiniteInternalHom l E W n).map
      (Prod.mkHom (((coefficientSequenceDerivedEvaluation l E W n).map f).op)
        ((coefficientSequenceDerivedEvaluation l E W n).map g))
  /-- The adjunct of the actual `coefficientSequenceDerivedTransition` on internal Hom,
  under `fiberHom` at m and n, is c_(m,n) followed by RHom(alpha_M inverse, alpha_N).
  Here c_(m,n) transposes reduced finite evaluation using `quotientCalculus.tensor`,
  whose `tensor_model` fixes its comparison on every pair of K-flat representatives. -/
  fiber_transition : CoefficientFiberTransition l E W toCoefficientDerivedSystemTensors
    quotientCalculus fiberHom
  /-- Beta evaluates to the usual finite internal-Hom reduction comparison. -/
  beta_evaluation : ∀ (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        (coefficientBaseChangeHom integralClosed systemClosed reduction reductionTensor P Q) ≫
      (fiberHom _ _ (reduction_normalized P) (reduction_normalized Q) n).hom =
    (reductionEvaluation n).hom.app ((coefficientIntegralInternalHom l E W).obj (op P, Q)) ≫
      coefficientBaseChangeHom integralClosed (finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n) (finiteTensor n) P Q ≫
      (coefficientFiniteInternalHom l E W n).map
        (Prod.mkHom (((reductionEvaluation n).hom.app P).op) ((reductionEvaluation n).inv.app Q))
  /-- Joint conservativity on actual derived system maps. -/
  isIso_iff_evaluations : ∀ {M N : coefficientSequenceDerived l E W} (f : M ⟶ N),
    IsIso f ↔ ∀ n : ℕ, IsIso ((coefficientSequenceDerivedEvaluation l E W n).map f)
  /-- Total derived global sections of a system retain its finite fibers. -/
  globalEvaluation : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientMappingEvaluation.{max u (t+1)} n).obj
          ((coefficientSequenceGlobalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteGlobalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
/-- The full calculus additionally carries its enriched and global-limit comparisons.
Source: Stacks 08J9, 07A6, 0941 and node proof steps 12--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemCalculus extends CoefficientDerivedSystemFibers l E W where
  /-- Enriched adjunction is invertible, without asserting completeness of P or N. -/
  enriched_isIso : ∀ (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W), IsNormalizedCoefficientSequence l E W N →
    IsIso (coefficientEnrichedAdjunctionMap integralClosed systemClosed reduction adjunction
      reductionTensor P N)
  /-- Global sections commute with the specified total limit, naturally as derived functors. -/
  globalLimit : coefficientSequenceLimit l E W ⋙
      coefficientIntegralSections l E W ≅
    coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
        coefficientMappingLimit.{max u (t+1)}
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The global comparison gamma is the global sections of the specified enriched adjunct,
followed by the specified total-limit comparison. Thus its data are real composites.
Source: Stacks 08J9, 07A6, 0941 and node proof steps 12--14
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def CoefficientDerivedSystemCalculus.gamma
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    (coefficientIntegralGlobalHom l E W).obj
        (op P, (coefficientSequenceLimit l E W).obj N) ≅
      coefficientMappingLimit.{max u (t+1)}.obj
        ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N)) :=
  (coefficientIntegralSections l E W).mapIso
      (@asIso _ _ _ _
        (coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
          S.adjunction S.reductionTensor P N) (S.enriched_isIso P N hN)) ≪≫
    S.globalLimit.app
      ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))

/-- The lax tensor comparison of the right adjoint, defined by the counit mate.
Source: Stacks 07A6 and node proof step 15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def CoefficientDerivedSystemCalculus.tensorLimitMap
    (S : CoefficientDerivedSystemCalculus l E W)
    (T : DerivedCategory (scalarReductionSource l E W)) (N : coefficientSequenceDerived l E W) :
    S.integralClosed.tensor.obj (T, (coefficientSequenceLimit l E W).obj N) ⟶
      (coefficientSequenceLimit l E W).obj
        (S.systemClosed.tensor.obj (S.reduction.obj T, N)) :=
  S.adjunction.homEquiv _ _
    ((S.reductionTensor).hom.app (T, (coefficientSequenceLimit l E W).obj N) ≫
      S.systemClosed.tensor.map
        (Prod.mkHom (𝟙 (S.reduction.obj T)) (S.adjunction.counit.app N)))

private theorem preservedLimitComparison_existsUnique
    {A : Type a} [Category.{b} A] [HasLimitsOfShape ℕᵒᵖ A]
    (G : A ⥤ AddCommGrpCat.{w}) [PreservesLimitsOfShape ℕᵒᵖ G] :
    ∃! e : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ G ≅
      (Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G ⋙ lim,
      ∀ (T : ℕᵒᵖ ⥤ A) (n : ℕ),
        e.hom.app T ≫ (lim.π (op n)).app (T ⋙ G) =
          G.map ((lim.π (op n)).app T) := by
  refine ⟨preservesLimitNatIso G, ?_, ?_⟩
  · intro T n
    exact preservesLimitIso_hom_π G T (op n)
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext T
    apply limit.hom_ext
    intro n
    exact (he T n.unop).trans (preservesLimitIso_hom_π G T n).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Ordinary global sections commute with inverse limit by the actual projections.
Source: Stacks 0941 and node proof step 12
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: Hom from the module unit preserves limits. The ordinary comparison sends a
section of the limit to its compatible family of sections. The inverse uses the limit
universal property. These maps commute with all projections and determine each other
uniquely; the same characterization proves naturality in the tower. -/
theorem coefficientSectionsLimitIso_exists :
    ∃! e : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) ⋙
        coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) ≅
      coefficientTowerSections l E W ⋙
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) ⥤ AddCommGrpCat.{max u (t+1)}),
      ∀ (T : ℕᵒᵖ ⥤ scalarReductionSource l E W) (n : ℕ),
        e.hom.app T ≫ (lim.π (op n)).app ((coefficientTowerSections l E W).obj T) =
          (coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).map ((lim.π (op n)).app T) := by
  let G : scalarReductionSource l E W ⥤ AddCommGrpCat.{max u (t+1)} :=
    coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
  have : PreservesLimits G := CategoryTheory.preservesLimits_preadditiveCoyoneda_obj _
  have : PreservesLimitsOfSize.{0, 0} G := preservesLimitsOfSize_shrink G
  exact preservedLimitComparison_existsUnique G

/-- The unique ordinary sections/limit comparison used by the derived normalization.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientSectionsLimitIso :=
  (coefficientSectionsLimitIso_exists l E W).choose

/-- The left composite universal comparison, from ordinary sections of the ordinary limit.
Source: Stacks 079P, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientGlobalLimitLeftComparison
    (K : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :=
  coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      ((Functor.mapHomologicalComplex
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
        (ComplexShape.up ℤ)).obj K) ≫
    (coefficientIntegralSections l E W).map
        (coefficientRightDerivedComparison
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) K)

attribute [local semireducible] CategoryTheory.Functor.mapHomologicalComplex in
/-- The right composite universal comparison, after ordinary sections/limit commutation.
Source: Stacks 079P, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientGlobalLimitRightComparison
    (K : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :=
  DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (coefficientSectionsLimitIso l E W).hom
        (ComplexShape.up ℤ)).app K) ≫
    coefficientRightDerivedComparison
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) ⥤ AddCommGrpCat.{max u (t+1)})
      (((coefficientTowerSections l E W).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
    coefficientMappingLimit.{max u (t+1)}.map
      (coefficientRightDerivedComparison (coefficientTowerSections l E W) K)

/-- Scalar restriction preserves finite limits with the exact recorded functor.
Source: Stacks 03DA, 03CZ (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientFiniteRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (scalarReductionRestriction l E W n) :=
  (scalarReductionRestriction_exact l E W n).1

/-- Scalar restriction preserves finite colimits with the exact recorded functor.
Source: Stacks 03DA, 03CZ (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientFiniteRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (scalarReductionRestriction l E W n) :=
  (scalarReductionRestriction_exact l E W n).2

/-- Projection, resolution, naturality and composition normalizations for the calculus.
These equations specify gamma and its actual total-limit projections simultaneously.
Source: node proof steps 12--15, Stacks 08J9, 07A6, 0941
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemScalarData where
  /-- Global sections after scalar restriction have the canonical finite meaning. -/
  scalarSections : ∀ n : ℕ,
    coefficientFiniteDerivedRestriction l E W n ⋙
      coefficientIntegralSections l E W ≅
      coefficientFiniteSections l E W n
  /-- Ordinary scalar-section transport is fixed on actual section maps. -/
  ordinaryScalarSections : ∀ n : ℕ,
    scalarReductionRestriction l E W n ⋙
      coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ≅
    coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)

attribute [local semireducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.instCategory in
attribute [local semireducible] preadditiveCoyoneda SheafOfModules.unit in
/-- The ordinary section transport is characterized on all section maps.
Source: Stacks 03CZ, 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientOrdinaryScalarSectionsFormula
    (D : CoefficientDerivedSystemScalarData l E W) : Prop :=
  ∀ (n : ℕ) (M : scalarReductionTarget l E W n)
    (f : SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (scalarReductionRestriction l E W n).obj M)
    (V : W.ProEtᵒᵖ) (b : (integralCoefficientSheaf l E W n).obj.obj V),
    (((D.ordinaryScalarSections n).hom.app M) f).val.app V b = b • (@id (M.val.obj V) (f.val.app V
      (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj V)))

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local semireducible] CategoryTheory.Functor.mapHomologicalComplex
  SheafOfModules.instCategory in
/-- Compatibility of scalar-section transport with the universal derived comparisons.
Source: Stacks 079P, 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientScalarSectionsModel
    (D : CoefficientDerivedSystemScalarData l E W) : Prop :=
  ∀ (n : ℕ) (I : CochainComplex (scalarReductionTarget l E W n) ℤ),
    let G : scalarReductionTarget l E W n ⥤ AddCommGrpCat.{max u (t+1)} :=
      coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
    let : G.PreservesZeroMorphisms := by
      let : G.Additive := CategoryTheory.additive_coyonedaObj' _
      exact Functor.preservesZeroMorphisms_of_additive G
    CoefficientComparisonEquation
      (coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        (((scalarReductionRestriction l E W n).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))
      ((coefficientIntegralSections l E W).map
          ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app I))
      ((D.scalarSections n).hom.app (DerivedCategory.Q.obj I))
      (DerivedCategory.Q.map
      (coefficientComplexCompositeSourceTransformation
        (scalarReductionRestriction l E W n)
        (coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W))
        (H := G) (D.ordinaryScalarSections n).hom I))
      (coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) I)

attribute [local irreducible] CoefficientOrdinaryScalarSectionsFormula
  CoefficientScalarSectionsModel

/-- The canonical scalar-section comparisons and their resolution normalization.
Source: Stacks 03CZ, 079P, 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemScalarCoherence
    extends CoefficientDerivedSystemScalarData l E W where
  /-- The ordinary transport acts by the actual sectionwise adjunct. -/
  ordinaryScalarSections_formula : CoefficientOrdinaryScalarSectionsFormula l E W
    toCoefficientDerivedSystemScalarData
  /-- The derived comparison extends the ordinary transport on all complexes. -/
  scalarSections_model : CoefficientScalarSectionsModel l E W
    toCoefficientDerivedSystemScalarData

attribute [local semireducible] CategoryTheory.Functor.mapHomologicalComplex in
/-- The simultaneous-resolution equation for the actual global-limit comparison.
This is the original model equation, packaged once to avoid duplicating its large
localization terms in every generated structure declaration.
Source: Stacks 079P, 0941, node proof steps 12--14
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientGlobalLimitModel (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (K : CochainComplex (coefficientSequenceModules l E W) ℤ),
    CoefficientComparisonEquation
      (coefficientGlobalLimitLeftComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      ((coefficientIntegralSections l E W).map
          ((coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))
      (S.globalLimit.hom.app (DerivedCategory.Q.obj K))
      (coefficientGlobalLimitRightComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      (coefficientMappingLimit.{max u (t+1)}.map
        ((coefficientTowerSections l E W).rightDerivedFunctor.map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))

attribute [local irreducible] CoefficientGlobalLimitModel

/-- The resolution normalization of the global mapping-system comparisons.
Source: Stacks 079P, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemResolutionCoherence
    (S : CoefficientDerivedSystemCalculus l E W)
    extends CoefficientDerivedSystemScalarCoherence l E W where
  /-- Retain the normalized system tensor constraints of the resolution construction. -/
  systemTensorCoherence :
    ∃ β : @SymmetricCategory (coefficientSequenceDerived l E W) _ S.systemClosed.monoidal,
      Nonempty (RingedDerivedTensorCoherence.{t+1, t, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) S.systemClosed S.systemTensorModel β)
  /-- Derived termwise sections commute with evaluation, before taking internal Hom. -/
  systemSectionsEvaluation : ∀ n : ℕ,
    coefficientSequenceDerivedRestriction l E W ⋙
        (coefficientTowerSections l E W).rightDerivedFunctor ⋙
          coefficientMappingEvaluation.{max u (t+1)} n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙
        coefficientFiniteSections l E W n
  /-- The finite global-Hom identification is obtained from the actual internal-Hom fiber. -/
  globalEvaluation_model : ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ),
    (S.globalEvaluation M N hM hN n).hom =
      (systemSectionsEvaluation n).hom.app
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≫
        (coefficientFiniteSections l E W n).map ((S.fiberHom M N hM hN n).hom)
  /-- The global-limit comparison is the simultaneous derived ordinary comparison. -/
  globalLimit_model : CoefficientGlobalLimitModel l E W S
/-- The finite enriched isIso equation of the coefficient calculus.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteEnrichedIsIso (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (n : ℕ) (P : DerivedCategory (scalarReductionSource l E W))
    (M : normalizedDVRDerived l E W n),
    IsIso (coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
      (coefficientFiniteDerivedExtension l E W n) (coefficientFiniteAdjunction l E W n)
          (S.finiteTensor n) P M)

/-- The gamma projection equation of the coefficient calculus.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientGammaProjection (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S) : Prop :=
  ∀ (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N)
    (n : ℕ),
    (S.gamma l E W P N hN).hom ≫
      (coefficientMappingProjection.{max u (t+1)} n).app
        ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N)) ≫
      (S.globalEvaluation _ _ (S.reduction_normalized P) hN n).hom =
    (coefficientIntegralGlobalHom l E W).map
        (Prod.mkHom (𝟙 (op P)) ((coefficientSequenceProjection l E W n).app N)) ≫
      (coefficientIntegralSections l E W).map
        (coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
          (coefficientFiniteDerivedExtension l E W n) (coefficientFiniteAdjunction l E W n)
          (S.finiteTensor n)
          P ((coefficientSequenceDerivedEvaluation l E W n).obj N)) ≫
      (D.scalarSections n).hom.app ((coefficientFiniteInternalHom l E W n).obj
        (op ((coefficientFiniteDerivedExtension l E W n).obj P),
          (coefficientSequenceDerivedEvaluation l E W n).obj N)) ≫
      (coefficientFiniteGlobalHom l E W n).map
        (Prod.mkHom (((S.reductionEvaluation n).hom.app P).op)
          (𝟙 ((coefficientSequenceDerivedEvaluation l E W n).obj N)))

/-- The gamma naturality equation of the coefficient calculus.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientGammaNaturality (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (P P' : DerivedCategory (scalarReductionSource l E W))
    (N N' : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N)
    (hN' : IsNormalizedCoefficientSequence l E W N') (a : P' ⟶ P) (b : N ⟶ N'),
    (coefficientIntegralGlobalHom l E W).map
        (Prod.mkHom (a.op) ((coefficientSequenceLimit l E W).map b)) ≫
      (S.gamma l E W P' N' hN').hom =
    (S.gamma l E W P N hN).hom ≫ coefficientMappingLimit.{max u (t+1)}.map
      ((coefficientSequenceGlobalHom l E W).map
        (Prod.mkHom ((S.reduction.map a).op) (b)))

/-- The recorded additive identification of integral H⁰ RHom with derived morphisms.
Source: Stacks 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientIntegralHomEquiv
    (P Q : DerivedCategory (scalarReductionSource l E W)) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj (op P, Q))) ≃+ (P ⟶ Q) :=
  (coefficientHomZeroEquiv.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)) P Q

/-- The recorded additive identification of finite H⁰ RHom with derived morphisms.
Source: Stacks 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteHomEquiv (n : ℕ)
    (P Q : normalizedDVRDerived l E W n) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
      ((coefficientFiniteGlobalHom l E W n).obj (op P, Q))) ≃+ (P ⟶ Q) :=
  (coefficientHomZeroEquiv.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)) P Q

/-- The actual H⁰ map of gamma itself, before taking any mapping-limit projection.
Source: Stacks 07A6, 08JA, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientGammaZero
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
        ((coefficientIntegralGlobalHom l E W).obj (op P,
          (coefficientSequenceLimit l E W).obj N)) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
        (coefficientMappingLimit.{max u (t+1)}.obj
          ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N))) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).map
    (S.gamma l E W P N hN).hom

/-- The actual H⁰ map of gamma followed by its nth mapping-limit projection and
finite global-Hom identification. This is the map used in the degree-zero formula,
so the formula cannot be satisfied by an unrelated additive equivalence.
Source: Stacks 07A6, 08JA, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientGammaZeroMap
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
        ((coefficientIntegralGlobalHom l E W).obj (op P,
          (coefficientSequenceLimit l E W).obj N)) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
        ((coefficientFiniteGlobalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj
            (S.reduction.obj P)),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)) :=
  coefficientGammaZero l E W S P N hN ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).map
      ((coefficientMappingProjection.{max u (t+1)} n).app
          ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N)) ≫
        (S.globalEvaluation _ _ (S.reduction_normalized P) hN n).hom)

/-- The actual degree-zero map of gamma, followed by its actual nth projection,
under the recorded H⁰ RHom identifications, sends h to reduction of h followed
by the evaluated counit. Normalization of N is precisely gamma's domain condition.
Source: Stacks 07A6, 08JA, 0941 and node proof step 14
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientHomProjection (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N)
    (h : P ⟶ (coefficientSequenceLimit l E W).obj N) (n : ℕ),
    coefficientFiniteHomEquiv l E W n _ _
      ((coefficientGammaZeroMap l E W S P N hN n)
        ((coefficientIntegralHomEquiv l E W P _).symm h)) =
      (S.reductionEvaluation n).hom.app P ≫
        (coefficientFiniteDerivedExtension l E W n).map h ≫
        (S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj N) ≫
        (coefficientSequenceDerivedEvaluation l E W n).map (S.adjunction.counit.app N)

/-- The composition equation of the coefficient calculus.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientMappingComposition (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (T U P : DerivedCategory (scalarReductionSource l E W))
    (N N' : coefficientSequenceDerived l E W)
    (f : S.integralClosed.tensor.obj (T, P) ⟶ (coefficientSequenceLimit l E W).obj N)
    (g : S.systemClosed.tensor.obj (S.reduction.obj U, N) ⟶ N'),
    S.adjunction.homEquiv _ _
      ((S.reductionTensor).hom.app (U, S.integralClosed.tensor.obj (T, P)) ≫
        S.systemClosed.tensor.map
        (Prod.mkHom (𝟙 (S.reduction.obj U)) ((S.adjunction.homEquiv _ _).symm f)) ≫ g) =
    S.integralClosed.tensor.map
        (Prod.mkHom (𝟙 U) (f)) ≫ S.tensorLimitMap l E W U N ≫
      (coefficientSequenceLimit l E W).map g

attribute [local irreducible] CoefficientFiniteEnrichedIsIso CoefficientGammaProjection
  CoefficientGammaNaturality CoefficientHomProjection CoefficientMappingComposition

/-- The specified finite projections, naturality and composition of gamma.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemCoherence (S : CoefficientDerivedSystemCalculus l E W)
    extends CoefficientDerivedSystemResolutionCoherence l E W S where
  /-- finite enriched isIso. -/
  finite_enriched_isIso : CoefficientFiniteEnrichedIsIso l E W S
  /-- gamma projection. -/
  gamma_projection : CoefficientGammaProjection l E W S
    toCoefficientDerivedSystemResolutionCoherence
  /-- gamma naturality. -/
  gamma_naturality : CoefficientGammaNaturality l E W S
  /-- hom projection. -/
  hom_projection : CoefficientHomProjection l E W S
  /-- composition. -/
  composition : CoefficientMappingComposition l E W S

/-- The two normalization equations used to identify actual mapping projections.
The first is a sections/limit statement for an arbitrary system, before internal Hom.
The second is the finite scalar adjunction's action on H-zero, before any system limit.
Neither equation is a gamma projection assertion.
Source: Stacks 07A6, 08JA, 0941, 0D6E and the normalized derived comparison units
(blueprint: def-coef-derived-system-projection-models). -/
structure CoefficientDerivedSystemProjectionModels
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S) : Prop where
  /-- Sections of the actual total-limit projection have the specified finite meaning. -/
  sections_projection : ∀ (M : coefficientSequenceDerived l E W) (n : ℕ),
    S.globalLimit.hom.app M ≫
        (coefficientMappingProjection.{max u (t+1)} n).app
          ((coefficientSequenceDerivedRestriction l E W ⋙
            (coefficientTowerSections l E W).rightDerivedFunctor).obj M) ≫
        (D.systemSectionsEvaluation n).hom.app M =
      (coefficientIntegralSections l E W).map
          ((coefficientSequenceProjection l E W n).app M) ≫
        (D.scalarSections n).hom.app ((coefficientSequenceDerivedEvaluation l E W n).obj M)
  /-- The finite enriched scalar adjunct has the normalized action on H-zero. -/
  scalar_hom_zero : ∀ (n : ℕ)
    (P : DerivedCategory (scalarReductionSource l E W))
    (M : normalizedDVRDerived l E W n)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj
        (op P, (coefficientFiniteDerivedRestriction l E W n).obj M))),
    coefficientFiniteHomEquiv l E W n _ _
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).map
          ((coefficientIntegralSections l E W).map
              (coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
                (coefficientFiniteDerivedExtension l E W n)
                (coefficientFiniteAdjunction l E W n) (S.finiteTensor n) P M) ≫
            (D.scalarSections n).hom.app
              ((coefficientFiniteInternalHom l E W n).obj
                (op ((coefficientFiniteDerivedExtension l E W n).obj P), M))) x) =
      ((coefficientFiniteAdjunction l E W n).homEquiv P M).symm
        (coefficientIntegralHomEquiv l E W P _ x)

end StandardCoefficientInstances

section ClosedAdjunctionCalculus
set_option backward.defeqAttrib.useBackward true

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
  (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
  (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
  (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)

private theorem coefficientClosedEnriched_eq (P : A) (N : B) :
    coefficientEnrichedAdjunctionMap SA SB F adj μ P N =
      (ClosedScalarHom.iso SA SB adj μ).inv.app (op P, N) := by
  apply (cancel_mono ((ClosedScalarHom.iso SA SB adj μ).hom.app (op P, N))).mp
  rw [Iso.inv_hom_id_app]
  rw [← ClosedScalarHom.representing]
  unfold ClosedScalarHom.bijection coefficientEnrichedAdjunctionMap coefficientBaseChangeHom
  dsimp only [Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom]
  rw [Equiv.symm_apply_apply]
  have hn := (SB.adjunction (F.obj P)).homEquiv_naturality_right
    (μ.inv.app (HA.obj (op P, G.obj N), P) ≫ F.map (SA.evaluation P (G.obj N)))
    (adj.counit.app N)
  change SB.transpose _ _ _ (_ ≫ adj.counit.app N) =
    SB.transpose _ _ _ _ ≫ HB.map (Prod.mkHom (𝟙 _) (adj.counit.app N)) at hn
  dsimp only [Functor.prod_obj, Functor.comp_obj, Functor.id_obj] at hn
  have hk := (congrArg (SB.transpose (F.obj (HA.obj (op P, G.obj N)))
    (F.obj P) N).symm hn).symm.trans
      ((SB.transpose (F.obj (HA.obj (op P, G.obj N))) (F.obj P) N).symm_apply_apply _)
  refine (congrArg (fun z ↦ SA.transpose _ P (G.obj N)
    (adj.homEquiv _ N ((μ.app (HA.obj (op P, G.obj N), P)).hom ≫ z ≫ 𝟙 N))) hk).trans ?_
  have hm : μ.hom.app (HA.obj (op P, G.obj N), P) ≫
      ((μ.inv.app (HA.obj (op P, G.obj N), P) ≫
        F.map (SA.evaluation P (G.obj N))) ≫ adj.counit.app N) ≫ 𝟙 N =
      F.map (SA.evaluation P (G.obj N)) ≫ adj.counit.app N := by
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    exact Category.comp_id _
  refine (congrArg (fun z ↦ SA.transpose _ P (G.obj N)
    (adj.homEquiv _ N z)) hm).trans ?_
  change SA.transpose _ P (G.obj N)
    (adj.homEquiv _ N ((adj.homEquiv _ N).symm (SA.evaluation P (G.obj N)))) = _
  have h := (adj.homEquiv (SA.tensor.obj (HA.obj (op P, G.obj N), P)) N).apply_symm_apply
    (SA.evaluation P (G.obj N))
  refine (congrArg (SA.transpose _ P (G.obj N)) h).trans ?_
  change (SA.adjunction P).homEquiv _ _ ((SA.adjunction P).counit.app (G.obj N)) = 𝟙 _
  rw [← (SA.adjunction P).homEquiv_symm_id (G.obj N)]
  exact (SA.adjunction P).homEquiv _ _ |>.apply_symm_apply _

/-- The actual enriched adjunct is invertible for every tensor-preserving left adjoint.
Source: Stacks 07A6, 08J9; the five Hom bijections of
`CategoryTheory.ClosedScalarHom.iso`
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
theorem coefficientClosedEnriched_isIso (P : A) (N : B) :
    IsIso (coefficientEnrichedAdjunctionMap SA SB F adj μ P N) := by
  rw [coefficientClosedEnriched_eq]
  infer_instance

/-- Naturality of the evaluation-defined enriched adjunct in both derived inputs.
Source: Stacks 07A6, 08J9; naturality of the same five Hom bijections
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
theorem coefficientClosedEnriched_naturality (P P' : A) (N N' : B) (a : P' ⟶ P) (b : N ⟶ N') :
    HA.map (Prod.mkHom a.op (G.map b)) ≫
        coefficientEnrichedAdjunctionMap SA SB F adj μ P' N' =
      coefficientEnrichedAdjunctionMap SA SB F adj μ P N ≫
        G.map (HB.map (Prod.mkHom (F.map a).op b)) := by
  simp only [coefficientClosedEnriched_eq]
  exact (ClosedScalarHom.iso SA SB adj μ).inv.naturality (Prod.mkHom a.op b)

end ClosedAdjunctionCalculus

end WeilConjectures
