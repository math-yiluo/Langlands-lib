/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
public import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData

import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedEssentialImage
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientDirectImageDiagrams
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackComparison
import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
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
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
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
import WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import WeilConjectures.CategoryTheory.StrictRoosComparison
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.StrictRoosNormalization
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstruction

/-! # Ordinary completed-ring realization of integral recollement

Source: Weil blueprint, main-20261015, smooth-purity localization, Integral stage
(blueprint: lem-sf-integral-ordinary-recollement-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [-instance] CategoryTheory.SignedDoubleHomCone.moduleBinaryBiproducts
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The completed-coefficient direct image is the pro-étale ringed direct image for the
canonical completed inverse-image identification `PurCompactSupport.completed`.
Source: Stacks 03D2 (blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: both are pushforwards along base change; their ring maps agree since the
coefficient identification is the adjoint of `sfCompletedCoefficientMap`. -/
theorem proEtaleRingModuleDirectImage_completed_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingModuleDirectImage f (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X)
        ((PurCompactSupport.completed l E).pull f) =
      sfCompletedModuleDirectImage l E f := by
  have he : proEtaleRingDirectImageMap f (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedCoefficientMap l E f :=
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
  rw [he]

/-- The exact pro-étale ringed module pullback is left adjoint to the
completed-coefficient direct image.
Source: Stacks 03D2 (blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfCompletedModulePullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingModulePullback f (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X)
        ((PurCompactSupport.completed l E).pull f) ⊣ sfCompletedModuleDirectImage l E f :=
  (proEtaleRingModuleOperations_properties f _ _
    ((PurCompactSupport.completed l E).pull f)).2.2.2.2.some.ofNatIsoRight
    (eqToIso (proEtaleRingModuleDirectImage_completed_eq l E f))

/-- Ordinary completed-coefficient direct image is a right adjoint.
Source: Stacks 03D2; localization proof step 1
(blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: the canonical completed structural map defines a morphism of ringed topoi.
Its module tensor inverse image is left adjoint to the specified module direct image. -/
@[instance] theorem sfOrdinaryModulePush_isRightAdjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfCompletedModuleDirectImage l E f).IsRightAdjoint := by
  exact (sfCompletedModulePullbackAdjunction l E f).isRightAdjoint

/-- The actual ordinary tensor inverse image, as Mathlib's left adjoint to the
specified completed-coefficient module direct image.
Source: Stacks 03D2; localization proof step 1
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryModulePull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarReductionSource l E Y ⥤ scalarReductionSource l E X :=
  (sfCompletedModuleDirectImage l E f).leftAdjoint

/-- The ordinary module adjunction, retaining its unit and counit.
Source: Stacks 03D2; localization proof step 1
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryModuleAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfOrdinaryModulePull l E f ⊣ sfCompletedModuleDirectImage l E f :=
  Adjunction.ofIsRightAdjoint (sfCompletedModuleDirectImage l E f)

/-- Additivity of ordinary tensor inverse image.
Source: Stacks 03D2; localization proof step 1
(blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: the module inverse-image adjunction is additive: its tensor and sheafification
constructions preserve addition of module maps. -/
@[instance] theorem sfOrdinaryModulePull_additive
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (sfOrdinaryModulePull l E f).Additive := by
  exact (sfOrdinaryModuleAdjunction l E f).left_adjoint_additive

/-- Exactness of ordinary immersion inverse image, with completed coefficients.
Source: Stacks 09AA, 099N; localization proof steps 1--2
(blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: the canonical coefficient inverse-image isomorphism commutes with each finite
projection. Immersion inverse image is exact, and coefficient transport is exact. -/
@[instance] theorem sfOrdinaryModulePull_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    PreservesFiniteLimits (sfOrdinaryModulePull l E f) := by
  exact preservesFiniteLimits_of_natIso ((sfOrdinaryModuleAdjunction l E f).leftAdjointUniq
    (sfCompletedModulePullbackAdjunction l E f)).symm

/-- Ordinary inverse image preserves finite colimits.
Source: Stacks 03D2; localization proof step 2
(blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: the specified functor is a left adjoint and therefore preserves colimits. -/
@[instance] theorem sfOrdinaryModulePull_preservesFiniteColimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (sfOrdinaryModulePull l E f) := by
  have : PreservesColimitsOfSize.{0, 0} (sfOrdinaryModulePull l E f) :=
    (sfOrdinaryModuleAdjunction l E f).leftAdjoint_preservesColimits
  infer_instance

/-- Exact descent of ordinary immersion pullback.
Source: Stacks 06YY; localization proof step 2
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryDerivedPull {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E X) :=
  (sfOrdinaryModulePull l E f).mapDerivedCategory

/-- Ordinary unbounded pullback/direct-image adjunction.
Source: Stacks 07A6; localization proof step 5
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryDerivedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    sfOrdinaryDerivedPull l E f ⊣ sfCompletedDerivedDirectImage l E f :=
  (sfOrdinaryModuleAdjunction l E f).mapDerivedCategoryRightDerivedAdjunction

/-- The canonical ordinary finite-reduction adjunct of a direct image.
Source: Stacks 07A6; localization proof steps 3--4
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryPushReduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
      ((sfCompletedDerivedDirectImage l E f).obj K) ⟶ sfFiniteDerivedDirectImage l E f K n :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    ((sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionUnit l E X n).app K) ≫
      (sfDerivedRestrictionComparison l E f n).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K))

/-- The actual nth strict Roos projection, before localization.
Source: Stacks 08TC; localization proof step 2
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryPullRoosProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
    integralOperationsRoos ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) ⟶
      ((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op n) :=
  CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism
      (K := fun m : ℕ ↦
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op m))
      (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P.obj))) ≫
    Pi.π (fun m : ℕ ↦
      ((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op m)) n

/-- The homotopy coordinate of the strict Roos complex.
Source: Stacks 08TC; localization proof step 2
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryPullRoosZeroCoordinate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (q : ℤ) :=
  (CochainComplex.mappingCocone.snd
    (towerTransitionEndomorphism
      (K := fun m : ℕ ↦
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op m))
      (integralOperationsTowerStep
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj)))).v q (q - 1) (by omega)

/-- The canonical quotient-augmentation leg, transposed through the ordinary
pullback adjunction. This is reduction unit followed by the finite pullback unit,
with the scalar-restriction/direct-image comparison in its specified direction.
Source: localization proof steps 2 and 5; Stacks 03D2, 07A6
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryPullAugmentationLeg {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) (q : ℤ) :
    P.obj.X q ⟶ (sfCompletedModuleDirectImage l E f).obj
      ((((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op n)).X q) :=
  (scalarReductionExtension_adjunction l E Y n).choose.unit.app (P.obj.X q) ≫
            (scalarReductionRestriction l E Y n).map
              ((coefficientProEtaleModuleAdjunction.{u, u} f
                (CommRingCat.of
                  (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
                    ((scalarReductionExtension l E Y n).obj (P.obj.X q))) ≫
            (sfDirectImageRestrictionComparison l E f n).hom.app
              ((integralOperationsLevelPullback l E f n).obj
                ((scalarReductionExtension l E Y n).obj (P.obj.X q)))

attribute [local irreducible] sfOrdinaryModulePull sfCompletedModuleDirectImage
  sfCompletedCoefficientMap integralDerivedPullback
  sfOrdinaryDerivedAdjunction
  integralOperationsPullbackTowerFunctor sfOrdinaryPullRoosProjection
  sfOrdinaryPullRoosZeroCoordinate sfOrdinaryPullAugmentationLeg

/-- Normalized comparisons for one immersion, in the actual completed and finite
module categories. All positive exponents occur as n+1. The representative equation
specifies the whole Roos augmentation, including its zero homotopy coordinate.
Source: localization Integral stage, proof steps 2--7
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
structure SfOrdinaryIntegralComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] where
  diagrams : CompletedCoefficientPushforward.ComparisonData l E f
  diagrams_structure : diagrams.structureMap =
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (sfCompletedCoefficientMap l E f)
  diagrams_model : diagrams.completedImage.functor ≅ sfCompletedDerivedDirectImage l E f
  diagrams_unit : ∀ I : CochainComplex (scalarReductionSource l E X) ℤ,
    HEq (diagrams.completedImage.unit.app I ≫
      diagrams_model.hom.app (DerivedCategory.Q.obj I))
      ((derivedCochainRightUnit (sfCompletedModuleDirectImage l E f)
        (sfCompletedDerivedDirectImage l E f)
        (sfCompletedModuleDirectImage l E f).rightDerivedFunctorUnit).app I)
  pull : sfOrdinaryDerivedPull l E f ⟶ integralDerivedPullback l E f
  pull_complete : ∀ K : DerivedCategory (scalarReductionSource l E Y),
    IsSfDerivedComplete l E Y K → IsIso (pull.app K)
  pull_preserves_complete : ∀ K : DerivedCategory (scalarReductionSource l E Y),
    IsSfDerivedComplete l E Y K →
      IsSfDerivedComplete l E X ((sfOrdinaryDerivedPull l E f).obj K)
  pull_model : ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
    ∃ a : ((sfOrdinaryModulePull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj ⟶
        integralOperationsRoos ((integralOperationsPullbackTowerFunctor l E f).obj P.obj),
      pull.app (DerivedCategory.Q.obj P.obj) ≫
          (integralDerivedPullbackComparison l E f).hom.app P =
        (sfOrdinaryModulePull l E f).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map a ∧
      (∀ (n : ℕ) (q : ℤ),
        (sfOrdinaryModuleAdjunction l E f).homEquiv _ _
          ((a ≫ sfOrdinaryPullRoosProjection l E f P n).f q) =
            sfOrdinaryPullAugmentationLeg l E f P n q) ∧
      (∀ q : ℤ, a.f q ≫ (sfOrdinaryPullRoosZeroCoordinate l E f P q) = 0)
  push : ∀ (K : DerivedCategory (scalarReductionSource l E X)),
    sfIntegralConstructible l E X K →
    ∀ [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K),
      (sfCompletedDerivedDirectImage l E f).obj K ≅ L.obj
  push_projection : ∀ (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) (n : ℕ),
    (push K hK L).hom ≫ L.projection ≫ Pi.π (sfDirectImageTerm l E f K) n =
      (sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionUnit l E X n).app K) ≫
        (sfDerivedRestrictionComparison l E f n).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K)
  push_reduction : ∀ (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) (n : ℕ),
    IsIso (sfDirectImageReductionComparison l E f L n) ∧
      (scalarReductionDerivedExtension l E Y n).map (push K hK L).hom ≫
        sfDirectImageReductionComparison l E f L n = sfOrdinaryPushReduction l E f K n
  push_constructible : ∀ K : DerivedCategory (scalarReductionSource l E X),
    sfIntegralConstructible l E X K →
      sfIntegralConstructible l E Y ((sfCompletedDerivedDirectImage l E f).obj K)
  pull_constructible : ∀ K : DerivedCategory (scalarReductionSource l E Y),
    sfIntegralConstructible l E Y K →
      sfIntegralConstructible l E X ((sfOrdinaryDerivedPull l E f).obj K) ∧
      sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K)

  pull_reduction : ∀ (K : DerivedCategory (scalarReductionSource l E Y))
    (_hK : sfIntegralConstructible l E Y K)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ),
    IsIso (integralPullbackFiniteComparison l E f K P e n)
  pull_interval : ∀ (K : DerivedCategory (scalarReductionSource l E Y))
    (a b : ℤ), a ≤ b → sfIntegralConstructible l E Y K →
    (∀ n : ℕ, proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension l E Y n).obj K) ⊆ Set.Icc a b) →
    ∀ n : ℕ, proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension l E X n).obj
        ((sfOrdinaryDerivedPull l E f).obj K)) ⊆ Set.Icc a b

end WeilConjectures
