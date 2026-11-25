/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalModels
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.IntegralSectionMemberModels
import WeilConjectures.AlgebraicGeometry.IntegralSectionScalarModels
import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.IntegralSectionRegularScalars
import WeilConjectures.AlgebraicGeometry.IntegralSectionRegularScalarsScalar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedRealizationRegularSupplement
import WeilConjectures.AlgebraicGeometry.IntegralConstantSectionProjection
import WeilConjectures.AlgebraicGeometry.DiscreteCoefficientModel
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Category.Profinite.AsLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.CategoryTheory.Sites.LocalSite
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletionTransport
import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Mathlib.Algebra.Homology.HomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
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
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
import WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.Algebra.Category.CommAlgCat.Basic
import WeilConjectures.RingTheory.LimitFlatModules
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
import WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
import WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.CompactAdicContinuousIdentification
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import Mathlib.Order.Filter.Bases.Basic
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import Mathlib.Order.CompletePartialOrder
import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientTerminalSupplement
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompleteSectionPredicate
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletedSectionIdeal
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletedSectionRing
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.IntegralModelsResidueIdealComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.CategoryTheory.RingedCocontinuousMonoidal
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import WeilConjectures.AlgebraicGeometry.DiscreteCoefficientLocalModels
import WeilConjectures.AlgebraicGeometry.DiscretePointPresentationRefinement
import WeilConjectures.AlgebraicGeometry.PointModelFreeModule
import WeilConjectures.AlgebraicGeometry.PointModelRestrictionModule
import WeilConjectures.AlgebraicGeometry.PointModelPullbackFunctor
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.Data.Int.Interval
import WeilConjectures.AlgebraicGeometry.DiscretePointPresentationTransport
import WeilConjectures.AlgebraicGeometry.CoefficientSliceRestrictionIso
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientChartPullback
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.IntegralSectionCoefficientNaturality
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonModelRealizationSupplement
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.DiscreteConstantPresentationLifting
import WeilConjectures.AlgebraicGeometry.ConstantSliceInternalPresentation
import WeilConjectures.AlgebraicGeometry.ConstantSliceModuleEncoding
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientPullbackCoordinates
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientRingPullback
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientSliceFixedModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ConstantModuleGlobalEncoding
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.DiscreteInternalMatrixLocalLifting
import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.DiscreteSectionCoordinates
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import WeilConjectures.CategoryTheory.FiniteLocalSectionLifts
import Mathlib.Data.Fintype.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.WeilObject.Sheaf.Stalk
import WeilConjectures.AlgebraicGeometry.NoetherianGlobalConstructibility
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquaresSupplement
import WeilConjectures.SixFunctors.ProEtale.IntegralSectionProjectionNormalization
import WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentationSupplement
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalIsomorphisms
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleSliceOrdinaryComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientSliceComparisonDataSupplement
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import all WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.Native.NativeAdicConstructibilityEncoding
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Native constructibility of an ordinary integral local model

Source: Bhatt--Scholze, Definitions 6.8.3 and 6.8.10, Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-heart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj TensorProduct

namespace WeilConjectures.LocallyFiniteAdicRealization

attribute [local instance 100000] Sheaf.monoidalCategory Sheaf.braidedCategory

open MonoidalCategory MonObj
open CategoryTheory.InternalAbelianSheafModule
open AlgebraicGeometry.ProEtale

private def liftSectionMap (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    {R S : Sheaf (ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) R ⟶
      sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) S) : R ⟶ S :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map a

private theorem liftSectionMap_mon (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    {R S : Sheaf (ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) R ⟶
      sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) S) : IsMonHom (liftSectionMap X a) := by
  let : MonObj R.obj := (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).monObjObj R
  let : MonObj S.obj := (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).monObjObj S
  have : IsMonHom ((sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).map
      (liftSectionMap X a)) := by
    constructor
    · apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro n
      change ULift.{u + 1} ℤ at n
      let f : ULift.{u + 1} ℤ →+ S.obj.obj U :=
        ((η[R.obj] ≫ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).map
          (liftSectionMap X a)).app U).hom
      let g : ULift.{u + 1} ℤ →+ S.obj.obj U := (η[S.obj].app U).hom
      change f n = g n
      have hn : n = n.down • (ULift.up 1 : ULift.{u + 1} ℤ) := by
        apply ULift.ext
        simp
      rw [hn, map_zsmul, map_zsmul]
      congr 1
      exact (a.hom.app U).hom.map_one
    · apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.toIntLinearMap_injective
      apply TensorProduct.ext'
      intro x y
      exact (a.hom.app U).hom.map_mul x y
  exact Sheaf.isMonHom_of_isMonHom_map _

private theorem stratifiedModels_of_iso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {M N : pbcModules X (pbcAdicCompletion X d)} (e : M ≅ N)
    (hM : IsIntegralStratifiedFinitelyPresented X d M) :
    IsIntegralStratifiedFinitelyPresented X d N := by
  obtain ⟨s, hs⟩ := hM
  refine ⟨s, fun j ↦ ?_⟩
  obtain ⟨V, hV, h⟩ := hs j
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h U f hf
  exact ⟨P, hP, ⟨(SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (s.immersion j) _).mapIso e.symm) ≪≫ eP⟩⟩

/-- A stratified finitely presented integral module becomes a native constructible
sheaf under ordinary tensor extension. No assertion about derived objects occurs here.

Source: Bhatt--Scholze, Definitions 6.8.3 and 6.8.10, Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-heart).

Proof in words: take the finite stratification and the covering sieves in hN.
Restriction along the normalized completed coefficient isomorphism identifies the
local models with completed constant realizations of finitely presented valuation-ring
modules. Tensoring with C.integralMap commutes with the actual-ring inverse images and
slice restrictions, by the scalar-extension adjunction and its balanced tensor
associator. On each covering member this gives the native coefficient tensored with the
scalar module localized to E and then extended along i. A finitely presented module over
the valuation DVR becomes a finite-dimensional E-vector space after localization;
torsion becomes zero. Choose a finite basis and extend it to identify the displayed
tensor with a finite direct sum of native units. The section-module equivalence and
scalar-forgetting equivalence identify those units and commute with inverse image;
full faithfulness lifts the trivializations through e. Replace each covering sieve by
a small pro-etale covering family. Hence the native restriction is lisse on each of the
same finitely many strata, and is therefore constructible. Empty strata, the empty
scheme, zero modules and torsion local models all use the permitted rank zero.
-/
theorem nativeIntegralCoefficient_heart
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (C : CoefficientPresentation l X E i)
    (N : scalarReductionSource.{u, u} l E X)
    (hN : IsIntegralStratifiedFinitelyPresented X (pbcIntegralDatum l E)
      ((SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison X l E).hom).obj N))
    (F : ProEtale.AdicSheaf l X)
    (e : (sections l X).obj F ≅ (pbcExtend (C.integralMap l X)).obj N) :
    ProEtale.IsAdicConstructibleSheaf F := by
  classical
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let A := ProEtale.AdicCompletion.ring l E X
  let H := ProEtale.integralSectionFunctor l E X
  let B := sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology X) (abRing l X)
  let : B.functor.IsEquivalence := B.isEquivalence_functor
  let : H.IsEquivalence := by dsimp only [H]; infer_instance
  let c := ProEtale.integralSectionRingIso l E X
  let t := c.hom ≫ C.integralMap l X
  let a := liftSectionMap X t
  have : IsMonHom a := liftSectionMap_mon X t
  have ha : CondensedRing.sectionRingMap X a = t := by
    ext U x
    rfl
  -- The restriction square determines the extension square by taking mates.
  let β : Mod.comap a ⋙ H ≅ B.functor ⋙ pbcRestrict (C.integralMap l X) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.sectionModuleComapIso X a)
        (pbcRestrict c.inv) ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft B.functor
        (pbcRestrictComp c.inv (CondensedRing.sectionRingMap X a) (C.integralMap l X)
          (by rw [ha]; exact c.inv_hom_id_assoc (C.integralMap l X)))
  let α := ((mateEquiv (Mod.extendRestrictAdjunction a)
    (pbcScalarAdjunction (C.integralMap l X))).symm β.hom)
  have : IsIso α := isIso_inverseMate_of_equivalences (G := H) (H := B.functor)
    (Mod.extendRestrictAdjunction a) (pbcScalarAdjunction (C.integralMap l X)) β
  let δ := (asIso α).symm
  -- Transport the given integral models through the section equivalence.
  let M := H.inv.obj N
  let counit : H.obj M ≅ N := H.asEquivalence.counitIso.app N
  have hm := stratifiedModels_of_iso X (pbcIntegralDatum l E)
    ((SheafOfModules.restrictScalars
      (integralDetailedCoefficientComparison X l E).hom).mapIso counit.symm) hN
  have hconst := (ProEtale.integralSectionLocalModels l E X M).mpr hm
  have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [ProEtale.IsConstantModelConstructible, ite_eq_left hqc] at hconst
  have hM := ProEtale.constructible_of_finiteConstantStratified _ X M hconst
  -- Scalar extension preserves constructibility; the native encoding reflects it.
  have hext := ProEtale.constructible_extend A (abRing l X) a hM
  let q : (ProEtale.AdicSheaf.forgetAb l X).obj F ≅ (Mod.extendScalars a).obj M :=
    B.functor.preimageIso
      (e ≪≫ (pbcExtend (C.integralMap l X)).mapIso counit.symm ≪≫ (δ.app M).symm)
  exact (ProEtale.encoding_constructible_iff F).mpr
    (_root_.constructible_comap (ProEtale.NativeEncoding.coefficientIso l X).hom
      (ProEtale.IsConstructibleModuleObject.of_iso q.symm hext))

end WeilConjectures.LocallyFiniteAdicRealization
