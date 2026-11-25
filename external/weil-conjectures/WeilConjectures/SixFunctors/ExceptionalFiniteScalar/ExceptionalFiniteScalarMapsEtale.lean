/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemQuotientNormalization
import all WeilConjectures.AlgebraicGeometry.Etale.Quotient.EtaleQuotientTensorProjectionOpenPasting
import WeilConjectures.AlgebraicGeometry.Etale.Quotient.EtaleQuotientTensorProjectionProperMate
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarConstantCoefficientIso
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionCoherence
import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability
import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
import WeilConjectures.CategoryTheory.CompactlyGenerated
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Equivalence
import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore
import WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
import WeilConjectures.CategoryTheory.DerivedHomologyInjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.LargeHomSolutionSet
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
import WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties
import Mathlib.Algebra.Module.ULift
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap
import WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.ProjectionFormulaCoproducts
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import WeilConjectures.CategoryTheory.CoproductsOfCopowers
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc
import WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionForward
import WeilConjectures.AlgebraicGeometry.SfGraphProjectionData
import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.SixFunctors.EtaleLocallyClosedGraphModel
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.SfGraphProjectionWord
import WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
import WeilConjectures.AlgebraicGeometry.SfGraphWordProjectionSquare
import WeilConjectures.AlgebraicGeometry.SfGraphFirstProjectionSquare
import WeilConjectures.AlgebraicGeometry.SfGraphProjectionStages
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
import WeilConjectures.AlgebraicGeometry.SfExactExchangePasting
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.SfGraphSecondProjectionSquare
import WeilConjectures.AlgebraicGeometry.SfGraphMiddleProjectionSquare
import WeilConjectures.AlgebraicGeometry.ProperOpenFactorProjection
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.SfGraphCompositionTailProjection
import WeilConjectures.AlgebraicGeometry.SfGraphInterchangeProjection
import WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
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
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.Compactification.BaseChange
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenCartesianNormalization
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenCubeNormalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonInterchange
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSidePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodWords
import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodGeometry
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonOpenShrink
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkFirstLeg
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkIntersectionWords
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphMiddleTransport
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphTransport
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSecondLeg
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductRowPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductInterchange
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductGeometry
import WeilConjectures.AlgebraicGeometry.EtalePairwiseProductGraphNormalization
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonProperAmbient
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientFirstSide
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientData
import WeilConjectures.AlgebraicGeometry.EtaleProperAmbientTransportComposition
import WeilConjectures.AlgebraicGeometry.Derived.DerivedCompactSupportCompositionCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientSecondSide
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientMiddle
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientGeometry
import WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSourcePasting
import WeilConjectures.AlgebraicGeometry.Open.OpenExchangeTowerSupplement
import WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSquarePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkLift
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkWords
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkSquare
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleGraphDiagonalNormalization
import WeilConjectures.AlgebraicGeometry.EtaleGraphRefinementNormalization
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphSideTransport
import WeilConjectures.AlgebraicGeometry.EtaleGraphFromOpenBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift

/-! # Finite scalar mates in the ordinary etale derived categories -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option cleanup.letToHave false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts
  cachedEtaleColimits cachedEtaleFlatResolution
  cachedEtaleInjectiveResolution cachedEtaleExactColimits
  cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

private theorem coefficient_annihilator (ell : ℕ) [Fact ell.Prime]
    (F : Type u) [Field F] [Algebra (Padic ell) F] [FiniteDimensional (Padic ell) F]
    (n : ℕ) : ((ell ^ (n + 1) : ℕ) : ULift.{u + 1}
      (Padic.coefficientExtensionRing ell F (n + 1))) = 0 := by
  let O := Padic.coefficientExtensionIntegers ell F
  let m := Padic.coefficientExtensionMaximalIdeal ell F
  have hs := (Padic.coefficientExtensionIntegers_dvr ell F).choose_spec
  have hm : (ell : O) ∈ m := by
    apply (hs.2.1 (ell : O)).2
    have he := spectralNorm_extends (K := Padic ell) (L := F) (ell : Padic ell)
    change spectralNorm (Padic ell) F (ell : F) < 1
    simpa only [map_natCast] using he.trans_lt (Padic.norm_p_lt_one (p := ell))
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer ell F} : Set O) = m := by
    exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  apply ULift.down_injective
  change ((ell ^ (n + 1) : ℕ) : Padic.coefficientExtensionRing ell F (n + 1)) = 0
  rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ell F (n + 1))),
    Ideal.Quotient.eq_zero_iff_mem]
  change ((ell ^ (n + 1) : ℕ) : O) ∈
    Ideal.span ({Padic.coefficientExtensionUniformizer ell F} : Set O) ^ (n + 1)
  rw [hg, Nat.cast_pow]
  exact Ideal.pow_mem_pow hm (n + 1)

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Etale.derivedTensor Etale.upperStar Etale.lowerStar HasDerivedCategory.standard
  Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategorySingleFunctor DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian

private theorem scalarRestrictionShift {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.scalarRestrictionPullbackIso a f).hom.CommShift ℤ := by
  dsimp only [Etale.scalarRestrictionPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    Functor.mapDerivedCategorySquareIso]
  infer_instance

private theorem inverseMateShift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    [G.CommShift ℤ] [H.CommShift ℤ] [L₁.CommShift ℤ] [R₁.CommShift ℤ]
    [L₂.CommShift ℤ] [R₂.CommShift ℤ]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift ℤ] [adj₂.CommShift ℤ]
    (β : TwoSquare R₁ H G R₂) [β.CommShift ℤ] :
    ((mateEquiv adj₁ adj₂).symm β).CommShift ℤ := by
  change ((Functor.leftUnitor (G ⋙ L₂)).inv ≫
    Functor.whiskerRight adj₁.unit (G ⋙ L₂) ≫
    (Functor.associator (L₁ ⋙ R₁) G L₂).inv ≫
    Functor.whiskerRight (Functor.associator L₁ R₁ G).hom L₂ ≫
    Functor.whiskerRight (Functor.whiskerLeft L₁ β) L₂ ≫
    Functor.whiskerRight (Functor.associator L₁ H R₂).inv L₂ ≫
    (Functor.associator (L₁ ⋙ H) R₂ L₂).hom ≫
    Functor.whiskerLeft (L₁ ⋙ H) adj₂.counit ≫
    (Functor.rightUnitor (L₁ ⋙ H)).hom).CommShift ℤ
  infer_instance

private theorem inverseConjugateShift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.CommShift ℤ] [L₂.CommShift ℤ] [R₁.CommShift ℤ] [R₂.CommShift ℤ]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift ℤ] [adj₂.CommShift ℤ]
    (β : R₁ ⟶ R₂) [β.CommShift ℤ] :
    ((conjugateEquiv adj₁ adj₂).symm β).CommShift ℤ := by
  let sq : TwoSquare R₁ (𝟭 D) (𝟭 C) R₂ :=
    .mk _ _ _ _ (R₁.rightUnitor.hom ≫ β ≫ R₂.leftUnitor.inv)
  have : sq.CommShift ℤ := by dsimp only [sq]; infer_instance
  have := inverseMateShift adj₁ adj₂ sq
  change (L₂.leftUnitor.inv ≫ ((mateEquiv adj₁ adj₂).symm sq) ≫
    L₁.rightUnitor.hom).CommShift ℤ
  infer_instance

private theorem inverseConjugateIsoShift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.CommShift ℤ] [L₂.CommShift ℤ] [R₁.CommShift ℤ] [R₂.CommShift ℤ]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift ℤ] [adj₂.CommShift ℤ]
    (e : R₁ ≅ R₂) [e.inv.CommShift ℤ] :
    ((conjugateIsoEquiv adj₁ adj₂).symm e).inv.CommShift ℤ := by
  rw [conjugateIsoEquiv_symm_apply_inv]
  exact inverseConjugateShift _ _ _

private theorem scalarPullbackShift {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.scalarPullbackIso a f).hom.CommShift ℤ := by
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)).leftAdjointCommShift ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).leftAdjointCommShift ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)).commShift_of_rightAdjoint ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).commShift_of_rightAdjoint ℤ
  let := scalarRestrictionShift a f
  rw [← Etale.scalarPullback_eq]
  dsimp only [ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_hom, asIso_inv]
  have h : (ProEtale.scalarPullbackReverseEtale a f).CommShift ℤ := by
    exact inverseMateShift _ _ _
  let := (ProEtale.scalarPullbackReverse_isIso a f).2
  exact NatTrans.CommShift.of_isIso _ ℤ

private theorem properScalarShift {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.scalarMate a f).CommShift ℤ := by
  let := scalarPullbackShift a f
  exact NatTrans.CommShift.mateEquiv _ _ _

private theorem shift_ofNatIsoRight
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G H : D ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (adj : F ⊣ G) [adj.CommShift ℤ] (e : G ≅ H) [e.hom.CommShift ℤ] :
    (adj.ofNatIsoRight e).CommShift ℤ where
  commShift_unit := by dsimp only [Adjunction.ofNatIsoRight]; infer_instance
  commShift_counit := by dsimp only [Adjunction.ofNatIsoRight]; infer_instance

private theorem openScalarShift {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (Etale.ExceptionalCoefficients.openIso a j).hom.CommShift ℤ := by
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)).leftAdjointCommShift ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).leftAdjointCommShift ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)).commShift_of_rightAdjoint ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).commShift_of_rightAdjoint ℤ
  let adjA :=
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) j).symm
  let adjB :=
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat B) j).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat B) j).symm
  have : adjA.CommShift ℤ := shift_ofNatIsoRight _ _
  have : adjB.CommShift ℤ := shift_ofNatIsoRight _ _
  let := scalarRestrictionShift a j
  let := NatTrans.CommShift.of_iso_inv (Etale.scalarRestrictionPullbackIso a j) ℤ
  change ((conjugateIsoEquiv
    (adjA.comp (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)))
    ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).comp adjB)).symm
        (Etale.scalarRestrictionPullbackIso a j)).inv.CommShift ℤ
  exact inverseConjugateIsoShift _ _ _

attribute [local irreducible] Etale.ExceptionalCoefficients.openIso Etale.scalarMate

private theorem pastedShift
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category D₁] [Category D₂] [Category D₃]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
    [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift D₃ ℤ]
    (JA : C₁ ⥤ C₂) (RA : C₂ ⥤ C₃) (JB : D₁ ⥤ D₂) (RB : D₂ ⥤ D₃)
    (TX : C₁ ⥤ D₁) (TZ : C₂ ⥤ D₂) (TY : C₃ ⥤ D₃)
    [JA.CommShift ℤ] [RA.CommShift ℤ] [JB.CommShift ℤ] [RB.CommShift ℤ]
    [TX.CommShift ℤ] [TZ.CommShift ℤ] [TY.CommShift ℤ]
    (q : RA ⋙ TY ⟶ TZ ⋙ RB) (r : JA ⋙ TZ ⟶ TX ⋙ JB)
    [q.CommShift ℤ] [r.CommShift ℤ] :
    ((Functor.associator JA RA TY).hom ≫ Functor.whiskerLeft JA q ≫
      (Functor.associator JA TZ RB).inv ≫ Functor.whiskerRight r RB ≫
      (Functor.associator TX JB RB).hom).CommShift ℤ := by
  infer_instance

private theorem compactScalarShift {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Etale.compactScalarMap a c).CommShift ℤ := by
  let := properScalarShift a c.g
  let := openScalarShift a c.i
  let JA := (Etale.openImmersionLowerShriek (ModuleCat A) c.i).mapDerivedCategory
  let JB := (Etale.openImmersionLowerShriek (ModuleCat B) c.i).mapDerivedCategory
  let RA := (Etale.lowerStar (ModuleCat A) c.g).rightDerivedFunctor
  let RB := (Etale.lowerStar (ModuleCat B) c.g).rightDerivedFunctor
  let TZ := Etale.scalarExtension a c.Z
  have he : Etale.compactScalarMap a c =
      (Functor.associator JA RA (Etale.scalarExtension a Y)).hom ≫
      Functor.whiskerLeft JA (Etale.scalarMate a c.g) ≫
      (Functor.associator JA TZ RB).inv ≫
      Functor.whiskerRight (Etale.ExceptionalCoefficients.openIso a c.i).hom RB ≫
      (Functor.associator (Etale.scalarExtension a X) JB RB).hom := by
    ext K
    simp only [NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    exact Etale.compactScalarMap_proper_open_factor a c K
  rw [he]
  exact pastedShift JA RA JB RB (Etale.scalarExtension a X) TZ
    (Etale.scalarExtension a Y) _ _

private theorem restrictionShift {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Etale.SystemProjection.singleRestriction (CommRingCat.ofHom a) c).CommShift ℤ := by
  let := scalarRestrictionShift a c.g
  have h : (Etale.scalarRestrictionDirectImageMap a c.g).CommShift ℤ :=
    NatTrans.CommShift.mateEquiv _ _ _
  have hopen : (Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso a c.i).inv.CommShift
      ℤ := by
    dsimp only [Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso,
      Functor.mapDerivedCategorySquareIso, Iso.trans_inv, Iso.symm_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv]
    infer_instance
  let JA := (Etale.openImmersionLowerShriek (ModuleCat A) c.i).mapDerivedCategory
  let JB := (Etale.openImmersionLowerShriek (ModuleCat B) c.i).mapDerivedCategory
  let RA := (Etale.lowerStar (ModuleCat A) c.g).rightDerivedFunctor
  let RB := (Etale.lowerStar (ModuleCat B) c.g).rightDerivedFunctor
  let UZ := Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology a
  have he : Etale.SystemProjection.singleRestriction (CommRingCat.ofHom a) c =
      (Functor.associator JB RB (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)).hom ≫
      Functor.whiskerLeft JB (Etale.scalarRestrictionDirectImageMap a c.g) ≫
      (Functor.associator JB UZ RA).inv ≫
      Functor.whiskerRight
        (Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso a c.i).inv RA ≫
      (Functor.associator (Sheaf.derivedRestrictScalars X.smallEtaleTopology a) JA RA).hom := by
    ext K
    simp only [NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    change (Etale.SystemProjection.singleRestriction (CommRingCat.ofHom a) c).app K = _
    rfl
  rw [he]
  exact pastedShift JB RB JA RA (Sheaf.derivedRestrictScalars X.smallEtaleTopology a) UZ
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a) _ _

private theorem rightUniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : F' ≅ F) :
    a.rightAdjointUniq (b.ofNatIsoLeft e) = conjugateIsoEquiv a b e := by
  ext Z
  simp [Adjunction.rightAdjointUniq, conjugateEquiv_apply_app]

attribute [local instance 2000] CategoryTheory.instAdditiveSheafConstantSheaf

attribute [local irreducible] Etale.singleFunctorCompLeftDerivedUpperStarIso
  Etale.scalarCoefficient Etale.quotientCoefficientComplex
  Etale.leftDerivedUpperStarComp Etale.leftDerivedUpperStarCompactificationIso
  Etale.rightDerivedLowerStarProjectionMap Etale.derivedOpenImmersionLowerShriekProjectionIso
  Etale.openImmersionLowerShriek Etale.derivedTensorSymmetry
  Etale.projectionMapOfCompactification

attribute [local irreducible] Etale.compactScalarMap
  Etale.SystemProjection.singleRestriction Etale.scalarTensorIso
  Etale.scalarCoefficientPullbackIso Etale.exceptionalConstantPullbackIso
  Etale.etaleScalarConstantCoefficientIso

attribute [local implicit_reducible] Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

private theorem cancelProjectionArrows
    {E : Type*} [Category E] {S M R C0 C1 C2 C3 C4 : E}
    {z0 : S ⟶ M} {z1 : M ⟶ R} {e : R ⟶ C3} {ei : C3 ⟶ R}
    {sy : S ⟶ C0} {bh : C0 ⟶ C1} {p' : C1 ⟶ C2} {q : C2 ⟶ C3}
    {p : C0 ⟶ C4} {n : C4 ⟶ C2} {w : C4 ⟶ R}
    (he : e ≫ ei = 𝟙 _)
    (hp : z0 ≫ z1 ≫ e = sy ≫ bh ≫ p' ≫ q)
    (hn : bh ≫ p' = p ≫ n) (ht : w ≫ e = n ≫ q) :
    z0 ≫ z1 = sy ≫ p ≫ w := by
  have h : (z0 ≫ z1) ≫ e = (sy ≫ p ≫ w) ≫ e := by
    rw [Category.assoc, hp, reassoc_of% hn]
    simp only [Category.assoc, ht]
  have hh := congrArg (fun m => m ≫ ei) h
  simpa only [Category.assoc, he, Category.comp_id] using hh

private theorem mapProjectionTail
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (TX : C ⥤ C) (L : D ⥤ C)
    {A0 A1 S : C} {B0 B1 : D} (bX : A0 ≅ A1) (bY : B0 ≅ B1)
    (sx : S ⟶ TX.obj A0) (sxi : TX.obj A0 ⟶ S) (hs : sxi ≫ sx = 𝟙 _)
    (t : L.obj B0 ⟶ A0) (Qf : L.obj B1 ⟶ A1)
    (hb : L.map bY.hom ≫ Qf = t ≫ bX.hom) :
    F.map (TX.map t ≫ sxi) ≫ F.map (sx ≫ TX.map bX.hom) =
    F.map (TX.map (L.map bY.hom)) ≫ F.map (TX.map Qf) := by
  simp only [← F.map_comp, Category.assoc, reassoc_of% hs,
    ← TX.map_comp, hb]

private theorem mapProjectionInverse
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (TX : C ⥤ C) {A0 A1 S : C} (bX : A0 ≅ A1)
    (sx : S ⟶ TX.obj A0) (sxi : TX.obj A0 ⟶ S) (hs : sx ≫ sxi = 𝟙 _) :
    F.map (sx ≫ TX.map bX.hom) ≫ F.map (TX.map bX.inv ≫ sxi) = 𝟙 _ := by
  have hbi : TX.map bX.hom ≫ TX.map bX.inv = 𝟙 _ := (TX.mapIso bX).hom_inv_id
  rw [← F.map_comp, Category.assoc, reassoc_of% hbi, hs, F.map_id]

private theorem forwardNaturalityOfInverse
    {C : Type*} [Category C] {A B D E : C}
    (p : A ⟶ D) (p' : B ⟶ E) (pi : D ⟶ A) (pi' : E ⟶ B)
    (y : A ⟶ B) (q : D ⟶ E)
    (hp : p ≫ pi = 𝟙 _) (hp' : pi' ≫ p' = 𝟙 _)
    (hn : q ≫ pi' = pi ≫ y) : y ≫ p' = p ≫ q := by
  have h := congrArg (fun m => p ≫ m ≫ p') hn
  simpa only [Category.assoc, hp', Category.comp_id, reassoc_of% hp,
    Category.id_comp] using h.symm

private theorem scalarProjectionWord {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a0 : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Etale.DerivedCategoryModule A X) :
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c
  let TX := (Etale.derivedTensor (ModuleCat A) X).obj K
  let TY := (Etale.derivedTensor (ModuleCat A) Y).obj (F.obj K)
  let bX := Etale.etaleScalarConstantCoefficientIso a0 X
  let bY := Etale.etaleScalarConstantCoefficientIso a0 Y
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    ((ModuleCat.restrictScalars a0).obj (ModuleCat.of B B))
  let Qf := (Etale.exceptionalConstantPullbackIso A f).hom.app V
  (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a0).map ((Etale.compactScalarMap a0 c).app K) ≫
    (Etale.SystemProjection.singleRestriction (CommRingCat.ofHom a0) c).app ((Etale.scalarExtension
    a0 X).obj K) ≫ F.map ((Etale.scalarTensorIso a0 X).hom.app K ≫ TX.map bX.hom) =
    (Etale.scalarTensorIso a0 Y).hom.app (F.obj K) ≫ TY.map bY.hom ≫
      ((Etale.projectionMapOfCompactification (ModuleCat A) c).app K).app ((constantSheaf
      Y.smallEtaleTopology (ModuleCat A)).mapDerivedCategory.obj V) ≫ F.map (TX.map Qf) := by
  have hp := Etale.constant_projection_word a0 c K
    (Etale.scalarMate_restrict_eq_projection_unbounded a0 c.g
      ((Etale.openImmersionLowerShriek (ModuleCat A) c.i).mapDerivedCategory.obj K))
  exact hp

private theorem scalarProjectionNaturality {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (a0 : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Etale.DerivedCategoryModule A X) :
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c
  let TX := (Etale.derivedTensor (ModuleCat A) X).obj K
  let TY := (Etale.derivedTensor (ModuleCat A) Y).obj (F.obj K)
  let bY := Etale.etaleScalarConstantCoefficientIso a0 Y
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    ((ModuleCat.restrictScalars a0).obj (ModuleCat.of B B))
  TY.map bY.hom ≫ ((Etale.projectionMapOfCompactification (ModuleCat A) c).app K).app
    ((constantSheaf Y.smallEtaleTopology (ModuleCat A)).mapDerivedCategory.obj V) =
    ((Etale.projectionMapOfCompactification (ModuleCat A) c).app K).app (Etale.scalarCoefficient a0
      Y) ≫ F.map (TX.map ((Etale.upperStar (ModuleCat A) f).leftDerivedFunctor.map bY.hom)) := by
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c
  let TX := (Etale.derivedTensor (ModuleCat A) X).obj K
  let TY := (Etale.derivedTensor (ModuleCat A) Y).obj (F.obj K)
  let bY := Etale.etaleScalarConstantCoefficientIso a0 Y
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    ((ModuleCat.restrictScalars a0).obj (ModuleCat.of B B))
  let p0 := ((Etale.projectionMapOfCompactification (ModuleCat A) c).app K).app
    (Etale.scalarCoefficient a0 Y)
  let p1 := ((Etale.projectionMapOfCompactification (ModuleCat A) c).app K).app
    ((constantSheaf Y.smallEtaleTopology (ModuleCat A)).mapDerivedCategory.obj V)
  have hi0 : p0 ≫ Etale.sfEtaleCompactProjectionInverse A c K
      (Etale.scalarCoefficient a0 Y) = 𝟙 _ := by
    let := (Etale.sfEtaleAmbientAdjointProjection A c).2 K (Etale.scalarCoefficient a0 Y)
    exact IsIso.hom_inv_id p0
  have hi1 : Etale.sfEtaleCompactProjectionInverse A c K
      ((constantSheaf Y.smallEtaleTopology (ModuleCat A)).mapDerivedCategory.obj V) ≫
      p1 = 𝟙 _ := by
    let := (Etale.sfEtaleAmbientAdjointProjection A c).2 K
      ((constantSheaf Y.smallEtaleTopology (ModuleCat A)).mapDerivedCategory.obj V)
    exact IsIso.inv_hom_id p1
  exact forwardNaturalityOfInverse p0 p1 _ _ _ _ hi0 hi1
    (Etale.sfEtaleCompactProjectionInverse_naturality_right A c K bY.hom)

private theorem scalarProjectionTail {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a0 : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Etale.DerivedCategoryModule A X) :
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c
  let TX := (Etale.derivedTensor (ModuleCat A) X).obj K
  let bX := Etale.etaleScalarConstantCoefficientIso a0 X
  let bY := Etale.etaleScalarConstantCoefficientIso a0 Y
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    ((ModuleCat.restrictScalars a0).obj (ModuleCat.of B B))
  let Qf := (Etale.exceptionalConstantPullbackIso A f).hom.app V
  F.map (TX.map (Etale.scalarCoefficientPullbackIso a0 f).hom ≫ (Etale.scalarTensorIso a0 X).inv.app
    K) ≫ F.map ((Etale.scalarTensorIso a0 X).hom.app K ≫ TX.map bX.hom) = F.map (TX.map
    ((Etale.upperStar (ModuleCat A) f).leftDerivedFunctor.map bY.hom)) ≫ F.map (TX.map Qf) := by
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c
  let TX := (Etale.derivedTensor (ModuleCat A) X).obj K
  let bX := Etale.etaleScalarConstantCoefficientIso a0 X
  let bY := Etale.etaleScalarConstantCoefficientIso a0 Y
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    ((ModuleCat.restrictScalars a0).obj (ModuleCat.of B B))
  let Qf := (Etale.exceptionalConstantPullbackIso A f).hom.app V
  exact mapProjectionTail F TX (Etale.upperStar (ModuleCat A) f).leftDerivedFunctor bX bY
    ((Etale.scalarTensorIso a0 X).hom.app K) ((Etale.scalarTensorIso a0 X).inv.app K)
    (Iso.inv_hom_id_app _ K) (Etale.scalarCoefficientPullbackIso a0 f).hom Qf
    (Etale.etaleScalarConstantCoefficientIso_pullback a0 f)

private theorem scalarProjectionInverse {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a0 : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Etale.DerivedCategoryModule A X) :
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c
  let TX := (Etale.derivedTensor (ModuleCat A) X).obj K
  let bX := Etale.etaleScalarConstantCoefficientIso a0 X
  F.map ((Etale.scalarTensorIso a0 X).hom.app K ≫ TX.map bX.hom) ≫ F.map (TX.map bX.inv ≫
    (Etale.scalarTensorIso a0 X).inv.app K) = 𝟙 _ := by
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c
  let TX := (Etale.derivedTensor (ModuleCat A) X).obj K
  let bX := Etale.etaleScalarConstantCoefficientIso a0 X
  exact mapProjectionInverse F TX bX ((Etale.scalarTensorIso a0 X).hom.app K)
    ((Etale.scalarTensorIso a0 X).inv.app K)
    (Iso.hom_inv_id_app _ K)

private theorem compactScalarProjection {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (a0 : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Etale.DerivedCategoryModule A X) :
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a0).map
        ((Etale.compactScalarMap a0 c).app K) ≫
      (Etale.SystemProjection.singleRestriction (CommRingCat.ofHom a0) c).app
        ((Etale.scalarExtension a0 X).obj K) =
    (Etale.scalarTensorIso a0 Y).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c).obj K) ≫
      ((Etale.projectionMapOfCompactification (ModuleCat A) c).app K).app
        (Etale.scalarCoefficient a0 Y) ≫
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c).map
        (((Etale.derivedTensor (ModuleCat A) X).obj K).map
            (Etale.scalarCoefficientPullbackIso a0 f).hom ≫
          (Etale.scalarTensorIso a0 X).inv.app K) := by
  have hp := scalarProjectionWord a0 c K
  have hn := scalarProjectionNaturality a0 c K
  have ht := scalarProjectionTail a0 c K
  have he := scalarProjectionInverse a0 c K
  exact cancelProjectionArrows he hp hn ht

private theorem restrictedCounit
    {C₁ D₁ C₂ D₂ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁} {F₂ : C₂ ⥤ D₂} {G₂ : D₂ ⥤ C₂}
    (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)
    (S : C₁ ⥤ C₂) (S' : D₁ ⥤ D₂) (U : C₂ ⥤ C₁) (U' : D₂ ⥤ D₁)
    (q : F₁ ⋙ S' ≅ S ⋙ F₂) (r : F₂ ⋙ U' ≅ U ⋙ F₁)
    (b : G₁ ⋙ S ≅ S' ⋙ G₂) (rho : G₂ ⋙ U ≅ U' ⋙ G₁)
    (hb : ∀ N, F₂.map (b.hom.app N) ≫ adj₂.counit.app (S'.obj N) =
      q.inv.app (G₁.obj N) ≫ S'.map (adj₁.counit.app N))
    (hrho : ∀ H, F₁.map (rho.hom.app H) ≫ adj₁.counit.app (U'.obj H) =
      r.inv.app (G₂.obj H) ≫ U'.map (adj₂.counit.app H)) (N : D₁) :
    U.map (b.hom.app N) ≫ rho.hom.app (S'.obj N) =
      adj₁.homEquiv _ _ (r.inv.app (S.obj (G₁.obj N)) ≫
        U'.map (q.inv.app (G₁.obj N)) ≫ U'.map (S'.map (adj₁.counit.app N))) := by
  apply (adj₁.eq_homEquiv_apply _ _).2
  rw [Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  rw [hrho]
  have hn := r.inv.naturality (b.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc]
  rw [hn]
  rw [Category.assoc, ← U'.map_comp, hb]
  simp only [Functor.map_comp]

private theorem iso_eq_of_postcomp
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e e' : F ≅ G)
    (h : ∀ (K : D) (H : C) (z : K ⟶ F.obj H),
      z ≫ e.hom.app H = z ≫ e'.hom.app H) : e = e' := by
  ext H
  simpa only [Category.id_comp] using h (F.obj H) H (𝟙 (F.obj H))

section ProjectionPasting

variable {C₁ C₂ D₁ D₂ : Type*}
  [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  (FA : C₁ ⥤ C₂) (FB : D₁ ⥤ D₂) (TX : C₁ ⥤ D₁) (TY : C₂ ⥤ D₂)
  (UX : D₁ ⥤ C₁) (UY : D₂ ⥤ C₂)
  (q : FA ⋙ TY ≅ TX ⋙ FB) (r : FB ⋙ UY ≅ UX ⋙ FA)

private def pasteProjection : FA ⋙ TY ⋙ UY ≅ (TX ⋙ UX) ⋙ FA :=
  (Functor.associator FA TY UY).symm ≪≫
    Functor.isoWhiskerRight q UY ≪≫ Functor.associator TX FB UY ≪≫
    Functor.isoWhiskerLeft TX r ≪≫ (Functor.associator TX UX FA).symm

private theorem pasteProjection_hom_app (K : C₁) :
    (pasteProjection FA FB TX TY UX UY q r).hom.app K =
      UY.map (q.hom.app K) ≫ r.hom.app (TX.obj K) := by
  simp only [pasteProjection, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

private theorem pasteProjection_inv_app (K : C₁) :
    (pasteProjection FA FB TX TY UX UY q r).inv.app K =
      r.inv.app (TX.obj K) ≫ UY.map (q.inv.app K) := by
  simp only [pasteProjection, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

variable [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [FA.CommShift ℤ] [FB.CommShift ℤ] [TX.CommShift ℤ] [TY.CommShift ℤ]
  [UX.CommShift ℤ] [UY.CommShift ℤ] [q.hom.CommShift ℤ] [r.hom.CommShift ℤ]

private theorem pasteProjection_shift :
    (pasteProjection FA FB TX TY UX UY q r).hom.CommShift ℤ := by
  dsimp only [pasteProjection, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  infer_instance

end ProjectionPasting

attribute [local irreducible] restrictionIso etaleAdjunction Etale.quotientRestrictionHomChain

-- Keep the adjunction calculations independent of the concrete coefficient quotients.
-- Allow the concrete projection and normalized six-Hom-chain type comparisons.
private theorem torsionScalarMapsEtale_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (A B : Type (u + 1)) [CommRing A] [CommRing B]
    [Finite A] [Finite B] (hA : ∃ r : ℕ, (l ^ r : A) = 0)
    (hB : ∃ r : ℕ, (l ^ r : B) = 0) (a' : A →+* B) :
    Nonempty (EtaleMates a' c) := by
  classical
  let FA := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
  let TX := Etale.scalarExtension a' X
  let TY := Etale.scalarExtension a' Y
  let UX := Sheaf.derivedRestrictScalars X.smallEtaleTopology a'
  let UY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology a'
  let adjA := etaleAdjunction A c
  let adjB := etaleAdjunction B c
  obtain ⟨q, hq, r, hr, rho, hchain, hrho, b, hb, hbc, P, hP, hrestricted⟩ :=
    Etale.etaleCoefficientQuotientNormalization D l hl f c A B hA hB a'
      (etaleExceptional A c) (etaleExceptional B c) adjA adjB
  let projection : FA ⋙ TY ⋙ UY ≅ (TX ⋙ UX) ⋙ FA :=
    pasteProjection FA FB TX TY UX UY q r
  refine ⟨{
    q := q
    q_normalized := hq
    properShift := properScalarShift a' c.g
    openShift := openScalarShift a' c.i
    b := b
    b_normalized := hb
    projection := projection
    projection_normalized := ?_
    projectionShift := by
      have hqshift : q.hom.CommShift ℤ := by rw [hq]; exact compactScalarShift a' c
      have hrshift : r.hom.CommShift ℤ := by rw [hr]; exact restrictionShift a' c
      exact pasteProjection_shift FA FB TX TY UX UY q r
    restricted_b := ?_ }⟩
  · intro K
    change (pasteProjection FA FB TX TY UX UY q r).hom.app K = _
    rw [pasteProjection_hom_app, hq, hr]
    exact compactScalarProjection a' c K
  · intro N
    have hrhoeq : rho = restrictionIso a' c q := by
      have heq : rho = Etale.quotientRestrictionIso a' c adjA adjB q := by
        apply iso_eq_of_postcomp
        intro K H z
        exact (hchain K H z).trans
          (Etale.quotientRestrictionIso_chain a' c adjA adjB q K H z).symm
      rw [heq]
      unfold Etale.quotientRestrictionIso restrictionIso
      exact (rightUniq_eq_conjugate
        ((Adjunction.ofIsRightAdjoint UX).comp adjB)
        (adjA.comp (Adjunction.ofIsRightAdjoint UY)) q).symm
    have hh := restrictedCounit adjA adjB TX TY UX UY q r b rho hbc hrho N
    change UX.map (b.hom.app N) ≫ (restrictionIso a' c q).hom.app (TY.obj N) =
      adjA.homEquiv _ _ (projection.inv.app ((etaleExceptional A c).obj N) ≫
        (TY ⋙ UY).map (adjA.counit.app N))
    rw [← hrhoeq, hh]
    congr 1
    simp only [projection, pasteProjection_inv_app, Functor.comp_map, Category.assoc]

/-- The ambient etale scalar-mate package exists for a finite coefficient map.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks 0GL6, 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-maps-etale).

This statement isolates the ordinary etale part of the construction: the proper/open
comparison, its adjoint mate, projection normalization, and shift compatibility.
It is strictly smaller than `ConstructionMaps`, whose remaining finite-subcategory
maps are supplied by `FiniteScalarMapsCore`.
-/
theorem finiteScalarMapsEtale_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    Nonempty (EtaleMates (RingHom.ulift.{u + 1, u + 1} a) c) := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let : Finite (Padic.coefficientExtensionRing l L (m + 1)) :=
    Padic.finite_coefficientExtensionRing l L (m + 1) (Nat.succ_pos m)
  exact torsionScalarMapsEtale_exists D l _hl f c _ _
    ⟨n + 1, by simpa only [Nat.cast_pow] using coefficient_annihilator l E n⟩
    ⟨m + 1, by simpa only [Nat.cast_pow] using coefficient_annihilator l L m⟩
    (RingHom.ulift.{u + 1, u + 1} a)

end WeilConjectures.ExceptionalFiniteScalar
