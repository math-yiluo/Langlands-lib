/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralRestrictionFunctors

import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import all WeilConjectures.AlgebraicGeometry.LisseLatticeEtaleLocal
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import all Mathlib.CategoryTheory.Sites.CoversTop.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import all WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import all Mathlib.CategoryTheory.Limits.Presheaf
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import all WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import all Mathlib.AlgebraicGeometry.Pullbacks
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all Mathlib.CategoryTheory.Sites.Precoverage.Generates
import all Mathlib.CategoryTheory.Sites.Finite
import all Mathlib.CategoryTheory.Sites.LocalProperties
import all Mathlib.CategoryTheory.Limits.Connected
import all Mathlib.CategoryTheory.Limits.Types.Filtered
import all Mathlib.CategoryTheory.Filtered.Connected
import all Mathlib.CategoryTheory.Filtered.Final
import all Mathlib.Basic.Finite.Prod
import all WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import all WeilConjectures.AlgebraicGeometry.LisseLatticeClassSheaf
import all WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import all WeilConjectures.AlgebraicGeometry.LatticeClassDescent
import all WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
import all WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
import all WeilConjectures.AlgebraicGeometry.LatticePairRestriction
import all Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import all WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
import all WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
import all WeilConjectures.AlgebraicGeometry.LatticePairDescentData
import all WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverPreserving
import all Mathlib.CategoryTheory.Sites.CoversTop.Over
import all Mathlib.CategoryTheory.Sites.SheafHom
import all WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
import all WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.LargeSetSheafification
import all WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import all WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import all WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
import all WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all Mathlib.LinearAlgebra.TensorProduct.Pi
import all Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import all Mathlib.LinearAlgebra.TensorProduct.Basis
import all WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import all Mathlib.Topology.Algebra.OpenSubgroup
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import all Mathlib.Topology.ContinuousMap.Algebra
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import all Mathlib.Analysis.Normed.Field.WithAbs
import all Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import all Mathlib.GroupTheory.Coset.Defs
import all Mathlib.Topology.Algebra.Module.Equiv.Basic
import all Mathlib.Topology.Algebra.Module.Equiv.Pi
import all Mathlib.Topology.CompactOpen
import all Mathlib.LinearAlgebra.Basis.Defs
import all WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.RingTheory.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import all Mathlib.Algebra.Field.ULift
import all Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.CategoryTheory.Sites.Over
import all WeilConjectures.AlgebraicGeometry.LisseLatticePresentationTransport
import all WeilConjectures.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import all Mathlib.LinearAlgebra.TensorProduct.Map
import all Mathlib.CategoryTheory.ShrinkYoneda
import all Mathlib.CategoryTheory.Limits.Preserves.Ulift
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.LisseLatticeSliceTransport
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLattices
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLocalFreeness
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingSliceFreeness
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeFiniteCoproductSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousFiniteEtaleLatticeDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionLocalModel
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ContinuousLatticeIntersectionSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalModel
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitModel
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitData
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralLocalizationSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralRegularTelescope
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralDenominators
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientTelescope
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import all Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import all Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.ConstructibleSheaf.FreeLifting
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
import all WeilConjectures.CategoryTheory.HomColimitExtension
import all Mathlib.CategoryTheory.Triangulated.Pretriangulated
import all Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.Algebra.Category.Grp.Colimits
import all Mathlib.CategoryTheory.Filtered.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.CategoryTheory.Triangulated.Yoneda
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import all Mathlib.CategoryTheory.Category.ULift
import all WeilConjectures.CategoryTheory.HomColimitTruncation
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all Mathlib.Algebra.Homology.QuasiIso
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import all WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import all WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.Topology.StratificationDense
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import all WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import all Mathlib.Algebra.Homology.CochainComplexPlus
import all Mathlib.Data.Int.Interval
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import all WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import all Mathlib.Algebra.Homology.TotalComplex
import all Mathlib.CategoryTheory.Abelian.Basic
import all WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import all WeilConjectures.CategoryTheory.Triangulated.Recollement
import all Mathlib.Algebra.Category.Grp.Zero
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import all Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Adjunction.Triple
import all Mathlib.CategoryTheory.EffectiveEpi.Comp
import all Mathlib.CategoryTheory.Extensive
import all Mathlib.CategoryTheory.GradedObject.Bifunctor
import all Mathlib.CategoryTheory.GradedObject.Monoidal
import all Mathlib.CategoryTheory.GradedObject.Trifunctor
import all Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import all Mathlib.CategoryTheory.Limits.Preserves.Filtered
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import all Mathlib.CategoryTheory.Monad.Adjunction
import all Mathlib.CategoryTheory.Monoidal.Action.Basic
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.CommMon_
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Monoidal.Mon
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.CategoryTheory.Sites.Coherent.Basic
import all Mathlib.CategoryTheory.Sites.Coherent.Comparison
import all Mathlib.CategoryTheory.Sites.ConcreteSheafification
import all Mathlib.CategoryTheory.Sites.Grothendieck
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.Combinatorics.Quiver.ReflQuiver
import all Mathlib.Order.Int.ConditionallyCompleteOrder
import all Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import all Mathlib.Geometry.RingedSpace.PresheafedSpace
import all Mathlib.Geometry.RingedSpace.SheafedSpace
import all Mathlib.Topology.Category.CompHausLike.Basic
import all Mathlib.Topology.Category.CompHausLike.Limits
import all Mathlib.Topology.Category.Profinite.Basic
import all Mathlib.Topology.Category.Profinite.Limits
import all Mathlib.Topology.Category.TopCat.Basic
import all Mathlib.Topology.ContinuousMap.Defs
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceHomContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.AlgebraicGeometry.CondensedLfpHomContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import all WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import all WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
import all WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import all WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.IntegralLfpHomContinuity
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import all WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import all Mathlib.Topology.MetricSpace.Ultra.Basic
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Analysis.Normed.Group.Ultra
import all Mathlib.Data.Finset.Max
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import all WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import all WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all Mathlib.Data.Fin.Tuple.Basic
import all WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import all WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import all Mathlib.CategoryTheory.Sites.Adjunction
import all Mathlib.Algebra.Category.Grp.Adjunctions
import all WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import all WeilConjectures.CategoryTheory.ProperBaseChange.CondensedUnderivedPushforwardContinuitySupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeKernelModel
import all WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeDenominators
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalization
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixKernelLocallyFree
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-! # Constructibility of the internal integral Tate line

Source: current blueprint, sk-thm-int-restriction-line.proof.md, paragraph (3),
and definition-tate-twists, local-generator and signed-power paragraphs.
(blueprint: lem-sfb-integral-tate-line-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local irreducible] spIntegralTwist

private abbrev literalRestriction {X : Scheme.{u}} (U : X.ProEt) :
    Sheaf (ProEt.topology X) Ab.{u + 1} ⥤ Sheaf (ProEt.topology U.left) Ab.{u + 1} :=
  let : (MorphismProperty.Over.map (P := @WeaklyEtale.{u}) (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  Functor.sheafPushforwardContinuous
    (MorphismProperty.Over.map (P := @WeaklyEtale.{u}) (f := U.hom) ⊤ U.prop)
    Ab.{u + 1} (ProEt.topology U.left) (ProEt.topology X)

set_option backward.isDefEq.respectTransparency false in
private instance literalRestrictionLaxMonoidal {X : Scheme.{u}} (U : X.ProEt) :
    (literalRestriction U).LaxMonoidal := by
  have : (MorphismProperty.Over.map (P := @WeaklyEtale.{u}) (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  exact Functor.sheafPushforwardContinuousLaxMonoidal
    (MorphismProperty.Over.map (P := @WeaklyEtale.{u}) (f := U.hom) ⊤ U.prop)
    Ab.{u + 1} (ProEt.topology U.left) (ProEt.topology X)

-- A sectionwise linear trivialization is linear for literal restriction as well.
private noncomputable def sliceInternalIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) (U : X.ProEt)
    (e : ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) R).functor.obj M).over U ≅
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology X) R).functor.obj (Mod.regular R)).over U) :
    ((literalRestriction U).mapMod R).obj M ≅
      ((literalRestriction U).mapMod R).obj
        (Mod.regular R) := by
  let G := MorphismProperty.Over.map (P := @WeaklyEtale.{u}) (f := U.hom) ⊤ U.prop
  have : G.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  have : (ProEt.sliceFrom X U).IsDenseSubsite (ProEt.topology U.left)
      ((ProEt.topology X).over U) := ProEt.sliceDense X U
  let q : (literalRestriction U).obj M.X ≅ (literalRestriction U).obj R :=
    ((ProEt.sliceFrom X U).sheafPushforwardContinuous Ab.{u + 1}
    (ProEt.topology U.left) ((ProEt.topology X).over U)).mapIso
      ((SheafOfModules.toSheaf _).mapIso e)
  have hq (V : U.left.ProEtᵒᵖ)
      (r : (InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        (ProEt.topology X) R).obj (G.op.obj V))
      (m : ((InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
        (ProEt.topology X) R).obj M).val.obj (G.op.obj V)) :
      (q.hom.hom.app V).hom (r • m) =
        r • (show ((InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
          (ProEt.topology X) R).obj (Mod.regular R)).val.obj (G.op.obj V) from
          (q.hom.hom.app V).hom m) := by
    exact (e.hom.val.app (op ((ProEt.sliceFrom X U).obj V.unop))).hom.map_smul r m
  clear_value q
  refine Mod.isoMk q ?_
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  change Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
      ((literalRestriction U).obj R) ((literalRestriction U).obj M.X) ≫
      (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1}).map
        (Mod.act (((literalRestriction U).mapMod R).obj M).X) ≫
      (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1}).map q.hom = _
  erw [← Functor.LaxMonoidal.μ_natural_right_assoc
    (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
    ((literalRestriction U).obj R) q.hom]
  ext V : 2
  simp only [NatTrans.comp_app]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  intro r m
  have hM := (by
    set_option backward.isDefEq.respectTransparency false in
      exact InternalModuleOperations.section_action
        (ProEt.topology U.left) (ProEt.topology X) G R
        ((literalRestriction U).obj R) M.X (𝟙 _) (Mod.act M.X) V r m)
  have hR := (by
    set_option backward.isDefEq.respectTransparency false in
      exact InternalModuleOperations.section_action
        (ProEt.topology U.left) (ProEt.topology X) G R
        ((literalRestriction U).obj R) R (𝟙 _) (Mod.act (Mod.regular R).X) V r
        ((q.hom.hom.app V).hom m))
  set_option backward.isDefEq.respectTransparency false in
    simp only [id_whiskerRight, Category.id_comp] at hM hR
  change (q.hom.hom.app V).hom
      (((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
        ((literalRestriction U).obj R) ((literalRestriction U).obj M.X)).app V ≫
        (Mod.act (((literalRestriction U).mapMod R).obj M).X).hom.app V).hom
          (r ⊗ₜ[ℤ] m)) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
      ((literalRestriction U).obj R) ((literalRestriction U).obj R)).app V ≫
      (Mod.act (((literalRestriction U).mapMod R).obj (Mod.regular R)).X).hom.app V).hom
        (r ⊗ₜ[ℤ] (q.hom.hom.app V).hom m)
  have hm' :
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
        ((literalRestriction U).obj R) ((literalRestriction U).obj M.X)).app V ≫
        (Mod.act (((literalRestriction U).mapMod R).obj M).X).hom.app V).hom
          (r ⊗ₜ[ℤ] m) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})
        R M.X).app (G.op.obj V) ≫ (Mod.act M.X).hom.app (G.op.obj V)).hom
          (r ⊗ₜ[ℤ] m) := by
    exact hM
  have hr' :
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
        ((literalRestriction U).obj R) ((literalRestriction U).obj R)).app V ≫
        (Mod.act (((literalRestriction U).mapMod R).obj (Mod.regular R)).X).hom.app V).hom
          (r ⊗ₜ[ℤ] (q.hom.hom.app V).hom m) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})
        R R).app (G.op.obj V) ≫ (Mod.act (Mod.regular R).X).hom.app (G.op.obj V)).hom
          (r ⊗ₜ[ℤ] (q.hom.hom.app V).hom m) := by
    exact hR
  rw [hm', hr']
  exact hq V r m

attribute [local irreducible] sliceInternalIso

set_option backward.isDefEq.respectTransparency false in
private theorem free_via_monoidalIso {X Y : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (F G : Sheaf (ProEt.topology X) Ab.{u + 1} ⥤
      Sheaf (ProEt.topology Y) Ab.{u + 1}) [F.LaxMonoidal] [G.LaxMonoidal]
    (τ : F ≅ G) [NatTrans.IsMonoidal τ.hom]
    (hG : Mod.IsFree (G.obj R) ((G.mapMod R).obj M)) :
    Mod.IsFree (F.obj R) ((F.mapMod R).obj M) := by
  exact ProEtale.free_of_iso (ProEtale.free_comap (τ.hom.app R) hG)
    ((Functor.mapModNatIso τ R).app M).symm

set_option backward.isDefEq.respectTransparency false in
private theorem free_of_slice_trivial (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) (U : X.ProEt)
    (e : ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) R).functor.obj M).over U ≅
      (SheafOfModules.unit _).over U) :
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} U.hom).obj R)
      (((ProEtale.upperStar Ab.{u + 1} U.hom).mapMod R).obj M) := by
  let e₀ :
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology X) R).functor.obj (Mod.regular R) ≅ SheafOfModules.unit _ := by
    let i :
        ((InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
          (ProEt.topology X) R).obj (Mod.regular R)).val ≅ (SheafOfModules.unit _).val :=
      PresheafOfModules.isoMk
        (fun _ ↦ ModuleCat.isoMk (Iso.refl _) (by intro r; ext x; rfl))
        (by intro U V f; rfl)
    exact
      { hom := ⟨i.hom⟩
        inv := ⟨i.inv⟩
        hom_inv_id := SheafOfModules.hom_ext i.hom_inv_id
        inv_hom_id := SheafOfModules.hom_ext i.inv_hom_id }
  clear_value e₀
  let er := e ≪≫ (SheafOfModules.overFunctor _ U).mapIso e₀.symm
  let q := sliceInternalIso X R M U er
  clear_value q
  let F := literalRestriction U
  let reg : (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  clear_value reg
  have hF : Mod.IsFree (F.obj R) ((F.mapMod R).obj M) := by
    exact ⟨1, ⟨q ≪≫ reg ≪≫ (biproductUniqueIso
      (fun _ : Fin 1 ↦ Mod.regular (F.obj R))).symm⟩⟩
  let : (literalRestriction U).LaxMonoidal := literalRestrictionLaxMonoidal U
  let τ : ProEtale.upperStar Ab.{u + 1} U.hom ≅ literalRestriction U :=
    upperStarIsoSheafPushforward Ab.{u + 1} U.hom U.prop
  have : NatTrans.IsMonoidal τ.hom := inferInstance
  clear_value τ
  exact free_via_monoidalIso R M (ProEtale.upperStar Ab.{u + 1} U.hom)
    (literalRestriction U) τ hF

private theorem locallyFree_of_trivial_cover (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    {I : Type (u + 1)} (U : I → X.ProEt)
    (f : ∀ i, U i ⟶ ProEt.mk (𝟙 X))
    (hc : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (he : ∀ i, Nonempty (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) R).functor.obj M).over (U i) ≅
      (SheafOfModules.unit _).over (U i))) :
    CondensedRing.LocallyFree R M := by
  classical
  have hmem : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage X := by
    have h := (ProEt.mem_precoverage_iff).mp hc
    rw [Presieve.map_ofArrows] at h
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage X at h
    have hf : (fun i ↦ (f i).left) = (fun i ↦ (U i).hom) := by
      funext i
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 X = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    rwa [hf] at h
  let : Precoverage.Small.{u} proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (propQCPrecoverage @WeaklyEtale))
  let C : Scheme.Cover.{u + 1} proetalePrecoverage X :=
    { I₀ := I, X := fun i ↦ (U i).left, f := fun i ↦ (U i).hom, mem₀ := hmem }
  let D := C.restrictIndexOfSmall.{u}
  refine ⟨D, fun i ↦ ?_⟩
  exact free_of_slice_trivial X R M (U (Precoverage.ZeroHypercover.Small.restrictFun C i))
    (he _).some

private noncomputable def signedOverUnit (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) (U : X.ProEt)
    (e : (spSignedTwist X R L 1).over U ≅ (spSignedTwist X R L 0).over U)
    (d : ℤ) : (spSignedTwist X R L d).over U ≅ (SheafOfModules.unit _).over U := by
  exact WeilConjectures.lineSignedOverUnit.{u} X
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) R)
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) R).functor.obj L)
    U e d

private theorem locallyFree_lfp {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : CondensedRing.LocallyFree R P) : ProEtale.IsLocallyFinitelyPresented R P := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun s ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hC s
  exact ⟨n, 0, 0, ⟨e ≪≫ Limits.cokernelZeroIsoTarget.symm⟩⟩

private theorem locallyFree_constructible {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : CondensedRing.LocallyFree R P) : ProEtale.IsConstructibleModuleObject R P :=
  ⟨Scheme.Stratification.trivial X, fun _ ↦
    locallyFree_lfp (CondensedRing.locallyFree_map _ hP)⟩

private theorem bounded_single_of_locallyFree (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (h : CondensedRing.LocallyFree R M) :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj M) := by
  have hM := locallyFree_constructible h
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isGE _ 0 n hn)
  · exact IsConstructibleModuleObject.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm hM
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isLE _ 0 n hn)

private theorem bounded_signed_of_cover (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) (d : ℤ)
    {I : Type (u + 1)} (U : I → X.ProEt)
    (f : ∀ i, U i ⟶ ProEt.mk (𝟙 X))
    (hc : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (hi : ∀ i, Nonempty ((spSignedTwist X R L 1).over (U i) ≅
      (spSignedTwist X R L 0).over (U i))) :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology X) R).inverse.obj
        (spSignedTwist X R L d))) := by
  classical
  let S := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) R
  let M := S.inverse.obj (spSignedTwist X R L d)
  have he (i : I) : Nonempty ((S.functor.obj M).over (U i) ≅
      (SheafOfModules.unit _).over (U i)) := by
    exact ⟨(SheafOfModules.overFunctor _ (U i)).mapIso (S.counitIso.app _) ≪≫
      signedOverUnit X R L (U i) (hi i).some d⟩
  exact bounded_single_of_locallyFree X R M
    (locallyFree_of_trivial_cover X R M U f hc he)

/-- The actual internal-module realization of every signed integral Tate line is
constructible in degree zero.

Source: definition-tate-twists, local-generator and signed-power paragraphs;
sk-thm-int-restriction-line.proof.md, paragraph (3).
(blueprint: lem-sfb-integral-tate-line-constructible).

Proof: trivialize the degree-one integral line on the compatible-root pro-etale
cover. The section-module equivalence retains the underlying abelian sheaf and
scalar action. Its pullback comparison identifies restriction of the internal
line with restriction of the sectionwise line. On that cover every nonnegative
power is the tensor power of the regular rank-one module, and every negative
power is its dual; multiplication and evaluation identify these with the regular
module. These trivializations are compatible with restriction. Thus the internal
line has a rank-one finite presentation on this cover. Use the trivial single
stratum, including for the empty scheme, to obtain constructibility. The single
complex has this cohomology in degree zero and zero in every other degree,
so it is bounded constructible. -/
theorem integralTateLine_constructible (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (d : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)
      ((DerivedCategory.singleFunctor _ 0).obj (tateLine ℓ E X d)) := by
  classical
  obtain ⟨I, U, f, ζ, e, hc, _, _, _, hi, _⟩ := spTwists_commonCover X ℓ
  exact bounded_signed_of_cover X _ (spIntegralTwist X ℓ E) d U f hc
    (fun i ↦ (hi E i).1)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
