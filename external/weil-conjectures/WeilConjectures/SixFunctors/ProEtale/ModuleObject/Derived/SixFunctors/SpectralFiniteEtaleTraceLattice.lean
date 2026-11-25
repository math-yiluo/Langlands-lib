/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousFiniteEtaleTraceLattice
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralLocalizationSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralRegularTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralDenominators
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientTelescope
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
import WeilConjectures.CategoryTheory.HomColimitExtension
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.HomColimitTruncation
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Topology.StratificationDense
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Data.Int.Interval
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.GradedObject.Bifunctor
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.GradedObject.Trifunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.ContinuousMap.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceHomContinuity
import WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.CondensedLfpHomContinuity
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.IntegralLfpHomContinuity
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Max
import WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Grp.Adjunctions
import WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.CategoryTheory.ProperBaseChange.CondensedUnderivedPushforwardContinuitySupplement

/-! # Spectral integral coefficient lattices

Source: Bhatt--Scholze, Section 6.8, and blueprint main-20261015.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 2000] HasImages.has_image

/-- Lattice existence for a fixed coefficient inclusion. -/
private def HasCoefficientLattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) : Prop :=
  ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X),
    LocallyFree (condensedRingObj A X) N ∧
    ∃ ι : N ⟶ (Mod.comap (coefficientMap a X)).obj P,
      Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
        (coefficientMap a X)).homEquiv N P).symm ι)

/-- Rationalization of the image of a surjective trace is the rational module.
Source: blueprint main-20261015, stratified lattice proof, final paragraph.
(blueprint: lem-sfb-spectral-finite-etale-trace-lattice).
Proof. Exact scalar extension preserves the monic image inclusion. It sends the pushed
lattice map to an isomorphism; the rational counit is invertible. Composing with the
surjective trace makes the scalar extension of the image inclusion epi too, hence iso. -/
private theorem continuousTraceImage_rationalization_isIso
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    {U : Scheme.{u}} (p : U ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (τ : (lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P) [Epi τ] :
    let g := latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
      (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ
    IsIso (((Mod.extendRestrictAdjunction
      (coefficientMap (integralScalarMap l E) X)).homEquiv (image g) P).symm (image.ι g)) := by
  dsimp only
  let a := coefficientMap (integralScalarMap l E) X
  let F := Mod.extendScalars a
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) a
  let adj := Mod.extendRestrictAdjunction a
  let b := latticePushedEmbedding (integralScalarMap l E) X P p M e
  let g := b ≫ G.map τ
  have := integralScalarCounit_isIso l E X P
  have := integralScalarCounit_isIso l E X
    ((lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P))
  have := integralScalarUnderivedPushHom_isIso l E p M
  have := latticePushedEmbedding_map_isIso (integralScalarMap l E) X P p M e
  have hfac : F.map g ≫ adj.counit.app P = F.map b ≫ adj.counit.app _ ≫ τ := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (fun z ↦ F.map b ≫ z) (adj.counit.naturality τ)
  have : Epi (F.map g ≫ adj.counit.app P) := by
    rw [hfac]
    infer_instance
  have : Epi (F.map g) :=
    (epi_comp_iff_of_isIso (F.map g) (adj.counit.app P)).mp inferInstance
  have : Epi (F.map (factorThruImage g) ≫ F.map (image.ι g)) := by
    rw [← F.map_comp, image.fac]
    infer_instance
  have : Epi (F.map (image.ι g)) :=
    epi_of_epi (F.map (factorThruImage g)) (F.map (image.ι g))
  have : IsIso (F.map (image.ι g)) := isIso_of_mono_of_epi _
  change IsIso (F.map (image.ι g) ≫ adj.counit.app P)
  infer_instance

/-- Rationalization of the image of a surjective trace is the rational module.
Source: blueprint main-20261015, stratified lattice proof, final paragraph.
(blueprint: lem-sfb-spectral-finite-etale-trace-lattice).
Proof. Exact scalar extension preserves the monic image inclusion. It sends the pushed
lattice map to an isomorphism; the rational counit is invertible. Composing with the
surjective trace makes the scalar extension of the image inclusion epi too, hence iso. -/
private theorem continuousTraceImage_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    {U : Scheme.{u}} (p : U ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (τ : (lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P) [Epi τ]
    (hI : LocallyFree (condensedRingObj (integralCoeff l E) X)
      (image (latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
        (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ))) :
    HasCoefficientLattice (integralCoeff l E) (Profinite.continuousMapRingObj E)
      (integralScalarMap l E) X P := by
  change ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff l E) X),
      LocallyFree (condensedRingObj (integralCoeff l E) X) N ∧
      ∃ ι : N ⟶ (Mod.comap (coefficientMap (integralScalarMap l E) X)).obj P,
        Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
          (coefficientMap (integralScalarMap l E) X)).homEquiv N P).symm ι)
  let g := latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
    (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ
  exact ⟨image g, hI, image.ι g, inferInstance,
    continuousTraceImage_rationalization_isIso l E X P p M e τ⟩

/-- Finite-cover lattice descent for a fixed coefficient map. -/
private def FiniteEtaleCoefficientLattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u}) : Prop :=
  ∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
    LocallyFree (condensedRingObj B X) P →
    ∀ {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
      (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U)),
      LocallyFree (condensedRingObj A U) M →
      ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B p).obj P) →
      HasCoefficientLattice A B a X P

/-- Transport finite-cover descent along an equality of coefficient maps. -/
private theorem finiteEtaleCoefficientLattice_congr
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a b : A ⟶ B) [IsMonHom a] [IsMonHom b] (X : Scheme.{u})
    (h : a = b) (hP : FiniteEtaleCoefficientLattice A B a X) :
    FiniteEtaleCoefficientLattice A B b X := by
  cases h
  exact hP

/-- Finite-cover lattice descent, as a predicate of the coefficient subring. -/
private def FiniteEtaleLatticeOverSubring {E : Type} [NontriviallyNormedField E]
    (A : Subring E) (X : Scheme.{u}) : Prop :=
  FiniteEtaleCoefficientLattice (Profinite.continuousMapRingObj A)
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap A.subtype continuous_subtype_val)) X

/-- Rationalize the locally free trace image and change the integral subring. -/
private theorem normedFiniteEtaleTrace_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    FiniteEtaleLatticeOverSubring (Padic.coefficientExtensionIntegers l E) X := by
  have h0 : FiniteEtaleCoefficientLattice (integralCoeff l E)
      (Profinite.continuousMapRingObj E) (integralScalarMap l E) X := by
    intro P hP U p _ _ _ M hM e
    obtain ⟨τ, hτ, hI⟩ := continuousFiniteEtaleTrace_lattice l E X P hP p M hM e
    have := hτ
    exact continuousTraceImage_lattice l E X P p M e τ hI
  have h : FiniteEtaleLatticeOverSubring (continuousIntegers l E) X :=
    finiteEtaleCoefficientLattice_congr (integralCoeff l E) (Profinite.continuousMapRingObj E)
      (integralScalarMap l E)
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (continuousIntegers l E).subtype continuous_subtype_val)) X rfl h0
  exact Eq.mp (congrArg (fun A ↦ FiniteEtaleLatticeOverSubring A X)
    (continuousIntegers_eq l E)) h

/-- Topological ring structure transported to an equal field structure. -/
private theorem normedField_topologicalRing (E : Type) (nE : NontriviallyNormedField E)
    (F : Field E) (h : nE.toField = F) :
    letI := nE
    letI : Field E := F
    IsTopologicalRing E := by
  cases h
  let := nE
  infer_instance

/-- The coefficient rings together with their inclusion. -/
private structure CoefficientDiagram where
  integral : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  rational : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  map : integral ⟶ rational

/-- Package actual coefficient rings and their map. -/
private def coefficientDiagramOfMap
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] : CoefficientDiagram.{u} :=
  ⟨CommMon.mk A, CommMon.mk B, CommMon.homMk (Mon.ofHom a)⟩

/-- Finite-cover lattice descent depending on a bundled coefficient diagram. -/
private def DiagramFiniteLattice (D : CoefficientDiagram.{u}) (X : Scheme.{u}) : Prop :=
  FiniteEtaleCoefficientLattice D.integral.X D.rational.X D.map.hom.hom X

/-- Package a finite-cover descent proof with its actual coefficients. -/
private theorem diagramFiniteLattice_pack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (h : FiniteEtaleCoefficientLattice A B a X) :
    DiagramFiniteLattice (coefficientDiagramOfMap A B a) X := h

/-- Unpack finite-cover descent with exactly the given coefficient map. -/
private theorem diagramFiniteLattice_unpack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (h : DiagramFiniteLattice (coefficientDiagramOfMap A B a) X) :
    FiniteEtaleCoefficientLattice A B a X := h

/-- The coefficient diagram in the given normed structure. -/
private def normedCoefficientDiagram
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : CoefficientDiagram.{u} :=
  coefficientDiagramOfMap
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))

/-- The same diagram with the original field and algebra retained explicitly. -/
private def originalCoefficientDiagram
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (nE : NontriviallyNormedField E) (hFieldEq : nE.toField = hField) :
    CoefficientDiagram.{u} := by
  let := nE
  let : Field E := hField
  let : Algebra ℚ_[l] E := hAlg
  let : IsTopologicalRing E := normedField_topologicalRing E nE hField hFieldEq
  exact coefficientDiagramOfMap
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))

/-- Finite dimensionality transported to coherent normed algebra data. -/
private theorem normedFiniteDimensional_of_coherent
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [hFin : FiniteDimensional ℚ_[l] E]
    (nE : NontriviallyNormedField E)
    (nAlg : letI := nE; NormedAlgebra ℚ_[l] E)
    (hFieldEq : nE.toField = hField) (hAlgEq : HEq nAlg.toAlgebra hAlg) :
    letI := nE
    letI : Field E := nE.toField
    letI : Algebra ℚ_[l] E := nAlg.toAlgebra
    FiniteDimensional ℚ_[l] E := by
  cases hFieldEq
  cases eq_of_heq hAlgEq
  exact hFin

/-- Equality of algebraic structures gives equality of the coefficient diagrams. -/
private theorem coefficientDiagram_coherence
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (nE : NontriviallyNormedField E)
    (nAlg : letI := nE; NormedAlgebra ℚ_[l] E)
    (hFieldEq : nE.toField = hField) (hAlgEq : HEq nAlg.toAlgebra hAlg) :
    @normedCoefficientDiagram.{u} l _ E nE nAlg
      (normedFiniteDimensional_of_coherent l E
        (hField := hField) (hAlg := hAlg) nE nAlg hFieldEq hAlgEq) =
      originalCoefficientDiagram l E nE hFieldEq := by
  cases hFieldEq
  cases eq_of_heq hAlgEq
  rfl

/-- The trace-image rationalization proof as a property of its coefficient diagram. -/
private theorem normedDiagram_finiteLattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    DiagramFiniteLattice (normedCoefficientDiagram l E) X := by
  apply diagramFiniteLattice_pack
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)) X
  exact normedFiniteEtaleTrace_lattice l E X

/-- Finite etale trace descent gives an integral lattice over spectral coefficients.
Source: blueprint main-20261015, lemma-lattices-after-finite-stratification, "Pushing down by the
trace"; Bhatt--Scholze, Section 6.8.
(blueprint: lem-sfb-spectral-finite-etale-trace-lattice).

Proof. Split the finite etale surjection etale locally. Sum the sheet counits to define
p_*p*P → P; invariance under permutations glues these maps. On a nonempty chart there
is a sheet, and insertion into that sheet makes the trace epic. Take the categorical
image of p_*M → Res(P) induced by e and trace. Trivialize P pro-etale locally.
Local constancy of the lattice-class sheaf makes the finitely many sheet lattices
constant on a common refinement. Their sum is a finite free lattice over the valuation
ring. A lifted basis supplies a continuous linear section of the sheet sum, so the
image on continuous functions is the continuous-function sheaf of that sum lattice.
Thus the image is locally free. Its image inclusion is monic. Integral localization
is exact; the pushed lattice comparison rationalizes to an isomorphism and trace is
epic, so the rationalized image inclusion is epic and monic, hence invertible.
The scalar-extension adjunction identifies that map with the adjoint of the actual
image inclusion. Transport along continuousIntegers_eq identifies the norm ball
with the spectral valuation ring; the topology is the subspace topology throughout.
No degree is divided out. Empty bases and zero ranks yield zero modules. -/
theorem spectralFiniteEtaleTrace_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [hFin : FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    let B := Profinite.continuousMapRingObj.{u} E
    let a : A ⟶ B := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)
    ∀ (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)),
      LocallyFree (condensedRingObj B X) P →
      ∀ {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
        (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U)),
      LocallyFree (condensedRingObj A U) M →
      ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B p).obj P) →
      ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X),
        LocallyFree (condensedRingObj A X) N ∧
        ∃ ι : N ⟶ (Mod.comap (coefficientMap a X)).obj P,
          Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
            (coefficientMap a X)).homEquiv N P).symm ι) := by
  let nE := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : Field E := hField
  let : Algebra ℚ_[l] E := hAlg
  let nAlg : NormedAlgebra ℚ_[l] E :=
    { spectralNorm.normedAlgebra ℚ_[l] E with toAlgebra := hAlg }
  have h : DiagramFiniteLattice (originalCoefficientDiagram l E nE rfl) X :=
    Eq.mp (congrArg (fun D ↦ DiagramFiniteLattice D X)
      (coefficientDiagram_coherence l E nE nAlg rfl (HEq.refl _)))
      (normedDiagram_finiteLattice l E X)
  intro A B a
  exact diagramFiniteLattice_unpack A B a X h

end AlgebraicGeometry.ProEtale.CondensedRing
