/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
public import WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullback
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import WeilConjectures.Algebra.Homology.RingedSiteBoundedDualComponents
import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwists
import WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.CondensedClosedSupportAdjunction
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasis
import WeilConjectures.AlgebraicGeometry.CondensedSubfieldBoundedCopowers
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralTransport
import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersection
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.AlgebraicGeometry.FiniteSectionCoproductLocalPermutation
import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryMonoidal
import WeilConjectures.AlgebraicGeometry.IntegralResiduePullOrdinaryUnit
import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
import WeilConjectures.AlgebraicGeometry.NormalizedDVRKFlatTransition
import WeilConjectures.AlgebraicGeometry.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.PrincipalConeKoszulRoosComparison
import WeilConjectures.AlgebraicGeometry.PrincipalIdealLocalTestCriterion
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
import WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import WeilConjectures.AlgebraicGeometry.StratifiedTorIntervalDevissage
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.CoefficientPushCopowerCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
import WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
import WeilConjectures.CategoryTheory.UnitPowerCompleteness
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.IntegersFinite
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.SheafGluing
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent

/-!
# Integral generators and their finite reductions

(1)--(3) (blueprint: lemma-integral-models).

The generator classes use the existing canonical scalar extension and locally closed
extension by zero. Finite reductions use the total left derived extension of scalars.
Their etale origin is tested through the existing intrinsic finite-coefficient comparison,
after the explicit restriction to constant scalars.
-/

@[expose] public section

set_option autoImplicit false
-- Preserve shared coefficient terms during proof cleanup.
set_option cleanup.letToHave false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale

universe u

namespace AlgebraicGeometry.ProEtale

/-- Convert a condensed ring sheaf to its existing ring object, then pull back to `X`.
Source: blueprint comparison with completed coefficients, notation `Λ_X`
(blueprint: lemma-comparison-completed-coefficients). -/
noncomputable def completedCoefficient (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  coefficientRing X
    (Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.SixFunctors

open scoped CategoryTheory.Functor

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

/-- Canonical coefficient specialization used in the integral generator statement.
(1)--(3)
(blueprint: lemma-integral-models). -/
noncomputable instance integralModel_coefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  Functor.monObjObj (F := upperStarFromPoint X) Λ

/-- The pulled-back continuous quotient ring retains its commutative ring structure.
Source: blueprint integral generators (3), the finite coefficient identification
(blueprint: lemma-integral-models). -/
noncomputable instance integralModelFiniteCoefficient_isComm (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsCommMonObj (completedCoefficient X (Profinite.continuousMapRingSheaf A)).X := by
  exact Functor.isCommMonObj_obj (F := upperStarFromPoint X)

end WeilConjectures.SixFunctors
