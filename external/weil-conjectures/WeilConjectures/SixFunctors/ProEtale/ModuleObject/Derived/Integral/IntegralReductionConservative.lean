/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
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
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Max
import WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
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
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralConstructibleNakayama
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralReductionScalar
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-! # Conservativity of integral reduction

Source: Bhatt--Scholze, Sections 6.7--6.8 (blueprint: lem-weil-pbc-integral-reduction-conservative).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- Derived reduction modulo ℓ detects isomorphisms between bounded constructible
integral complexes. Source: Bhatt--Scholze, Proposition 6.8.11(3) and derived Nakayama
(blueprint: lem-weil-pbc-integral-reduction-conservative).

Proof in words. The valuation ring of a finite normed extension is a complete discrete
valuation ring, and ℓ is a positive power of a uniformizer times a unit. On a finite
stratification the cohomology modules are locally finitely presented. The kernel, cokernel
and extension closure of these modules makes the cone of φ bounded constructible.
The integral realization identifies the locally finitely presented internal modules
with the continuous integral sheaves in Proposition 6.8.11(3); this identification and
the coefficient-dependent closure assertions must be established, rather than inferred
from noetherianity alone. Derived reduction carries the cone to zero when the reduced
map is invertible. The two-term coefficient resolution identifies its restricted
reduction with the cone of multiplication by ℓ, so multiplication by ℓ is invertible
on the cone and hence on every cohomology module. Constructible Nakayama makes each
of those modules zero. The cone is therefore zero,
so φ is invertible. This argument includes torsion modules, zero complexes, and empty X;
it uses no properness or exchange hypothesis. -/
theorem integralReduction_reflects_isIso (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    {M N : ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X)}
    (φ : M ⟶ N)
    (hφ : IsIso ((integralReduction ℓ E X).map φ.hom)) : IsIso φ := by
  let := (integralConstructible_serre ℓ E X).1
  let := (integralConstructible_serre ℓ E X).2.1
  let := (integralConstructible_serre ℓ E X).2.2
  let : (boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).IsTriangulated :=
    isTriangulated_boundedConstructible_of_serre _
      (fun _ _ f hM hN ↦ ⟨ObjectProperty.prop_kernel _ f hM hN,
        ObjectProperty.prop_cokernel _ f hM hN⟩)
      (fun _ hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)
  obtain ⟨C, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ.hom
  obtain ⟨C', hC', ⟨e⟩⟩ := ObjectProperty.ext_of_isTriangulatedClosed₃'
    (boundedConstructible (condensedRingObj (integralCoeff ℓ E) X))
      _ hT M.property N.property
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (integralReductionMap ℓ E) X)
  let : (L(Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X))).CommShift ℤ :=
    adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : (L(Mod.extendScalars
      (coefficientMap (integralReductionMap ℓ E) X))).IsTriangulated :=
    adj.isTriangulated_leftAdjoint
  have hred : IsZero ((integralReduction ℓ E X).obj C) := by
    exact Pretriangulated.Triangle.isZero₃_of_isIso₁ _
      ((L(Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X))).map_distinguished
        _ hT) hφ
  have hred' : IsZero ((integralReduction ℓ E X).obj C') :=
    hred.of_iso ((integralReduction ℓ E X).mapIso e).symm
  have hℓ : IsIso (ℓ • 𝟙 C') := integralReduction_isIso_nsmul_of_isZero ℓ E X C' hred'
  have hzero : IsZero C' := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro n
    let H := DerivedCategory.homologyFunctor
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) n
    have hℓH : IsIso (ℓ • 𝟙 (H.obj C')) := by
      have : IsIso (H.map (ℓ • 𝟙 C')) := inferInstance
      rw [H.map_nsmul, H.map_id] at this
      exact this
    exact integralConstructible_isZero_of_isIso_nsmul ℓ E X _ (hC'.2 n) hℓH
  exact (ObjectProperty.isIso_hom_iff _).mp
    ((Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).mp (hzero.of_iso e))

end AlgebraicGeometry.ProEtale.CondensedRing
