/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
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
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationLeftSystem
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.ProperBaseChange.RealizationScalarFunctor

/-! # Normalized continuous field realization system

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15.
(blueprint: lem-weil-pbc-condensed-e-system)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
universe u
namespace WeilConjectures

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj TensorProduct

set_option synthInstance.maxSize 4096

section TensorAdjunction
universe r a b c d
variable (R : Type r) [CommRing R] (p : R)
  {C : Type a} [Category.{b} C] [Preadditive C] [Linear R C]
  {D : Type c} [Category.{d} D] [Preadditive D] [Linear R D]

private def tensorAdjunction (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (adj : F ⊣ G) :
    ScalarLocalization.transport R p F ⊣ ScalarLocalization.transport R p G where
  unit :=
    { app X := 1 ⊗ₜ[R] adj.unit.app X.obj
      naturality {X Y} f := by
        dsimp only [ScalarLocalization.transport, ScalarLocalization.transportHom,
          Functor.id_obj, Functor.comp_obj]
        change ScalarLocalization.composition R C p _ _ _
          (1 ⊗ₜ[R] adj.unit.app Y.obj) f =
          ScalarLocalization.composition R C p _ _ _
            ((G.mapLinearMap R).baseChange (Localization.Away p)
              ((F.mapLinearMap R).baseChange (Localization.Away p) f))
            (1 ⊗ₜ[R] adj.unit.app X.obj)
        induction f using TensorProduct.inductionOn with
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.unit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  counit :=
    { app X := 1 ⊗ₜ[R] adj.counit.app X.obj
      naturality {X Y} f := by
        dsimp only [ScalarLocalization.transport, ScalarLocalization.transportHom,
          Functor.id_obj, Functor.comp_obj]
        change ScalarLocalization.composition R D p _ _ _
          (1 ⊗ₜ[R] adj.counit.app Y.obj)
            ((F.mapLinearMap R).baseChange (Localization.Away p)
              ((G.mapLinearMap R).baseChange (Localization.Away p) f)) =
          ScalarLocalization.composition R D p _ _ _ f (1 ⊗ₜ[R] adj.counit.app X.obj)
        induction f using TensorProduct.inductionOn with
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.counit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  left_triangle_components X := by
    change ScalarLocalization.composition R D p _ _ _ (1 ⊗ₜ[R] adj.counit.app (F.obj X.obj))
      ((ScalarLocalization.transport R p F).map (1 ⊗ₜ[R] adj.unit.app X.obj)) = _
    simp only [ScalarLocalization.transport, ScalarLocalization.transportHom,
      LinearMap.baseChange_tmul]
    rw [ScalarLocalization.composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.left_triangle_components X.obj)
  right_triangle_components X := by
    change ScalarLocalization.composition R C p _ _ _
      ((ScalarLocalization.transport R p G).map (1 ⊗ₜ[R] adj.counit.app X.obj))
      (1 ⊗ₜ[R] adj.unit.app (G.obj X.obj)) = _
    simp only [ScalarLocalization.transport, ScalarLocalization.transportHom,
      LinearMap.baseChange_tmul]
    rw [ScalarLocalization.composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.right_triangle_components X.obj)
end TensorAdjunction

end WeilConjectures
