/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.CondensedPullbackTensorComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarModelImmersionExtension
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
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
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
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
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
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
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
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
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LfpTensorSingleSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb

/-!
# Operations on bounded constructible integral coefficient complexes

Source: blueprint main-20261015, chap-Construction-of-f, lemma-integral-models,
sk-lem-integral-models-operations.md (blueprint: lemma-integral-models).

Constructibility uses finite constant scalar models, as in the recorded
definition-constructible-sheaves. The tensors and the projection formula are ambient and
uncompleted.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] DerivedCategory.TStructure.t
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The constructible-sheaf tensor calculation on an arbitrary Noetherian scheme.
Source: Bhatt--Scholze, Proposition 6.8.11(3), as in the existing
`boundedConstructible_tensor_single` proof. Its local calculation, common stratification
and vanishing detection use only Noetherianity; no field base is needed. -/
private theorem tensor_single_noetherian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hlfp : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (F G : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) F →
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) G →
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
      ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj F ⊗
          (DerivedCategory.singleFunctor _ 0).obj G)))
    (X : Scheme.{u}) [IsNoetherian X]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X) G) :
    boundedConstructible (condensedRingObj Λ X)
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G) := by
  classical
  let R := condensedRingObj Λ X
  let K := (DerivedCategory.singleFunctor _ 0).obj F ⊗
    (DerivedCategory.singleFunctor _ 0).obj G
  obtain ⟨S, hS⟩ := common_lfp_stratification hF hG
  let H (a : Fin S.n) := upperStar Λ (S.immersion a)
  have lfp (a : Fin S.n)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
      (hM : IsLocallyFinitelyPresented
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a)) ((H a).obj M) := by
    exact localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _).symm
      (localFinitePresentation_comap _ hM)
  let e (a : Fin S.n) : (H a).leftDerivedFunctor.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj ((H a).obj F) ⊗
        (DerivedCategory.singleFunctor _ 0).obj ((H a).obj G) :=
    (Functor.Monoidal.μIso (H a).leftDerivedFunctor _ _).symm ≪≫
      tensorIso ((H a).singleFunctorCompLeftDerivedFunctorIso.app F)
        ((H a).singleFunctorCompLeftDerivedFunctorIso.app G)
  have hlocal (a : Fin S.n) :
      TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.noetherianSpace
  have hom_lfp (a : Fin S.n) (n : ℤ) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a))
        ((H a).obj ((DerivedCategory.homologyFunctor _ n).obj K)) := by
    apply localFinitePresentation_of_iso
      ((H a).leftDerivedFunctorHomologyFunctorIso n |>.app K).symm
    apply localFinitePresentation_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso (e a)).symm
    exact (hlfp (S.domain a) ((H a).obj F) ((H a).obj G)
      (lfp a F (hS a).1) (lfp a G (hS a).2)).2 n
  have detect
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
      (hM : ∀ a : Fin S.n, IsZero ((H a).obj M)) : IsZero M := by
    rw [IsZero.iff_id_eq_zero]
    apply Mod.hom_ext
    apply eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
    · intro x
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
      exact ⟨a, S.range_immersion a |>.symm ▸ ha⟩
    · intro a
      let e' := (Mod.extendScalarsIsoComapInv
        (condensedPullbackHom Λ (S.immersion a))).app
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)
      have hz := (Mod.forget _).map_isZero ((hM a).of_iso e'.symm)
      change IsZero ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj M.X) at hz
      simpa using hz.eq_of_src
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).map (𝟙 M.X)) 0
  have hupper := DerivedCategory.isLE_tensor
    ((DerivedCategory.singleFunctor _ 0).obj F)
    ((DerivedCategory.singleFunctor _ 0).obj G) 0 0
  rw [add_zero] at hupper
  apply (mem_boundedConstructible_iff R K).2
  constructor
  · refine ⟨-1, 0, fun n hn ↦ ?_⟩
    rcases hn with hn | hn
    · apply detect
      intro a
      have hb := (hlfp (S.domain a) ((H a).obj F) ((H a).obj G)
        (lfp a F (hS a).1) (lfp a G (hS a).2)).1
      have hz := (DerivedCategory.isGE_iff _ (-1)).1 hb n hn
      exact hz.of_iso
        (((H a).leftDerivedFunctorHomologyFunctorIso n).app K ≪≫
          (DerivedCategory.homologyFunctor _ n).mapIso (e a))
    · exact (DerivedCategory.isLE_iff K 0).1 hupper n hn
  · intro n
    refine ⟨S, fun a ↦ ?_⟩
    apply localFinitePresentation_of_comap (inv (condensedPullbackHom Λ (S.immersion a)))
    apply localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _)
    exact hom_lfp a n

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek supportPullback
attribute [local irreducible] closedSupportProjection openSupportProjection

/-- The projection formula for a locally closed immersion `j ≫ i`, with `j` an open
immersion and `i` a closed immersion of Noetherian schemes: for arbitrary unbounded complexes
`L` on `S` and `M` on `X`, the natural isomorphism `a_! L ⊗ᴸ M ≅ a_! (L ⊗ᴸ a^* M)`, where
`a = j ≫ i` and `a_! = Ri_* ∘ j_!`.

It is the closed support projection isomorphism `closedSupportProjection` for `i` (applied to
`j_! L` and `M`), followed by the inverse of the open support projection isomorphism
`openSupportProjection` for `j` (applied to `L` and `i^* M`), conjugated by the identifications
`Ri_* ≅ i_*`, `supportPullback ≅ upperStar` and `(j ≫ i)^* ≅ j^* ∘ i^*`. -/
noncomputable def immersionLowerShriekProjectionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (L : DerivedCategory (supportModules Λ S))
    (M : DerivedCategory (supportModules Λ X)) :
    ((derivedTensor Λ X).obj
        ((lowerStar Λ i).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj M ≅
      (lowerStar Λ i).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj
          (((derivedTensor Λ S).obj L).obj
            ((upperStar Λ (j ≫ i)).mapDerivedCategory.obj M))) :=
  have hij : Set.range i.base = (Set.range i.openComplement.ι.base)ᶜ := by
    simp [Scheme.Hom.coe_openComplement]
  letI : PreservesFiniteColimits (lowerStar Λ i) :=
    closedSupport_lowerStarExact Λ i i.openComplement.ι hij
  let qi := (lowerStar Λ i).mapDerivedCategory
  let qj := (openImmersionLowerShriek Λ j).mapDerivedCategory
  let pi := (upperStar Λ i).mapDerivedCategory
  let ei := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ i)
  let ej := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ j)
  let ecomp := Functor.mapDerivedCategoryNatIso (upperStarComp Λ j i) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ j)).symm
  let er := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  haveI : IsIso (closedSupportProjection Λ i (qj.obj L) M) :=
    (openClosedSupportProjectionFormula Λ i i.openComplement.ι hij).1 (qj.obj L) M
  haveI : IsIso (openSupportProjection Λ j L (pi.obj M)) :=
    (openClosedSupportProjectionFormula Λ j.closedComplement j
      j.range_closedComplement).2 L (pi.obj M)
  ((derivedTensor Λ X).mapIso (er.app (qj.obj L))).app M ≪≫
    asIso (closedSupportProjection Λ i (qj.obj L) M) ≪≫
    qi.mapIso (((derivedTensor Λ Z).obj (qj.obj L)).mapIso (ei.app M)) ≪≫
    qi.mapIso (asIso (openSupportProjection Λ j L (pi.obj M))).symm ≪≫
    qi.mapIso (qj.mapIso (((derivedTensor Λ S).obj L).mapIso
      (ej.app (pi.obj M) ≪≫ (ecomp.app M).symm))) ≪≫
    (er.app _).symm

/-- Inverse image, uncompleted relative derived tensor and locally closed extension by zero
preserve bounded constructibility over the integral coefficient ring. The locally closed functor
is written explicitly as open extension by zero followed by derived closed direct image; the
latter is ordinary direct image on Noetherian schemes. Finite coefficient fields are represented
inside the fixed algebraic closure, with their induced valuation and ring of integers.

This theorem records clauses (1)--(3). Clause (4), the projection formula for arbitrary
unbounded complexes, is the natural isomorphism `immersionLowerShriekProjectionIso` (applied
with coefficient `Profinite.padicIntegersRingObj ℓ E.val`).

Source: blueprint main-20261015, sk-lem-integral-models-operations, clauses (1)--(4)
(blueprint: lemma-integral-models).

Proof plan (the reviewed DAG proof, retaining the finite constant scalar convention):

1. Use the integral coefficient ring sheaf $R_T=\mathcal O_{E,T}$ and write $A=\mathcal O_E$.
Here $\Dbc(T,A)$ means bounded complexes with constructible cohomology, with finite constant
local models $R_V\otimes_A P$ for finitely presented scalar $A$-modules $P$, as in
[definition-constructible-sheaves, sk-def-sfb-bounded-constructible]. Thus we can prove membership
directly from cohomology and strata; we do not assume that an arbitrary bounded complex of
finite free modules splits into its terms. No additional completeness condition is inserted into
this definition.

2. For clause (1), [lemma-inverse-image-coefficient-sheaves] identifies $f^*R_Y=R_X$ and says that
module pullback is exact inverse image. It therefore preserves kernels, images, cokernels and
cohomology, so $H^q(f^*K)=f^*H^q(K)$ with the same bounds. For each constructible $H^q(K)$ pull
its finite stratification back to $X$ using [lemma-constructible-pullback-stratification]. Pull
each pro-étale covering of a stratum back to its fibre product with $X$; it is again a covering:
weakly étale arrows remain weakly étale by [lem-weil-pbc-weakly-etale-composition-base-change],
and the family remains fpqc by [lem-galois-fpqc-covering-base-change]. The covering definition
[definition-small-pro-etale-site--1] then applies, even though the new base is not an object of the
old small site. A scalar finite presentation $A^m\to A^n\to P\to0$ gives $R_V^m\to R_V^n\to
R_V\otimes_A P\to0$; exact inverse image pulls this cokernel presentation back to the same
scalar matrix over the new coefficient ring. Thus the pulled-back cohomology has finite constant
local models. The pulled-back strata are locally closed and hence constructible on the
Noetherian scheme $X$. This proves $f^*K\in\Dbc(X,A)$ for every $f$, without any finite-type or
field-base hypothesis.

3. For clause (3), first take an open immersion $j:U\hookrightarrow T$ and its complementary
closed immersion $i:Z\hookrightarrow T$. Every open subset of a Noetherian topological space is
quasi-compact, by Noetherian induction on closed subsets: if a finite subcover did not exist,
choose a minimal closed subset on which it fails; removing one cover member containing a point
gives a proper closed subset, covered finitely by minimality, and adjoining that member
contradicts minimality. Apply this standard lemma to the underlying Noetherian spaces; the open
immersion is quasi-compact. With the inverse-image coefficient rings,
[lem-weil-pbc-proetale-ringed-open-closed] says that $j_!$ and $i_*$ are exact, restrict to the
identity on their own loci, and restrict to zero on the complementary loci. The coefficient
rings agree with $R_U,R_Z$ by [lemma-inverse-image-coefficient-sheaves]. Given a finite
stratification for a constructible sheaf on $U$ (respectively $Z$), regard its strata as locally
closed subschemes of $T$ and append the complementary closed (respectively open) locus. On the
original strata the extended sheaf has the same scalar local models; on the added locus its
model is zero. Hence both functors preserve constructible sheaves. Since they are exact, their
termwise functors commute with cohomology and preserve bounds, proving preservation of $\Dbc$.
Apply the open conclusion to $u:S\hookrightarrow\overline S$ and then the closed conclusion to
$i:\overline S\hookrightarrow X$ to obtain $a_!L=i_*u_!L\in\Dbc(X,A)$.

4. For the tensor calculation first take constructible sheaves $F,G$ in degree zero. Intersect
their finite stratifications, forming the actual fibre products of strata using
[lemma-constructible-pullback-stratification]; the intersections are locally closed, disjoint
and cover $X$. On each stratum $T$ intersect the two pro-étale trivializing covers by fibre
products $V_\alpha\times_T W_\beta$. The base-change and composition axioms of a site
[def-weil-pbc-sites-and-cohomology] make this a covering: first pull the second cover back over
each member of the first, then compose. On its objects $V$, exact inverse image and the scalar
cokernel argument of step 2 identify the two sheaves with $R_V\otimes_A P$ and $R_V\otimes_A Q$
for finitely presented scalar modules $P,Q$. By
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback], the restriction of $F\otimes^{\mathbf
L}_{R_X}G$ is the derived tensor of these two models.

5. The ring $A=\mathcal O_E$ is a DVR, and each nonzero element is a unit times a power of a
uniformizer $\pi$ [lem-weil-l-adic-extension-integers-dvr]. Choose a finite free surjection
$A^n\twoheadrightarrow P$, with kernel $N\subset A^n$. By
[lem-sc-dvr-saturation-line-smith-normal-form] the inclusion of $N$ has a diagonal matrix in
finite bases, of rank at most $n$. Each diagonal entry is nonzero because the inclusion is
injective, and can be replaced by $\pi^r$ after multiplying a basis vector by a unit. Taking the
cokernel gives a finite direct sum decomposition of $P$ into copies of $A$ and $A/\pi^r$ with
$r\geq1$; unit entries give zero summands. Do the same for $Q$. Right exactness of ordinary
tensor gives decompositions of the two local models into copies of $R=R_V$ and $R/\pi^rR$.

6. The constant-to-completed coefficient map $A_V\to R_V$ is flat by clause (1) of
[lemma-integral-models--1]. The constant presheaf map given by
multiplication $A\xrightarrow{\pi^r}A$ is injective because $A$ is a domain. Its sheafification
is multiplication on the constant ring sheaf [def-weil-pbc-constant-sheaf] and is still
injective by exact sheafification [situation-conventions]. Flatness here means that
the sheaf tensor functor $-\otimes_{A_V}R_V$ is exact [def-pc-flat-sheaf-modules]. Applying that
functor to the kernel sequence $0\to A_V\xrightarrow{\pi^r}A_V$, and identifying
$A_V\otimes_{A_V}R_V=R_V$, gives the kernel sequence $0\to R_V\xrightarrow{\pi^r}R_V$. Hence
this multiplication on $R$ is injective. Consequently $[R\xrightarrow{\pi^r}R]$, placed in
degrees $-1,0$, resolves $R/\pi^rR$. It is K-flat directly from [def-pc-kflat-complex]:
tensoring it with any acyclic complex gives the cone of multiplication by $\pi^r$ on that
complex, up to the usual shift, which is acyclic by the cohomology long exact sequence
[lem-sf-derived-homology-long-exact]. Also $R[0]$ is K-flat because tensoring with it is the
identity. Thus these explicit complexes compute the derived tensors, using
[sk-def-sfb-derived-tensor-hom].

7. Tensoring a free summand with another summand leaves it in degree zero. For two torsion
summands the explicit resolution of step 6 gives $$ (R/\pi^rR)\otimes_R^{\mathbf
L}(R/\pi^sR)\simeq[R/\pi^sR\xrightarrow{\pi^r}R/\pi^sR]. $$ If $r\geq s$, the differential is
zero, so both cohomology sheaves are $R/\pi^sR$. If $r<s$, the cokernel is $R/\pi^rR$ and the
kernel is $\pi^{s-r}R/\pi^sR\cong R/\pi^rR$. To check the latter for sheaves, lift a quotient
section locally to $x\in R$. The equation $\pi^r x=0$ modulo $\pi^s$ means, after a refinement,
$\pi^r x=\pi^s y$. Cancellation using step 6 gives $x=\pi^{s-r}y$. For the map $R\to R/\pi^sR$,
$y\mapsto\pi^{s-r}y$, a section in its kernel locally satisfies $\pi^{s-r}y=\pi^s z$.
Injectivity of $\pi^{s-r}$ gives $y=\pi^r z$; conversely every $y=\pi^r z$ maps to zero. Its
kernel is therefore exactly $\pi^rR$. Thus in both cases $H^{-1}$ and $H^0$ are
$R/\pi^{\min(r,s)}R$, and other cohomology vanishes. Finite sums give the calculation for the
local models in step 5. These resulting cohomology sheaves have finite constant scalar models,
and all local tensors have amplitude in $[-1,0]$. Exact restrictions commute with cohomology. By
[lem-weil-pbc-noetherian-stratum-detection], these restrictions detect vanishing outside that
interval globally. The models themselves give constructibility by
[definition-constructible-sheaves]. Hence $F\otimes^{\mathbf L}G\in\Dbc(X,A)$.

8. Extend the sheaf calculation to clause (2) by two finite cohomological inductions. The
standard truncation triangles of [def-sbc-standard-tstructure-derived-category] give, for
bounded $K$ with cohomology in $[a,b]$, $$\tau_{\leq b-1}K\longrightarrow K\longrightarrow
H^b(K)[-b]\longrightarrow(\tau_{\leq b-1}K)[1].$$ Derived tensor is exact in each variable
[lem-weil-pbc-ringed-projection-mate-exact], and $\Dbc(X,A)$ is a triangulated subcategory on
Noetherian $X$ [sk-def-sfb-bounded-constructible]. Fix a constructible sheaf $G$. The empty
interval is the zero case and the one-degree case is step 7 shifted. Tensoring the displayed
triangle with $G$, the first term is handled by induction on $b-a$ and the third by the sheaf
case; closure under triangles gives $K\otimes^{\mathbf L}G$. Now fix such a $K$ and induct on an
interval $[c,d]$ containing the cohomology of $M$. The empty interval is again zero, the
one-degree case is the conclusion just established shifted, and the triangle for $M$ gives outer
terms $K\otimes^{\mathbf L}\tau_{\leq d-1}M$ and $(K\otimes^{\mathbf L}H^d(M))[-d]$. They belong
to $\Dbc$ by induction and the first induction. Therefore the middle term $K\otimes^{\mathbf
L}M$ belongs to $\Dbc$. All these are ambient derived tensors; no completion is taken.

9. For clause (4), prove the open projection formula on the unbounded ambient categories. For
$j:U\hookrightarrow T$, the pro-étale site of $U$ is the localized site of $T$ at $U$
[lem-weil-proetale-weakly-etale-localization], and the coefficient ring restricts to $R_U$
[lemma-inverse-image-coefficient-sheaves]. Choose a representative complex for $L$ and a K-flat
resolution $P\to M$ with flat terms [lem-pc-kflat-resolution]. The complex $j^*P$ is K-flat with
flat terms by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Thus $j_!L\otimes^{\mathbf
L}M$ is represented by $j_!L\otimes P$, and $L\otimes^{\mathbf L}j^*M$ by $L\otimes j^*P$. Apply
[lem-weil-pbc-ringed-slice-extension-tensor] in each bidegree. Since $j_!$ is left adjoint to
$j^*$ and exact [lem-weil-pbc-proetale-ringed-open-closed], it preserves the direct sums in
totalization [situation-conventions] and induces its termwise derived
functor. Write the bidegree isomorphism as $\theta_{p,q}:(j_!L^p)\otimes P^q\to j_!(L^p\otimes
j^*P^q)$. Naturality in its first argument makes $\theta$ commute with the maps induced by
$d_L^p$, and naturality in its second argument makes it commute with the maps induced by
$d_P^q$. Additivity then makes it commute with their signed sum $d_L\otimes1+(-1)^p1\otimes d_P$
in bidegree $(p,q)$. Summing these maps over $p+q=n$ gives an isomorphism of total complexes,
naturally $$j_!L\otimes^{\mathbf L}M\simeq j_!(L\otimes^{\mathbf L}j^*M).$$ This argument
imposes no bounds or constructibility on $L,M$.

10. For a closed immersion $i:Z\hookrightarrow T$ with open complement $j$, $i_*$ is exact since
$T$ is Noetherian [lem-weil-pbc-proetale-ringed-open-closed]. Thus $Ri_*=i_*$ termwise and
$Li^*=i^*$ because the coefficient system is Cartesian [lemma-inverse-image-coefficient-sheaves].
The natural projection map of [lem-weil-pbc-ringed-projection-mate-exact] is $$i_*N\otimes^{\mathbf
L}M\longrightarrow i_*(N\otimes^{\mathbf L}i^*M).$$ Its restriction by $i^*$ is the identity on
$N\otimes^{\mathbf L}i^*M$: the defining mate uses the counit $i^*i_*N\to N$, which is an
isomorphism, and the monoidal pullback comparison
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Its restriction by $j^*$ is a map $0\to0$,
since $j^*i_*=0$ and pullback commutes with derived tensor. The identities and vanishings are
those of [lem-weil-pbc-proetale-ringed-open-closed]. The two strata $Z,U$ jointly detect
isomorphisms by [lem-weil-pbc-noetherian-stratum-detection], so this projection map is an
isomorphism for arbitrary $N,M$.

11. Finally apply step 10 with $N=u_!L$ and then step 9 inside $\overline S$: $$
(i_*u_!L)\otimes^{\mathbf L}M\simeq i_*(u_!L\otimes^{\mathbf L}i^*M)\simeq
i_*u_!(L\otimes^{\mathbf L}u^*i^*M)=a_!(L\otimes^{\mathbf L}a^*M). $$ Here $a^*=u^*i^*$ by
composition of inverse-image functors [lem-weil-pbc-site-morphism-composition] and the Cartesian
coefficient identifications already fixed. Both factors are the ambient, exact immersion
functors from step 3. This gives clause (4), `immersionLowerShriekProjectionIso`, for arbitrary
derived objects; it is natural in both arguments.
-/
theorem integralModels_operations (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) f).mapDerivedCategory).obj K)) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X] (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj M)) ∧
    (∀ {S Z X : Scheme.{u}} [IsNoetherian S] [IsNoetherian Z] [IsNoetherian X]
      (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) S))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) S L →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj
          (((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.val)
            j).mapDerivedCategory).obj L))) := by
  have hE : FiniteDimensional ℚ_[ℓ] E.val := E.property
  refine ⟨?_, ?_, ?_⟩
  · intro X Y _ _ f K hK
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    have hX := (adicConstructibilityPredicateComparison ℓ X Λ (.integral E.val)).1
    have hY := (adicConstructibilityPredicateComparison ℓ Y Λ (.integral E.val)).1
    refine ⟨(upperStar Λ f).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
    apply (hX _).1
    exact constructible_of_iso
      (((upperStar Λ f).mapDerivedCategoryHomologyFunctorIso n).app K)
      (isConstructibleModuleObject_upperStar Λ f _ ((hY _).2 (hK.2 n)))
  · intro X _ K M hK hM
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    let P := boundedConstructible (condensedRingObj Λ X)
    have hp := (adicConstructibilityPredicateComparison ℓ X Λ (.integral E.val)).2
    rw [← hp] at hK hM ⊢
    have : P.IsTriangulated := isTriangulated_boundedConstructible_ellAdic_padicIntegers X ℓ E.val
    change P (K ⊗ M)
    apply prop_of_boundedConstructibleModule (P.inverseImage (tensorLeft K)) ?_ hM
    intro G hG
    exact prop_of_boundedConstructibleModule
      (P.inverseImage (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)))
      (fun F hF ↦ tensor_single_noetherian Λ
        (fun Y _ F G hF hG ↦ PadicIntegersRingObj.lfp_tensor_single Y ℓ E.val F G hF hG)
        X F G hF hG) hK
  · intro S Z X _ _ _ j _ i _ L hL
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    have ho : ScalarModelImmersionExtensionAssertions Λ j j.closedComplement :=
      ((scalarModelImmersionExtension ℓ j j.closedComplement
      (by simp [j.range_closedComplement])).2.2.2.1 E).1
    have hc : ScalarModelImmersionExtensionAssertions Λ i.openComplement.ι i :=
      ((scalarModelImmersionExtension ℓ i.openComplement.ι i
      (by simp [Scheme.Hom.coe_openComplement])).2.2.2.1 E).1
    have : PreservesFiniteColimits (lowerStar Λ i) := hc.2.2.2.1
    have hiZ : ObjectProperty.IsClosedUnderIsomorphisms
        (IsConstantModelConstructible Λ Z) :=
      (constantModelConstructibleFiniteTor_wellDefined Λ Z).1
    have hiX : ObjectProperty.IsClosedUnderIsomorphisms
        (IsConstantModelConstructible Λ X) :=
      (constantModelConstructibleFiniteTor_wellDefined Λ X).1
    have hJ : constantModelBoundedConstructible Λ Z
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L) := by
      refine ⟨(openImmersionLowerShriek Λ j).bounded_mapDerivedCategory_obj hL.1,
        fun n ↦ ?_⟩
      exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ Z)
        (((openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso n).app L)
        (ho.2.2.2.2.1 _ (hL.2 n))
    have he := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
    refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso (he.app _).symm
      ((lowerStar Λ i).bounded_mapDerivedCategory_obj hJ.1), fun n ↦ ?_⟩
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      (((lowerStar Λ i).rightDerivedFunctorHomologyFunctorIso n).app _)
      (hc.2.2.2.2.2.1 _ (hJ.2 n))

end AlgebraicGeometry.ProEtale.CondensedRing
