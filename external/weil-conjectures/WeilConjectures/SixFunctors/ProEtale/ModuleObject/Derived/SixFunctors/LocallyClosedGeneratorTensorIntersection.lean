/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

import all WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
import WeilConjectures.CategoryTheory.ModuleObjects.ResidueOrdinary.IntegralResidueOrdinaryMonoidal
import all WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedReconstruction
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
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
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
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
import all Mathlib.Analysis.Normed.Module.FiniteDimension
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
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates

/-! # Tensor of locally closed lisse generators

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-field/
sk-thm-sf-pf-field-tensor.proof.md,
Proof (1) (blueprint: lem-sfb-locally-closed-generator-tensor-intersection).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Both orders of open/closed factorization, using Mathlib's factorization data without a new
factorization notion. Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
abbrev GeneratorFactorization {S X : Scheme.{u}} (a : S ⟶ X) :=
  MorphismProperty.MapFactorizationData @IsClosedImmersion @IsOpenImmersion a ⊕
    MorphismProperty.MapFactorizationData @IsOpenImmersion @IsClosedImmersion a

/-- The actual module extension `j_! i_*`, or `i_* j_!`, for the given factorization.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) :
    Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  match A with
  | .inl A =>
    letI : IsOpenImmersion A.p := A.hp
    lowerStar Λ A.i ⋙ openImmersionLowerShriek Λ A.p
  | .inr A =>
    letI : IsOpenImmersion A.i := A.hi
    openImmersionLowerShriek Λ A.i ⋙ lowerStar Λ A.p

/-- Restriction normalization: inverse open unit and closed counit in factorization order,
with the canonical inverse-image composition. Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) :
    generatorExtension Λ A ⋙ upperStar Λ a ⟶ 𝟭 _ :=
  match A with
  | .inl A =>
    letI : IsOpenImmersion A.p := A.hp
    (Functor.associator (lowerStar Λ A.i) (openImmersionLowerShriek Λ A.p)
      (upperStar Λ a)).hom ≫
      Functor.whiskerLeft (lowerStar Λ A.i)
        (Functor.whiskerLeft (openImmersionLowerShriek Λ A.p)
          ((eqToIso (congrArg (upperStar Λ) A.fac.symm) ≪≫
            upperStarComp Λ A.i A.p).hom) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (asIso (openImmersionLowerShriekUpperStarAdjunction Λ A.p).unit).inv
            (upperStar Λ A.i) ≫
          (Functor.leftUnitor _).hom) ≫
      (upperStarLowerStarAdjunction Λ A.i).counit
  | .inr A =>
    letI : IsOpenImmersion A.i := A.hi
    (Functor.associator (openImmersionLowerShriek Λ A.i) (lowerStar Λ A.p)
      (upperStar Λ a)).hom ≫
      Functor.whiskerLeft (openImmersionLowerShriek Λ A.i)
        (Functor.whiskerLeft (lowerStar Λ A.p)
          ((eqToIso (congrArg (upperStar Λ) A.fac.symm) ≪≫
            upperStarComp Λ A.i A.p).hom) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (upperStarLowerStarAdjunction Λ A.p).counit
            (upperStar Λ A.i) ≫
          (Functor.leftUnitor _).hom) ≫
      (asIso (openImmersionLowerShriekUpperStarAdjunction Λ A.i).unit).inv

/-- Source bifunctor on the full categories of lisse modules, in degree zero.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorTensorSource
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}} {a : S ⟶ X} {b : T ⟶ X}
    (A : GeneratorFactorization a) (B : GeneratorFactorization b) :=
  (((Functor.whiskeringLeft₂ _).obj
    ((ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S))) ⋙
      generatorExtension Λ A ⋙ DerivedCategory.singleFunctor _ 0)).obj
    ((ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T))) ⋙
      generatorExtension Λ B ⋙ DerivedCategory.singleFunctor _ 0)).obj (derivedTensor Λ X)

/-- Ordinary relative tensor after the two actual fibre-product projections.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorIntersectionModule
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}} (a : S ⟶ X) (b : T ⟶ X) :=
  (((Functor.whiskeringLeft₂ _).obj (upperStar Λ (pullback.fst a b))).obj
    (upperStar Λ (pullback.snd a b))).obj (MonoidalCategory.curriedTensor _)

/-- Target bifunctor: extend the underived relative tensor from the actual fibre product.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorTensorTarget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}} (a : S ⟶ X) (b : T ⟶ X)
    (C : GeneratorFactorization (pullback.fst a b ≫ a)) :=
  (Functor.postcompose₂.obj (generatorExtension Λ C ⋙ DerivedCategory.singleFunctor _ 0)).obj
    ((((Functor.whiskeringLeft₂ _).obj
      (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)))).obj
      (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)))).obj
      (generatorIntersectionModule Λ a b))

section GeneratorTensorProof

section FiniteFreeTensor
universe uBip vBip
variable {C : Type uBip} [Category.{vBip} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]

end FiniteFreeTensor

attribute [local irreducible] upperStar upperStarComp upperStarCongr
  Mod.monoidalCategoryStruct

private theorem immersion_noetherian {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] (a : S ⟶ X) [IsImmersion a] :
    IsLocallyNoetherian S ∧ CompactSpace S := by
  let : IsNoetherian X := ⟨⟩
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  exact ⟨LocallyOfFiniteType.isLocallyNoetherian a, inferInstance⟩

attribute [local irreducible] upperStarLowerStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorRestriction_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) : IsIso (generatorRestriction Λ A) := by
  rcases A with A | A
  · let : IsOpenImmersion A.p := A.hp
    let : IsClosedImmersion A.i := A.hi
    have := moduleCounitOfAbelian Λ A.i (ProEtale.abelian_closed_counit A.i)
    dsimp only [generatorRestriction]
    infer_instance
  · let : IsClosedImmersion A.p := A.hp
    let : IsOpenImmersion A.i := A.hi
    have := moduleCounitOfAbelian Λ A.p (ProEtale.abelian_closed_counit A.p)
    dsimp only [generatorRestriction]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedPullback_zero_of_disjoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z X Y : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (g : Y ⟶ X)
    (hg : Disjoint (Set.range g) (Set.range i))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsZero ((upperStar Λ g).obj ((lowerStar Λ i).obj M)) := by
  let V := Scheme.openComplementOfIsClosedImmersion i
  have hV : Set.range V.ι = (Set.range i)ᶜ := by
    simp [V, Scheme.openComplementOfIsClosedImmersion]
  have h := openRestrictionPushforwardZero Λ i V.ι hV M
  have hgV : Set.range g ⊆ Set.range V.ι := by
    rw [hV]
    exact hg.subset_compl_right
  let f := IsOpenImmersion.lift V.ι g hgV
  have hf : f ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ hgV
  exact ((upperStar Λ f).map_isZero h).of_iso
    ((upperStarCongr Λ hf.symm).app _ ≪≫ (upperStarComp Λ f V.ι).app _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedOpenExtension_zero_of_disjoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S V X Y : Scheme.{u}}
    (i : S ⟶ V) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    (g : Y ⟶ X) (hg : Disjoint (Set.range g) (Set.range (i ≫ j)))
    (P : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    IsZero ((upperStar Λ g).obj
      ((openImmersionLowerShriek Λ j).obj ((lowerStar Λ i).obj P))) := by
  have hdis : Disjoint (Set.range (pullback.snd g j)) (Set.range i) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    apply Set.disjoint_left.mp hg
      (show j (pullback.snd g j y) ∈ Set.range g from
        ⟨pullback.fst g j y, by
          exact congrArg (fun f : pullback g j ⟶ X ↦ f y) pullback.condition⟩)
    exact ⟨z, congrArg j hz⟩
  have hz := closedPullback_zero_of_disjoint Λ i (pullback.snd g j) hdis P
  have hz' : IsZero ((ProEtale.upperStar Ab.{u + 1} (pullback.snd g j)).obj
      ((lowerStar Λ i).obj P).X) :=
    ((Mod.forget _).map_isZero hz).of_iso
      (upperStarObjXIso Λ (pullback.snd g j) _).symm
  have e := (ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1}
    (IsPullback.of_hasPullback g j).flip).app ((lowerStar Λ i).obj P).X
  apply isZero_of_isZero_X Λ
  exact ((ProEtale.openImmersionLowerShriek Ab.{u + 1} (pullback.fst g j)).map_isZero
    hz').of_iso (upperStarObjXIso Λ g _ ≪≫ e.symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedBaseChange_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (i : Z ⟶ X) [IsClosedImmersion i] (g : Y ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (h : IsZero ((upperStar Λ (pullback.snd g i)).obj P)) :
    IsZero ((upperStar Λ g).obj ((lowerStar Λ i).obj P)) := by
  let U := Scheme.openComplementOfIsClosedImmersion i
  have hU : Set.range U.ι = (Set.range i)ᶜ := by
    simp [U, Scheme.openComplementOfIsClosedImmersion]
  obtain ⟨hu, hz, delta, gamma, hd, hg, alpha, beta, ha, hb⟩ :=
    ProEtale.ringSheaf_baseChange_mates i U.ι hU (condensedRingObj Λ X) g
  let := hu
  let := hz
  let P' := (Mod.comap (condensedPullbackHom Λ i)).obj P
  have e := (Mod.forget _).mapIso (beta.app P')
  have h' : IsZero ((ProEtale.upperStar Ab.{u + 1} (pullback.snd g i)).obj P.X) :=
    ((Mod.forget _).map_isZero h).of_iso
      (upperStarObjXIso Λ (pullback.snd g i) P).symm
  apply isZero_of_isZero_X Λ
  exact ((ProEtale.lowerStar Ab.{u + 1} (pullback.fst g i)).map_isZero h').of_iso
    (upperStarObjXIso Λ g _ ≪≫ e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorExtension_support
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    {a : S ⟶ X} (A : GeneratorFactorization a) (g : Y ⟶ X)
    (hg : Disjoint (Set.range g) (Set.range a))
    (P : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    IsZero ((upperStar Λ g).obj ((generatorExtension Λ A).obj P)) := by
  rcases A with A | A
  · let : IsClosedImmersion A.i := A.hi
    let : IsOpenImmersion A.p := A.hp
    have hgp : Disjoint (Set.range g) (Set.range (A.i ≫ A.p)) := by
      rw [A.fac]
      exact hg
    exact closedOpenExtension_zero_of_disjoint Λ A.i A.p g hgp P
  · let : IsClosedImmersion A.p := A.hp
    let : IsOpenImmersion A.i := A.hi
    apply closedBaseChange_zero Λ A.p g
    apply isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ A.i
    rw [disjoint_comm, Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    apply Set.disjoint_left.mp hg
      (show A.p (pullback.snd g A.p y) ∈ Set.range g from
        ⟨pullback.fst g A.p y, by
          exact congrArg (fun f : pullback g A.p ⟶ X ↦ f y) pullback.condition⟩)
    refine ⟨z, ?_⟩
    have hf := congrArg (fun f : S ⟶ X ↦ f z) A.fac
    exact hf.symm.trans (congrArg A.p hz)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleOpenSupportedCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hij : Set.range j = (Set.range i)ᶜ)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hi : IsZero ((upperStar Λ i).obj N)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app N) := by
  have hzero : IsZero ((ProEtale.upperStar Ab.{u + 1} i).obj N.X) :=
    ((Mod.forget _).map_isZero hi).of_iso (upperStarObjXIso Λ i N).symm
  have hc := ProEtale.abelian_open_supported_counit i j hij N.X hzero
  apply (Adjunction.isIso_counit_app_iff_mem_essImage _).2
  apply mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ j
  exact (Adjunction.isIso_counit_app_iff_mem_essImage _).1 hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleClosedSupportedUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hij : Set.range j = (Set.range i)ᶜ)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hj : IsZero ((upperStar Λ j).obj N)) :
    IsIso ((upperStarLowerStarAdjunction Λ i).unit.app N) := by
  have hzero : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj N.X) :=
    ((Mod.forget _).map_isZero hj).of_iso (upperStarObjXIso Λ j N).symm
  exact moduleUnitOfAbelian Λ i N
    ((ProEtale.abelian_closed_support_counit_and_unit i j hij).2 N.X hzero)

private instance generatorExtension_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) : (generatorExtension Λ A).Additive := by
  rcases A with A | A
  · let : IsOpenImmersion A.p := A.hp
    dsimp only [generatorExtension]
    infer_instance
  · let : IsOpenImmersion A.i := A.hi
    dsimp only [generatorExtension]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def generatorExtension_fullyFaithful
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) : (generatorExtension Λ A).FullyFaithful := by
  rcases A with A | A
  · let : IsOpenImmersion A.p := A.hp
    let : IsClosedImmersion A.i := A.hi
    have := moduleCounitOfAbelian Λ A.i (ProEtale.abelian_closed_counit A.i)
    change (lowerStar Λ A.i ⋙ openImmersionLowerShriek Λ A.p).FullyFaithful
    exact (upperStarLowerStarAdjunction Λ A.i).fullyFaithfulROfIsIsoCounit.comp
      (fullyFaithfulOpenImmersionLowerShriek Λ A.p)
  · let : IsOpenImmersion A.i := A.hi
    let : IsClosedImmersion A.p := A.hp
    have := moduleCounitOfAbelian Λ A.p (ProEtale.abelian_closed_counit A.p)
    change (openImmersionLowerShriek Λ A.i ⋙ lowerStar Λ A.p).FullyFaithful
    exact (fullyFaithfulOpenImmersionLowerShriek Λ A.i).comp
      (upperStarLowerStarAdjunction Λ A.p).fullyFaithfulROfIsIsoCounit

universe uC uD vC vD₀

private theorem normalized_comparison_of_essImage
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD₀} D]
    (E : C ⥤ D) (R : D ⥤ C) (_ff : E.FullyFaithful) (η : E ⋙ R ≅ 𝟭 C)
    (N : D) (P : C) (hN : ∃ Q, Nonempty (N ≅ E.obj Q))
    (σ : R.obj N ≅ P) :
    ∃ e : N ≅ E.obj P, R.map e.hom ≫ η.hom.app P = σ.hom := by
  obtain ⟨Q, ⟨eQ⟩⟩ := hN
  let d : Q ≅ P := (η.app Q).symm ≪≫ (R.mapIso eQ).symm ≪≫ σ
  refine ⟨eQ ≪≫ E.mapIso d, ?_⟩
  have hn := η.hom.naturality d.hom
  dsimp at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hn]
  simp only [d, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv]
  simp only [← Category.assoc, Iso.hom_inv_id_app,
    ← R.map_comp, Iso.hom_inv_id, R.map_id, Category.id_comp, Functor.comp_obj]

private theorem disjoint_comp_immersion
    {S T V X : Scheme.{u}} (i : S ⟶ V) (g : T ⟶ V) (j : V ⟶ X)
    [IsImmersion j] (h : Disjoint (Set.range g) (Set.range i)) :
    Disjoint (Set.range (g ≫ j)) (Set.range (i ≫ j)) := by
  rw [Set.disjoint_left]
  rintro x ⟨y, rfl⟩ ⟨z, hz⟩
  exact Set.disjoint_left.mp h ⟨y, rfl⟩ ⟨z, j.isEmbedding.injective hz⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorExtension_reconstruct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    {a : S ⟶ X} (A : GeneratorFactorization a)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hs : ∀ {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]
      (g : Y ⟶ X), Disjoint (Set.range g) (Set.range a) →
        IsZero ((upperStar Λ g).obj N)) :
    Nonempty (N ≅ (generatorExtension Λ A).obj ((upperStar Λ a).obj N)) := by
  rcases A with A | A
  · let : IsClosedImmersion A.i := A.hi
    let : IsOpenImmersion A.p := A.hp
    obtain ⟨hV, hVc⟩ := immersion_noetherian A.p
    let := hV
    let := hVc
    let : IsNoetherian A.Z := ⟨⟩
    obtain ⟨hB, hBc⟩ := immersion_noetherian A.p.closedComplement
    let := hB
    let := hBc
    have houter : Disjoint (Set.range A.p.closedComplement) (Set.range a) := by
      simp only [A.p.range_closedComplement, ← A.fac]
      exact (disjoint_compl_left (a := Set.range A.p)).mono_right
        (Set.range_comp_subset_range A.i A.p)
    have ho := moduleOpenSupportedCounit Λ A.p.closedComplement A.p
      (by rw [A.p.range_closedComplement, compl_compl]) N
      (hs A.p.closedComplement houter)
    let U := Scheme.openComplementOfIsClosedImmersion A.i
    have hU : Set.range U.ι = (Set.range A.i)ᶜ := by
      simp [U, Scheme.openComplementOfIsClosedImmersion]
    obtain ⟨hU₁, hU₂⟩ := immersion_noetherian U.ι
    let := hU₁
    let := hU₂
    have hd : Disjoint (Set.range (U.ι ≫ A.p)) (Set.range a) := by
      simpa only [A.fac] using disjoint_comp_immersion A.i U.ι A.p
        (by rw [hU]; exact disjoint_compl_left)
    have hz := (hs (U.ι ≫ A.p) hd).of_iso
      ((upperStarComp Λ U.ι A.p).app N).symm
    have hi := moduleClosedSupportedUnit Λ A.i U.ι hU
      ((upperStar Λ A.p).obj N) hz
    have hF : generatorExtension Λ (.inl A) =
        lowerStar Λ A.i ⋙ openImmersionLowerShriek Λ A.p := rfl
    have hobj := (Functor.congr_obj hF ((upperStar Λ a).obj N)).trans
      (Functor.comp_obj (lowerStar Λ A.i) (openImmersionLowerShriek Λ A.p)
        ((upperStar Λ a).obj N))
    refine ⟨(asIso ((openImmersionLowerShriekUpperStarAdjunction Λ A.p).counit.app N)).symm
      ≪≫ (openImmersionLowerShriek Λ A.p).mapIso
        (asIso ((upperStarLowerStarAdjunction Λ A.i).unit.app
          ((upperStar Λ A.p).obj N))) ≪≫ ?_ ≪≫ eqToIso hobj.symm⟩
    exact (openImmersionLowerShriek Λ A.p).mapIso ((lowerStar Λ A.i).mapIso
      (((upperStarComp Λ A.i A.p).symm ≪≫ upperStarCongr Λ A.fac).app N))
  · let : IsOpenImmersion A.i := A.hi
    let : IsClosedImmersion A.p := A.hp
    obtain ⟨hV, hVc⟩ := immersion_noetherian A.p
    let := hV
    let := hVc
    let : IsNoetherian A.Z := ⟨⟩
    let U := Scheme.openComplementOfIsClosedImmersion A.p
    have hU : Set.range U.ι = (Set.range A.p)ᶜ := by
      simp [U, Scheme.openComplementOfIsClosedImmersion]
    obtain ⟨hU₁, hU₂⟩ := immersion_noetherian U.ι
    let := hU₁
    let := hU₂
    have houter : Disjoint (Set.range U.ι) (Set.range a) := by
      simp only [hU, ← A.fac]
      exact (disjoint_compl_left (a := Set.range A.p)).mono_right
        (Set.range_comp_subset_range A.i A.p)
    have ho := moduleClosedSupportedUnit Λ A.p U.ι hU N (hs U.ι houter)
    obtain ⟨hB, hBc⟩ := immersion_noetherian A.i.closedComplement
    let := hB
    let := hBc
    have hd : Disjoint (Set.range (A.i.closedComplement ≫ A.p)) (Set.range a) := by
      simpa only [A.fac] using disjoint_comp_immersion A.i A.i.closedComplement A.p
        (by rw [A.i.range_closedComplement]; exact disjoint_compl_left)
    have hz := (hs (A.i.closedComplement ≫ A.p) hd).of_iso
      ((upperStarComp Λ A.i.closedComplement A.p).app N).symm
    have hi := moduleOpenSupportedCounit Λ A.i.closedComplement A.i
      (by rw [A.i.range_closedComplement, compl_compl]) ((upperStar Λ A.p).obj N) hz
    have hF : generatorExtension Λ (.inr A) =
        openImmersionLowerShriek Λ A.i ⋙ lowerStar Λ A.p := rfl
    have hobj := (Functor.congr_obj hF ((upperStar Λ a).obj N)).trans
      (Functor.comp_obj (openImmersionLowerShriek Λ A.i) (lowerStar Λ A.p)
        ((upperStar Λ a).obj N))
    refine ⟨asIso ((upperStarLowerStarAdjunction Λ A.p).unit.app N) ≪≫
      (lowerStar Λ A.p).mapIso
        (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ A.i).counit.app
          ((upperStar Λ A.p).obj N))).symm ≪≫ ?_ ≪≫ eqToIso hobj.symm⟩
    exact (lowerStar Λ A.p).mapIso ((openImmersionLowerShriek Λ A.i).mapIso
      (((upperStarComp Λ A.i A.p).symm ≪≫ upperStarCongr Λ A.fac).app N))

attribute [local irreducible] generatorExtension generatorRestriction
  generatorIntersectionModule generatorTensorSource generatorTensorTarget
  derivedTensor DerivedCategory.singleFunctors DerivedCategory.homologyFunctor

section TensorAlgebra
universe uA uB vA vB
variable {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
  [MonoidalCategory C] [MonoidalCategory D]

private noncomputable def tensorRestrictionIso (F : C ⥤ D) [F.Monoidal]
    {P Q : C} {L M : D} (e : F.obj P ≅ L) (e' : F.obj Q ≅ M) :
    F.obj (P ⊗ Q) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso F P Q).symm ≪≫ tensorIso e e'

private theorem pullTensor_zero_right [Preadditive D] [HasZeroObject D]
    [MonoidalPreadditive D] (F : C ⥤ D) [F.Monoidal]
    (P Q : C) (h : IsZero (F.obj Q)) : IsZero (F.obj (P ⊗ Q)) :=
  ((tensorLeft (F.obj P)).map_isZero h).of_iso (Functor.Monoidal.μIso F P Q).symm

private theorem pullTensor_zero_left [Preadditive D] [HasZeroObject D]
    [MonoidalPreadditive D] (F : C ⥤ D) [F.Monoidal]
    (P Q : C) (h : IsZero (F.obj P)) : IsZero (F.obj (P ⊗ Q)) :=
  ((tensorRight (F.obj Q)).map_isZero h).of_iso (Functor.Monoidal.μIso F P Q).symm
private theorem mono_map_whiskerLeft (F : C ⥤ D) [F.Monoidal]
    (P : C) {Q Q' : C} (f : Q ⟶ Q') (hm : Mono (F.obj P ◁ F.map f)) :
    Mono (F.map (P ◁ f)) := by
  let := hm
  rw [Functor.Monoidal.map_whiskerLeft]
  infer_instance

private theorem flat_of_kernel_detection [Abelian C] [Abelian D]
    [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
    (F : C ⥤ D) [F.Monoidal] [F.Additive] [PreservesFiniteLimits F]
    (P : C) (hP : ObjectProperty.flat (F.obj P))
    (hker : ∀ {Q Q' : C} (f : Q ⟶ Q'),
      IsZero (F.obj (kernel (P ◁ f))) → IsZero (kernel (P ◁ f))) :
    ObjectProperty.flat P := by
  apply (ObjectProperty.flat_iff_preservesFiniteLimits P).mpr
  have : (MonoidalCategory.tensorLeft P).PreservesMonomorphisms := by
    constructor
    intro Q Q' f hf
    let := hf
    have : PreservesFiniteLimits (MonoidalCategory.tensorLeft (F.obj P)) :=
      hP.tensorLeft.preservesFiniteLimits
    have : Mono (F.map f) := F.map_mono f
    have : Mono (F.map (P ◁ f)) := mono_map_whiskerLeft F P f
      ((MonoidalCategory.tensorLeft (F.obj P)).map_mono (F.map f))
    apply Preadditive.mono_of_isZero_kernel
    apply hker f
    exact (isZero_kernel_of_mono (F.map (P ◁ f))).of_iso
      (PreservesKernel.iso F (P ◁ f))
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels
    (MonoidalCategory.tensorLeft P)
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end TensorAlgebra

attribute [local irreducible] tensorRestrictionIso ObjectProperty.flat

private def universallySupported
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} (a : S ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∀ {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]
    (g : Y ⟶ X), Disjoint (Set.range g) (Set.range a) → IsZero ((upperStar Λ g).obj N)

private theorem supported_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) [IsImmersion a]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : universallySupported Λ a N) (ha : IsZero ((upperStar Λ a).obj N)) : IsZero N := by
  obtain ⟨V, i, j, hi, hj, hc⟩ := IsImmersion.isImmersion_iff_exists.mp
    (inferInstance : IsImmersion a)
  let A : GeneratorFactorization a := .inl ⟨V, i, j, hc, hi, hj⟩
  obtain ⟨e⟩ := generatorExtension_reconstruct Λ A N hN
  exact ((generatorExtension Λ A).map_isZero ha).of_iso e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_tensor_left
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} (a : S ⟶ X)
    (P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : universallySupported Λ a P) :
    universallySupported Λ a (MonoidalCategory.tensorObj P Q) := by
  intro Y _ _ g hg
  exact pullTensor_zero_left (upperStar Λ g) P Q (hP g hg)

private theorem disjoint_pullback_iff
    {S X Y Z : Scheme.{u}} (a : S ⟶ X) (g : Y ⟶ X) (d : Z ⟶ Y) :
    Disjoint (Set.range d) (Set.range (pullback.fst g a)) ↔
      Disjoint (Set.range (d ≫ g)) (Set.range a) := by
  rw [Scheme.Pullback.range_fst, Set.disjoint_left, Set.disjoint_left]
  constructor
  · intro h x ⟨z, hz⟩ hx
    exact h ⟨z, rfl⟩ (show g (d z) ∈ Set.range a from hz.symm ▸ hx)
  · intro h x ⟨z, hz⟩ hx
    exact h ⟨z, congrArg g hz⟩ hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X Y : Scheme.{u}}
    (a : S ⟶ X) (g : Y ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : universallySupported Λ a P) :
    universallySupported Λ (pullback.fst g a) ((upperStar Λ g).obj P) := by
  intro Z _ _ d hd
  exact (hP (d ≫ g) ((disjoint_pullback_iff a g d).mp hd)).of_iso
    ((upperStarComp Λ d g).app P).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_tensor_intersection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a]
    (P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : universallySupported Λ a P) (hQ : universallySupported Λ b Q) :
    universallySupported Λ (pullback.fst a b ≫ a) (MonoidalCategory.tensorObj P Q) := by
  intro Y _ _ g hg
  obtain ⟨hW, hWc⟩ := immersion_noetherian (pullback.fst g a)
  let := hW
  let := hWc
  apply supported_zero Λ (pullback.fst g a)
  · exact supported_pullback Λ a g _ (supported_tensor_left Λ a P Q hP)
  · let d := pullback.fst g a
    have hd : Disjoint (Set.range (d ≫ g)) (Set.range b) := by
      rw [Set.disjoint_left]
      rintro x ⟨z, rfl⟩ hx
      apply Set.disjoint_left.mp hg ⟨d z, rfl⟩
      rw [Scheme.Pullback.range_fst_comp]
      refine ⟨?_, hx⟩
      exact ⟨pullback.snd g a z,
        congrArg (fun f : pullback g a ⟶ X ↦ f z) pullback.condition.symm⟩
    have hz : IsZero ((upperStar Λ d).obj ((upperStar Λ g).obj Q)) :=
      (hQ (d ≫ g) hd).of_iso ((upperStarComp Λ d g).app Q).symm
    exact pullTensor_zero_right (upperStar Λ g ⋙ upperStar Λ d) P Q hz

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_kernel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    (a : S ⟶ X)
    {P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : P ⟶ Q) (hP : universallySupported Λ a P) :
    universallySupported Λ a (kernel f) := by
  intro Y _ _ g hg
  have hm := (hP g hg).mono ((upperStar Λ g).map f)
  exact (isZero_kernel_of_mono ((upperStar Λ g).map f)).of_iso
    (PreservesKernel.iso (upperStar Λ g) f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) [IsImmersion a]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : universallySupported Λ a P) (ha : ObjectProperty.flat ((upperStar Λ a).obj P)) :
    ObjectProperty.flat P := by
  apply flat_of_kernel_detection (upperStar Λ a) P ha
  intro Q Q' f hK
  exact supported_zero Λ a _
    (supported_kernel Λ a (P ◁ f) (supported_tensor_left Λ a P Q hP)) hK

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem lisse_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))
    (hP : IsLisseCoefficientModule Λ P) : ObjectProperty.flat P := by
  obtain ⟨U, hU⟩ := hP
  have hraw := ProEtale.condensed_locally_free_tensor_preservesFiniteLimits
    (condensedRingObj Λ W) P
    ((isLocallyFree_iff P).2 ⟨U, hU⟩)
  apply (ObjectProperty.flat_iff_preservesFiniteLimits P).mpr
  exact preservesFiniteLimits_of_natIso
    (Mod.ResidueOrdinary.relativeTensorRightIso P ≪≫
      (BraidedCategory.tensorLeftIsoTensorRight P).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorExtension_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] {a : S ⟶ X} [IsImmersion a]
    (A : GeneratorFactorization a)
    (P : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hP : IsLisseCoefficientModule Λ P) : ObjectProperty.flat ((generatorExtension Λ A).obj P) := by
  apply supported_flat Λ a _ (fun g hg ↦ generatorExtension_support Λ A g hg P)
  have hr := generatorRestriction_isIso Λ A
  exact ObjectProperty.prop_of_iso ObjectProperty.flat
    ((asIso (generatorRestriction Λ A)).app P).symm (lisse_flat Λ P hP)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def restrictionAlong
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S W X : Scheme.{u}}
    {a : S ⟶ X} (A : GeneratorFactorization a) (r : W ⟶ S)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (upperStar Λ (r ≫ a)).obj ((generatorExtension Λ A).obj L) ≅
      (upperStar Λ r).obj L := by
  have hA := generatorRestriction_isIso Λ A
  exact (upperStarComp Λ r a).app _ ≪≫
    (upperStar Λ r).mapIso ((asIso (generatorRestriction Λ A)).app L)

section RestrictionNaturality
universe uNat vNat
variable {C D E : Type uNat} [Category.{vNat} C] [Category.{vNat} D]
  [Category.{vNat} E]

end RestrictionNaturality

private noncomputable def intersectionRestrictionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    (a : S ⟶ X) (b : T ⟶ X)
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (upperStar Λ (pullback.fst a b ≫ a)).obj
      ((generatorExtension Λ A).obj L ⊗ (generatorExtension Λ B).obj M) ≅
      ((upperStar Λ (pullback.fst a b)).obj L ⊗
        (upperStar Λ (pullback.snd a b)).obj M) := by
  exact tensorRestrictionIso (upperStar Λ (pullback.fst a b ≫ a))
    (restrictionAlong Λ A (pullback.fst a b) L)
    ((upperStarCongr Λ (pullback.condition (f := a) (g := b))).app
      ((generatorExtension Λ B).obj M) ≪≫ restrictionAlong Λ B (pullback.snd a b) M)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryComparison_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    ∃ e : ((generatorExtension Λ A).obj L ⊗ (generatorExtension Λ B).obj M) ≅
      (generatorExtension Λ C).obj
        ((upperStar Λ (pullback.fst a b)).obj L ⊗
          (upperStar Λ (pullback.snd a b)).obj M),
      (upperStar Λ (pullback.fst a b ≫ a)).map e.hom ≫
        (generatorRestriction Λ C).app _ = (intersectionRestrictionIso Λ a b A B L M).hom := by
  have hs : universallySupported Λ (pullback.fst a b ≫ a)
      ((generatorExtension Λ A).obj L ⊗ (generatorExtension Λ B).obj M) :=
    supported_tensor_intersection Λ a b _ _
      (fun g hg ↦ generatorExtension_support Λ A g hg L)
      (fun g hg ↦ generatorExtension_support Λ B g hg M)
  have he := generatorExtension_reconstruct Λ C _ hs
  have hr := generatorRestriction_isIso Λ C
  exact normalized_comparison_of_essImage (generatorExtension Λ C)
    (upperStar Λ (pullback.fst a b ≫ a))
    (generatorExtension_fullyFaithful Λ C) (asIso (generatorRestriction Λ C))
    ((generatorExtension Λ A).obj L ⊗ (generatorExtension Λ B).obj M) _
    ⟨_, he⟩ (intersectionRestrictionIso Λ a b A B L M)

private noncomputable def ordinaryComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
  Classical.choose (ordinaryComparison_exists Λ a b A B C L M)

attribute [local irreducible] ordinaryComparison

section TensorExistence
universe uE vE
variable {D : Type uE} [Category.{vE} D] [MonoidalCategory D]

-- Cache the coproduct and tensor-preservation proofs before specializing to sheaf modules.
private theorem gradedGoodTensor12 [MonoidalClosed D] [BraidedCategory D]
    (X₁ X₂ X₃ : GradedObject ℤ D) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by
  infer_instance

private theorem gradedGoodTensor23 [MonoidalClosed D]
    (X₁ X₂ X₃ : GradedObject ℤ D) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by
  infer_instance

end TensorExistence

attribute [local instance] gradedGoodTensor12 gradedGoodTensor23

section SingleTensor
universe uK vK wK
variable {D : Type uK} [Category.{vK} D] [Abelian D] [MonoidalCategory D]
  [hBraided : BraidedCategory D] [hClosed : MonoidalClosed D] [MonoidalPreadditive D]
  [IsGrothendieckAbelian.{vK} D] [hFlatResolution : Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{wK} D]


attribute [local irreducible] Functor.LaxMonoidal.μ

set_option backward.isDefEq.respectTransparency true in
private noncomputable def singleTensorHom (F G : D) :
    (DerivedCategory.singleFunctor D 0).obj F ⊗
      (DerivedCategory.singleFunctor D 0).obj G ⟶
        (DerivedCategory.singleFunctor D 0).obj (F ⊗ G) :=
  (((DerivedCategory.singleFunctorIsoCompQ D 0).app F).hom ⊗ₘ
      ((DerivedCategory.singleFunctorIsoCompQ D 0).app G).hom) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((CochainComplex.singleFunctor D 0).obj F) ((CochainComplex.singleFunctor D 0).obj G) ≫
    DerivedCategory.Q.map (DerivedCategory.moduleCup_singleTensorIso F G).hom ≫
    ((DerivedCategory.singleFunctorIsoCompQ D 0).app (F ⊗ G)).inv

private theorem singleTensorHom_isIso (F G : D) (hF : ObjectProperty.flat F) :
    IsIso (singleTensorHom F G) := by
  have hK : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((CochainComplex.singleFunctor D 0).obj F) :=
    (CochainComplex.kFlat_single_obj_iff_flat F 0).mpr hF
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((CochainComplex.singleFunctor D 0).obj F)
      ((CochainComplex.singleFunctor D 0).obj G)) := by
    rw [← DerivedCategory.flat_comparison _ _ hK]
    infer_instance
  dsimp only [singleTensorHom]
  infer_instance

private noncomputable def singleTensorIso (F G : D) (hF : ObjectProperty.flat F) :
    (DerivedCategory.singleFunctor D 0).obj F ⊗
      (DerivedCategory.singleFunctor D 0).obj G ≅
        (DerivedCategory.singleFunctor D 0).obj (F ⊗ G) := by
  have := singleTensorHom_isIso F G hF
  exact asIso (singleTensorHom F G)

private noncomputable def singleTensorIsoComp (F G H : D)
    (hF : ObjectProperty.flat F) (e : F ⊗ G ≅ H) :
    (DerivedCategory.singleFunctor D 0).obj F ⊗
      (DerivedCategory.singleFunctor D 0).obj G ≅
        (DerivedCategory.singleFunctor D 0).obj H :=
  singleTensorIso F G hF ≪≫ (DerivedCategory.singleFunctor D 0).mapIso e

end SingleTensor


attribute [local irreducible] singleTensorHom singleTensorIsoComp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientModule_flatResolution
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  Mod.hasFunctorialFlatResolution

set_option maxSynthPendingDepth 16 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def derivedComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hL : IsLisseCoefficientModule Λ L) :
    (DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ A).obj L) ⊗
      (DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ B).obj M) ≅
        (DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ C).obj
          ((upperStar Λ (pullback.fst a b)).obj L ⊗
            (upperStar Λ (pullback.snd a b)).obj M)) := by
  exact singleTensorIsoComp
    (D := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hBraided := Mod.braidedCategory) (hClosed := Mod.monoidalClosed)
    (hFlatResolution := coefficientModule_flatResolution Λ X)
    ((generatorExtension Λ A).obj L) ((generatorExtension Λ B).obj M) _
    (generatorExtension_flat Λ A L hL) (ordinaryComparison Λ a b A B C L M)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] derivedComparison

universe vD wD

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedTensor_eq_curriedTensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    derivedTensor Λ X = curriedTensor
      (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := by
  unfold derivedTensor
  rfl

section TensorComparisonNaturality
universe uTC₁ vTC₁ uTC₂ vTC₂ uTC₃ vTC₃ uTC₄ vTC₄ uTC₅ vTC₅
variable {A₀ : Type uTC₁} [Category.{vTC₁} A₀]
  {B₀ : Type uTC₂} [Category.{vTC₂} B₀]
  {C₀ : Type uTC₃} [Category.{vTC₃} C₀]
  {D₀ : Type uTC₄} [Category.{vTC₄} D₀] [MonoidalCategory D₀]
  {E₀ : Type uTC₅} [Category.{vTC₅} E₀] [MonoidalCategory E₀]

private noncomputable def tensorComparisonSource
    (F : A₀ ⥤ C₀) (G : B₀ ⥤ C₀) (S : C₀ ⥤ D₀) : A₀ ⥤ B₀ ⥤ D₀ :=
  (((Functor.whiskeringLeft₂ _).obj (F ⋙ S)).obj (G ⋙ S)).obj (curriedTensor D₀)

private noncomputable def tensorComparisonTarget
    (R : A₀ ⥤ E₀) (T : B₀ ⥤ E₀) (J : E₀ ⥤ C₀) (S : C₀ ⥤ D₀) : A₀ ⥤ B₀ ⥤ D₀ :=
  (Functor.postcompose₂.obj (J ⋙ S)).obj
    ((((Functor.whiskeringLeft₂ _).obj R).obj T).obj (curriedTensor E₀))

private noncomputable def tensorComparisonNatIso
    (F : A₀ ⥤ C₀) (G : B₀ ⥤ C₀) (R : A₀ ⥤ E₀) (T : B₀ ⥤ E₀)
    (J : E₀ ⥤ C₀) (S : C₀ ⥤ D₀)
    (e : ∀ L M, S.obj (F.obj L) ⊗ S.obj (G.obj M) ≅
      S.obj (J.obj (R.obj L ⊗ T.obj M)))
    (he : ∀ {L L' : A₀} {M M' : B₀} (f : L ⟶ L') (g : M ⟶ M'),
      (S.map (F.map f) ⊗ₘ S.map (G.map g)) ≫ (e L' M').hom =
        (e L M).hom ≫ S.map (J.map (R.map f ⊗ₘ T.map g))) :
    tensorComparisonSource F G S ≅ tensorComparisonTarget R T J S := by
  refine NatIso.ofComponents (fun L ↦ ?_) ?_
  · refine NatIso.ofComponents (fun M ↦ e L M) ?_
    intro M M' g
    change S.obj (F.obj L) ◁ S.map (G.map g) ≫ _ =
      _ ≫ S.map (J.map (R.obj L ◁ T.map g))
    have hn := he (𝟙 L) g
    simpa only [F.map_id, S.map_id, R.map_id, id_tensorHom] using hn
  · intro L L' f
    apply NatTrans.ext
    funext M
    change S.map (F.map f) ▷ S.obj (G.obj M) ≫ _ =
      _ ≫ S.map (J.map (R.map f ▷ T.obj M))
    have hn := he f (𝟙 M)
    simpa only [NatIso.ofComponents_hom_app, G.map_id, S.map_id, T.map_id,
      tensorHom_id] using hn

end TensorComparisonNaturality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section

section ActualTensorAssembly
variable {A₀ B₀ C₀ D₀ E₀ : Type*} [Category* A₀] [Category* B₀]
  [Category* C₀] [Category* D₀] [Category* E₀]

end ActualTensorAssembly

end

end GeneratorTensorProof

end AlgebraicGeometry.ProEtale.CondensedRing
