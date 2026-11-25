/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.K.KInjectiveDerivedMapComputation
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import WeilConjectures.Algebra.Homology.SequenceProjection.SequencePushforwardLimitProjections
import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
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
import Mathlib.CategoryTheory.Adjunction.Basic
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
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic

/-! # Resolution-normalized sequence-site adjoints

Source: blueprint main-20261015, `sec-six-functors/sk-thm-sf-package/`
`fix-prop-coherence.proof.md`, coefficient-comparison sentence; Stacks 0940,
0941, 03D7, 06YY, 07A6 and 0D6E
(blueprint: lem-pur-sequence-adjoint-resolution-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u c v d z
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceRestriction coefficientSequenceEvaluation
  coefficientFiniteDerivedExtension scalarReductionExtension
  coefficientConstantTowerLimit coefficientSequenceLimit
  coefficientFiniteReductionModel purSequenceShiftIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Shift the actual simultaneous replacement, including the canonical termwise
restriction comparison. Source: Stacks 0941, 070H
(blueprint: lem-pur-sequence-adjoint-resolution-shifts). -/
def purSequenceShiftedReplacement
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ J)
    (r : ℤ) :
    ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj (N⟦r⟧) ⟶
      J⟦r⟧ :=
  (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
    N ≫ j⟦r⟧'

attribute [local irreducible] purSequenceShiftedReplacement

/-- The prescribed cochain shifts of both derived adjoints, with the same resolutions.
`CommShift` includes naturality and the zero/addition coherence equations. The
representative squares use the ordinary termwise shift, hence identity on the
reindexed scalar-tensor terms and differential multiplied by `r.negOnePow`.
Source: Stacks 06YY, 0941, 0D6E; cochain shifts in derived.tex
(blueprint: lem-pur-sequence-adjoint-resolution-shifts). -/
structure PurSequenceLeftShiftModels
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (D : PurSequenceDerivedAdjoints l E W S O) where
  left_shift : D.L.CommShift ℤ
  reduction_shift : S.reduction.CommShift ℤ
  finite_shift : ∀ n : ℕ, (coefficientFiniteDerivedExtension l E W n).CommShift ℤ
  left_comparison : ∀ (P : DerivedCategory (scalarReductionSource l E W)) (r : ℤ),
    (purSequenceShiftIso D.L left_shift r).hom.app P ≫ (D.left.hom.app P)⟦r⟧' =
      D.left.hom.app (P⟦r⟧) ≫ (purSequenceShiftIso S.reduction reduction_shift r).hom.app P
  left_resolution : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ),
    D.L.map ((DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
      (purSequenceShiftIso D.L left_shift r).hom.app (DerivedCategory.Q.obj Q) ≫
      (D.ε.app Q)⟦r⟧' =
    D.ε.app (Q⟦r⟧) ≫ DerivedCategory.Q.map
      (((O.pullback.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app Q) ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q)
  left_terms : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r i : ℤ),
    HEq ((((O.pullback.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app Q).f i)
      (𝟙 (O.pullback.obj (Q.X (i + r))))
  finite_resolution : ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (r : ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (hQr : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q⟦r⟧)),
    (coefficientFiniteDerivedExtension l E W n).map
        ((DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
      (purSequenceShiftIso (coefficientFiniteDerivedExtension l E W n)
        (finite_shift n) r).hom.app (DerivedCategory.Q.obj Q) ≫
      (coefficientFiniteReductionModel l E W Q hQ n).hom⟦r⟧' =
    (coefficientFiniteReductionModel l E W (Q⟦r⟧) hQr n).hom ≫
      DerivedCategory.Q.map
        ((((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
          Q) ≫ (DerivedCategory.Q.commShiftIso r).hom.app
            (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
  finite_evaluation : ∀ (n : ℕ) (P : DerivedCategory (scalarReductionSource l E W)) (r : ℤ),
    (S.reductionEvaluation n).hom.app (P⟦r⟧) ≫
      (purSequenceShiftIso (coefficientFiniteDerivedExtension l E W n)
        (finite_shift n) r).hom.app P =
    (coefficientSequenceDerivedEvaluation l E W n).map
      ((purSequenceShiftIso S.reduction reduction_shift r).hom.app P) ≫
      ((coefficientSequenceDerivedEvaluation l E W n).commShiftIso r).hom.app
        (S.reduction.obj P) ≫ ((S.reductionEvaluation n).hom.app P)⟦r⟧'

/-- The right comparison square for the actual shifted simultaneous replacement.
This names the same equation separately to keep repeated structure type checking small.
Source: Stacks 0941 and 0D6E
(blueprint: lem-pur-sequence-adjoint-resolution-shifts). -/
def purSequenceRightResolutionCompatibility
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (D : PurSequenceDerivedAdjoints l E W S O)
    (limit_shift : (coefficientSequenceLimit l E W).CommShift ℤ) : Prop :=
  ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ J)
    [J.IsKInjective] [QuasiIso j] (r : ℤ)
    [QuasiIso (purSequenceShiftedReplacement l E W N J j r)],
    (coefficientSequenceLimit l E W).map
        ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      (purSequenceShiftIso (coefficientSequenceLimit l E W) limit_shift r).hom.app
        (DerivedCategory.Q.obj N) ≫ (D.model N J j).hom⟦r⟧' =
    (@D.model (N⟦r⟧) (J⟦r⟧) (purSequenceShiftedReplacement l E W N J j r)
      ((CochainComplex.isKInjective_shift_iff J r).mpr inferInstance) inferInstance).hom ≫
      DerivedCategory.Q.map
        ((((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
          |>.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app J) ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
          |>.mapHomologicalComplex (.up ℤ)).obj J)

/-- The degree component of the limit of the actual shifted replacement.
Source: Stacks 0941 and the cochain shift convention
(blueprint: lem-pur-sequence-adjoint-resolution-shifts). -/
def purSequenceShiftedDegreeCompatibility : Prop :=
  ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ J)
    (r i : ℤ),
    HEq ((((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
      |>.mapHomologicalComplex (.up ℤ)).map
        (purSequenceShiftedReplacement l E W N J j r)).f i)
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W).map
        (j.f (i + r)))

/-- The total-limit shifts on every supplied simultaneous replacement.
Source: Stacks 0941 and 0D6E
(blueprint: lem-pur-sequence-adjoint-resolution-shifts). -/
structure PurSequenceRightShiftModels
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (D : PurSequenceDerivedAdjoints l E W S O) where
  right_shift : D.R.CommShift ℤ
  limit_shift : (coefficientSequenceLimit l E W).CommShift ℤ
  right_comparison : ∀ (N : coefficientSequenceDerived l E W) (r : ℤ),
    (purSequenceShiftIso D.R right_shift r).hom.app N ≫ (D.right.hom.app N)⟦r⟧' =
      D.right.hom.app (N⟦r⟧) ≫
        (purSequenceShiftIso (coefficientSequenceLimit l E W) limit_shift r).hom.app N
  shifted_quasiIso : ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj N ⟶ J)
    [QuasiIso j] (r : ℤ), QuasiIso (purSequenceShiftedReplacement l E W N J j r)
  right_resolution : purSequenceRightResolutionCompatibility l E W S O D limit_shift
  shifted_degree : purSequenceShiftedDegreeCompatibility l E W

/-- The prescribed shifts with their actual adjunction compatibility.
Source: Stacks 06YY, 0941 and 0D6E
(blueprint: lem-pur-sequence-adjoint-resolution-shifts). -/
structure PurSequenceAdjointShifts
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (D : PurSequenceDerivedAdjoints l E W S O) where
  left : PurSequenceLeftShiftModels l E W S O D
  right : PurSequenceRightShiftModels l E W S O D
  adjoint_unit : ∀ r : ℤ,
    purSequenceUnitShiftCompatibility D.adjunction left.left_shift right.right_shift r
  adjoint_counit : ∀ r : ℤ,
    purSequenceCounitShiftCompatibility D.adjunction left.left_shift right.right_shift r

/-- Resolution-normalized identification of the sequence-site derived adjoints.
Source: blueprint main-20261015, `fix-prop-coherence.proof.md`, coefficient-comparison
sentence; Stacks 0940, 0941, 03D7, 06YS, 06YY, 07A6 and 0D6E
(blueprint: lem-pur-sequence-adjoint-resolution-shifts).

Proof, following the node:
1. The constant-tower functor preserves finite limits and is left adjoint to limit,
so gives the geometric projection g (def-coef-ringed-sequence-site). The actual
quotient maps cA to B define a ring change a with identity geometric inverse image.
Restriction a_* is exact on underlying abelian sheaves. Their composite is p.
2. The ordinary module adjunction (lem-weil-pbc-ringed-topoi-module-adjunction)
sends h to the family x tensor b mapped to b times pi_n(h(x)); its inverse sends
x to the compatible family f_n(x tensor 1). These formulas are mutually inverse
and natural and fix the ordinary unit and counit.
3. Resolve P by one flat-term K-flat Q (lem-pc-kflat-resolution). The universal
left-derived comparison (lem-weil-pbc-ringed-topoi-derived-pullback) computes
Lp^* by the strict quotient system on Q. The supplied calculus uses this same
model, including the maps of resolutions and quotient transitions; the finite
comparisons are those of lem-pur-derived-change-of-rings.
4. Q[r] remains K-flat: the tensor shift multiplies its (p,q) summand by
(-1)^(r*p), intertwining the tensor differentials. Its terms remain flat and the
resolution remains a quasi-isomorphism. Ordinary scalar extension commutes with
cochain shift by the identity on reindexed terms, with differential (-1)^r d.
5. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition to a and g,
and lem-weil-pbc-ringed-strict-tower-homotopy-limit to g. Exact U localizes
termwise (situation-conventions). For K-injective I
and a K-injective replacement j:UI to J, the comparison is represented by lim j,
which is a quasi-isomorphism. Resolutions exist by
prop-pur-kinjective-resolutions-exist; U need not preserve K-injectives.
6. For any N and any supplied replacement UN to J, first resolve N to I.
The bijection of lem-weil-pbc-kinjective-hom-derived gives a unique homotopy
class b:UI to J whose composite with Ui is the given replacement. Two-out-of-three
makes b a quasi-isomorphism. The preceding normalization computes the comparison
on this particular J. Independence and naturality on all derived morphisms follow
from lem-sf-kinjective-derived-map-computation and its comparison cocycle equations.
7. Use lem-coef-sequence-projection-derived-adjunction and the fraction normalization
of lem-sfb-resolving-derived-adjunction-normalization. A map p^*Q to I transposes
to Q to lim UI and then lim j. The canonical projection/counit formulas of
lem-coef-sequence-pushforward-limit-projections are exactly the supplied calculus
adjunction. Thus the whole Hom bijections agree, so their units and counits agree
as system maps, without using faithfulness of derived level evaluation.
8. By lem-weil-pbc-kinjective-shift, I[r] and J[r] are K-injective. Apply step 5
to exactly j[r]; its degree-i limit map is lim j^(i+r). The ordinary limit shift
is identity on reindexed terms, with differential (-1)^r d. For arbitrary N,
use the same shifted replacement and comparison class b[r]; uniqueness and step 6
give the square on every derived input and morphism.
9. For r+s use Q[r+s], I[r+s] and j[r+s]. The sign identity
(-1)^r * (-1)^s = (-1)^(r+s) gives addition coherence, while zero and inverse
shifts give their identity equations. This covers negative shifts, zero complexes,
and the empty scheme, without normalizedness, completeness, or exact products. -/
theorem purSequenceAdjointResolutionShifts
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S) :
    ∃ A : PurSequenceResolutionData l E W S,
      Nonempty (PurSequenceAdjointShifts l E W S A.ordinary A.derived) := by
  sorry

end WeilConjectures
