/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence

/-!
# Realization of integral pullback comparisons

Source: Stacks Project, Tags 099N(2),(5), 0D6D, 06YY and 0941; blueprint
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
final common-stage transport paragraph
(blueprint: lem-trf-integral-pullback-comparison-realization).

The sequence site retains the whole quotient diagram. Its pullback is the left
adjoint of the actual sectionwise direct image. Scalar change is the universal
derived change of rings for the actual map of quotient coefficient sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Apply reduction to the defining pullback realization, then the actual
whole-system action counit. By integralComparisonReductionCounit_formula this
is derived coefficient change of the K-injective-normalized epsilon.
Source: Stacks 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonPullbackCounit {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (SZ : CoefficientDerivedSystemCalculus l E Z)
    (ρ : IntegralComparisonRoosModel l E Z)
    (M : IntegralComparisonPullbackModel l E f SY ρ) :
    integralDerivedPullback l E f ⋙ SZ.reduction ⟶
      SY.reduction ⋙ integralComparisonDerivedSequencePullback l E f :=
  Functor.whiskerRight M.realization.hom SZ.reduction ≫
    Functor.whiskerLeft (SY.reduction ⋙ integralComparisonDerivedSequencePullback l E f)
      SZ.adjunction.counit

/-- The scalar analogue of the entire-system counit construction.
Source: Stacks 06YY, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarCounit (Y : Scheme.{t})
    (SE : CoefficientDerivedSystemCalculus l E Y)
    (SL : CoefficientDerivedSystemCalculus l L Y)
    (ρ : IntegralComparisonRoosModel l L Y)
    (M : IntegralComparisonScalarModel l E L ι Y SE ρ) :
    integralScalarExtensionOfUniverses l E L ι Y ⋙ SL.reduction ⟶
      SE.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι Y :=
  Functor.whiskerRight M.realization.hom SL.reduction ≫
    Functor.whiskerLeft (SE.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι Y)
      SL.adjunction.counit

/-- Coherent realization interfaces at one coefficient field. Each constituent
has the actual representative normalization; effectivity is asserted only on
the intrinsic constructible-complete domain with ell invertible.
Source: Stacks 099N(5), 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonCoefficientData where
  /-- The published normalized reduction calculus on each small pro-etale site. -/
  system : ∀ X : Scheme.{u}, CoefficientDerivedSystemCalculus l E X
  /-- Total limit is identified with the specified Roos construction. -/
  roos : ∀ X : Scheme.{u}, IntegralComparisonRoosModel l E X
  /-- The pullback realization, tested on every simultaneous K-flat presentation. -/
  pullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    IntegralComparisonPullbackModel l E f (system Y) (roos X)
  /-- The counit-built diagram map is invertible on every allowed input. -/
  effective : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    IsIso ((integralComparisonPullbackCounit l E f (system Y) (system X)
      (roos X) (pullback f)).app K.obj)
  /-- Derived completeness makes the normalized reconstruction unit invertible. -/
  complete : ∀ (X : Scheme.{u}) (K : sfIntegralConstructibleCategory l E X),
    IsIso (((system X).adjunction.unit).app K.obj)

/-- The scalar realization, with its entire-system counit invertible on the
intrinsic constructible domain. Source: Stacks 06YY, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonScalarData
    (DE : IntegralComparisonCoefficientData l E) (DL : IntegralComparisonCoefficientData l L) where
  /-- The cochain-normalized scalar realization on every scheme. -/
  model : ∀ X : Scheme.{u},
    IntegralComparisonScalarModel l E L ι X (DE.system X) (DL.roos X)
  /-- The specified scalar counit is an isomorphism, without a Tor-amplitude bound. -/
  effective : ∀ (X : Scheme.{u}) (K : sfIntegralConstructibleCategory l E X),
    IsIso ((integralComparisonScalarCounit l E L ι X (DE.system X) (DL.system X)
      (DL.roos X) (model X)).app K.obj)

/-- One simultaneously normalized system for all finite coefficient extensions.
Small coefficient models and their embeddings express subextensions of any fixed
algebraic closure without identifying its universe with the site universe.
Source: blueprint final common-stage transport paragraph; Stacks 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonSystem (l : ℕ) [Fact l.Prime] where
  /-- All one-field realization data, with the same functors as the dependencies. -/
  coefficient : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], IntegralComparisonCoefficientData l E
  /-- All finite scalar inclusions at once, including identity and composite inclusions. -/
  scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    IntegralComparisonScalarData l E L ι (coefficient E) (coefficient L)

variable (D : IntegralComparisonSystem.{u} l)

/-- Eta is realization of h-star applied to the whole-system counit for k.
Source: Stacks 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonEta {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralDerivedPullback l E h).obj ((integralDerivedPullback l E k).obj K.obj) ≅
      (coefficientSequenceLimit l E Z).obj
        ((integralComparisonDerivedSequencePullback l E h).obj
          ((integralComparisonDerivedSequencePullback l E k).obj
            (((D.coefficient E).system V).reduction.obj K.obj))) :=
  letI := (D.coefficient E).effective k K
  ((D.coefficient E).pullback h).realization.app
      ((integralDerivedPullback l E k).obj K.obj) ≪≫
    (coefficientSequenceLimit l E Z).mapIso
      ((integralComparisonDerivedSequencePullback l E h).mapIso
        (asIso ((integralComparisonPullbackCounit l E k
          ((D.coefficient E).system V) ((D.coefficient E).system W)
          ((D.coefficient E).roos W) ((D.coefficient E).pullback k)).app K.obj)))

/-- Lambda is realization of scalar change of the whole-system pullback counit.
Source: Stacks 06YY, 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonLambda {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    (integralScalarExtension l E L ι X).obj ((integralDerivedPullback l E f).obj K.obj) ≅
      (coefficientSequenceLimit l L X).obj
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj
          ((integralComparisonDerivedSequencePullback l E f).obj
            (((D.coefficient E).system Y).reduction.obj K.obj))) :=
  letI := (D.coefficient E).effective f K
  ((D.scalar E L ι).model X).realization.app
      ((integralDerivedPullback l E f).obj K.obj) ≪≫
    (coefficientSequenceLimit l L X).mapIso
      ((integralComparisonDerivedSequenceScalar l E L ι X).mapIso
        (asIso ((integralComparisonPullbackCounit l E f
          ((D.coefficient E).system Y) ((D.coefficient E).system X)
          ((D.coefficient E).roos X) ((D.coefficient E).pullback f)).app K.obj)))

/-- Mu is pullback of the whole-system scalar counit, followed by the inverse
of the generator-normalized scalar/pullback associator on entire diagrams.
Source: Stacks 06YY, 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonMu {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    (integralDerivedPullback l L f).obj ((integralScalarExtension l E L ι Y).obj K.obj) ≅
      (coefficientSequenceLimit l L X).obj
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj
          ((integralComparisonDerivedSequencePullback l E f).obj
            (((D.coefficient E).system Y).reduction.obj K.obj))) :=
  letI := (D.scalar E L ι).effective Y K
  ((D.coefficient L).pullback f).realization.app
      ((integralScalarExtension l E L ι Y).obj K.obj) ≪≫
    (coefficientSequenceLimit l L X).mapIso
      ((integralComparisonDerivedSequencePullback l L f).mapIso
        (asIso ((integralComparisonScalarCounit l E L ι Y
          ((D.coefficient E).system Y) ((D.coefficient L).system Y)
          ((D.coefficient L).roos Y) ((D.scalar E L ι).model Y)).app K.obj))) ≪≫
    (coefficientSequenceLimit l L X).mapIso
      ((integralComparisonSystemScalarPullback l E L ι f).app
        (((D.coefficient E).system Y).reduction.obj K.obj)).symm

/-- The specified integral compositor is Rlim of the finite compositor, followed
by eta inverse. Source: Stacks 0D6D, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonComposition {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralDerivedPullback l E (h ≫ k)).obj K.obj ≅
      (integralDerivedPullback l E h).obj ((integralDerivedPullback l E k).obj K.obj) :=
  ((D.coefficient E).pullback (h ≫ k)).realization.app K.obj ≪≫
    (coefficientSequenceLimit l E Z).mapIso
      ((integralComparisonSystemComposition l E h k).app
        (((D.coefficient E).system V).reduction.obj K.obj)) ≪≫
    (integralComparisonEta l E D h k K).symm

/-- The specified scalar comparison is lambda followed by mu inverse.
Source: Stacks 06YY, 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalar {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :=
  integralComparisonLambda l E L ι D f K ≪≫ (integralComparisonMu l E L ι D f K).symm

/-- The actual scalar extension on the intrinsic full categories. The auxiliary
prime-to-characteristic parameter of the existing interface is discharged by
p=ell+1; this supplies no assumption on schemes or reductions.
Source: blueprint integral scalar extension, order 1460
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonConstructibleScalar (X : Scheme.{u}) :=
  sfConstructibleIntegralScalarExtension (l + 1) l
    (Nat.ne_of_lt (Nat.lt_succ_self l)) E L ι X

/-- The identity pullback is the identity finite diagram followed by the
inverse derived-completeness unit. Source: Stacks 099N, 0D6D
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonUnit (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X) :
    (integralDerivedPullback l E (𝟙 X)).obj K.obj ≅ K.obj :=
  letI := (D.coefficient E).complete X K
  ((D.coefficient E).pullback (𝟙 X)).realization.app K.obj ≪≫
    (coefficientSequenceLimit l E X).mapIso
      ((integralComparisonSystemUnit l E X).app
        (((D.coefficient E).system X).reduction.obj K.obj)) ≪≫
    (asIso (((D.coefficient E).system X).adjunction.unit.app K.obj)).symm

/-- Identity scalar extension under ordinary multiplication and the specified
completion map chi. Source: blueprint scalar-extension unit; Stacks 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarUnit (X : Scheme.{u})
    (K : sfIntegralConstructibleCategory l E X) :
    (integralScalarExtension l E E (AlgHom.id ℚ_[l] E) X).obj K.obj ≅ K.obj :=
  (scalarCompletionIso l E E (AlgHom.id ℚ_[l] E) X K.obj K.property.1).symm ≪≫
    (integralOrdinaryDerivedScalarUnit l E X).app K.obj

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

/-- The integral scalar associator is precisely the ordinary derived tensor
associator conjugated by the specified completion maps chi.
Source: blueprint common-stage transport; Stacks 06YY, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarAssociator (X : Scheme.{u})
    (K : sfIntegralConstructibleCategory l E X) :
    (integralScalarExtension l L M j X).obj
        ((integralScalarExtension l E L ι X).obj K.obj) ≅
      (integralScalarExtension l E M (j.comp ι) X).obj K.obj :=
  (scalarCompletionIso l L M j X _
      (((integralComparisonConstructibleScalar l E L ι X).obj K).property.1)).symm ≪≫
    (integralOrdinaryDerivedScalar l L M j X).mapIso
      (scalarCompletionIso l E L ι X K.obj K.property.1).symm ≪≫
    (integralOrdinaryDerivedScalarComp l E L ι X M j).app K.obj ≪≫
    scalarCompletionIso l E M (j.comp ι) X K.obj K.property.1

end WeilConjectures

namespace WeilConjectures

/-- Composition laws for the specified families, on strict systems and their realization.
Source: Stacks 0D6D, 0941; blueprint common-stage transport
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonCompositionLaws
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : IntegralComparisonSystem.{u} l) : Prop where
  /-- The finite composition equation is an equation of entire quotient systems. -/
  systemAssociative : ∀ {V W Z Y : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) (N : coefficientSequenceModules l E V),
    (integralComparisonSequenceComposition.{u, u} l E (j ≫ h) k).hom.app N ≫
        (integralComparisonSequenceComposition.{u, u} l E j h).hom.app
          ((integralComparisonSequencePullback.{u, u} l E k).obj N) =
      eqToHom (congrArg (fun f : Y ⟶ V ↦
        (integralComparisonSequencePullback.{u, u} l E f).obj N) (Category.assoc j h k).symm) ≫
        (integralComparisonSequenceComposition.{u, u} l E j (h ≫ k)).hom.app N ≫
        (integralComparisonSequencePullback.{u, u} l E j).map
          ((integralComparisonSequenceComposition.{u, u} l E h k).hom.app N)
  /-- The source identity is the specified inverse-image unit, before realization. -/
  systemUnitSource : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y),
    (integralComparisonSequenceComposition.{u, u} l E (𝟙 X) f).hom.app N ≫
        (integralComparisonSequenceUnit.{u, u} l E X).hom.app
          ((integralComparisonSequencePullback.{u, u} l E f).obj N) =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralComparisonSequencePullback.{u, u} l E g).obj N) (Category.id_comp f))
  /-- The target identity is the same unit, before realization. -/
  systemUnitTarget : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y),
    (integralComparisonSequenceComposition.{u, u} l E f (𝟙 Y)).hom.app N ≫
        (integralComparisonSequencePullback.{u, u} l E f).map
          ((integralComparisonSequenceUnit.{u, u} l E Y).hom.app N) =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralComparisonSequencePullback.{u, u} l E g).obj N) (Category.comp_id f))
  /-- Naturality of the realized composition comparisons. -/
  naturality : ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K J : sfIntegralConstructibleCategory l E V) (r : K ⟶ J),
    (integralDerivedPullback l E (h ≫ k)).map r.hom ≫
        (integralComparisonComposition l E D h k J).hom =
      (integralComparisonComposition l E D h k K).hom ≫
        (integralDerivedPullback l E h).map ((integralDerivedPullback l E k).map r.hom)
  /-- Associativity after transport by eta, with the actual scheme equality. -/
  associative : ∀ {V W Z Y : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
    (integralComparisonComposition l E D (j ≫ h) k K).hom ≫
        (integralComparisonComposition l E D j h
          ((constructibleIntegralPullback l E k).obj K)).hom =
      eqToHom (congrArg (fun f : Y ⟶ V ↦
        (integralDerivedPullback l E f).obj K.obj) (Category.assoc j h k).symm) ≫
        (integralComparisonComposition l E D j (h ≫ k) K).hom ≫
        (integralDerivedPullback l E j).map
          ((integralComparisonComposition l E D h k K).hom)
  /-- Realized source unit, with the completeness normalization. -/
  unitSource : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralComparisonComposition l E D (𝟙 X) f K).hom ≫
        (integralComparisonUnit l E D X ((constructibleIntegralPullback l E f).obj K)).hom =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralDerivedPullback l E g).obj K.obj) (Category.id_comp f))
  /-- Realized target unit. -/
  unitTarget : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralComparisonComposition l E D f (𝟙 Y) K).hom ≫
        (integralDerivedPullback l E f).map ((integralComparisonUnit l E D Y K).hom) =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralDerivedPullback l E g).obj K.obj) (Category.comp_id f))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l)

/-- The left side of the scalar/composition equation, in the full constructible category.
Source: blueprint common-stage transport; Stacks 06YY, 0D6D
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarSquareLeft {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonConstructibleScalar l E L ι Z).obj
        ((constructibleIntegralPullback l E (h ≫ k)).obj K) ⟶
      (constructibleIntegralPullback l L h).obj ((constructibleIntegralPullback l L k).obj
        ((integralComparisonConstructibleScalar l E L ι V).obj K)) :=
  ObjectProperty.homMk
    ((integralScalarExtension l E L ι Z).map
        (integralComparisonComposition l E D h k K).hom ≫
      (integralComparisonScalar l E L ι D h
        ((constructibleIntegralPullback l E k).obj K)).hom ≫
      (integralDerivedPullback l L h).map (integralComparisonScalar l E L ι D k K).hom)

/-- The right side, with the very same source and target integral objects.
Source: blueprint common-stage transport; Stacks 06YY, 0D6D
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarSquareRight {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonConstructibleScalar l E L ι Z).obj
        ((constructibleIntegralPullback l E (h ≫ k)).obj K) ⟶
      (constructibleIntegralPullback l L h).obj ((constructibleIntegralPullback l L k).obj
        ((integralComparisonConstructibleScalar l E L ι V).obj K)) :=
  ObjectProperty.homMk
    ((integralComparisonScalar l E L ι D (h ≫ k) K).hom ≫
      (integralComparisonComposition l L D h k
        ((integralComparisonConstructibleScalar l E L ι V).obj K)).hom)

/-- All coherence equations for the normalized construction. Equations on systems precede
realization; the integral equations refer to the displayed counit-built eta, lambda and mu.
Source: Stacks 099N, 0D6D, 06YY, 0941; blueprint common-stage transport
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonRealizationCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l) : Prop where
  /-- Associativity and units for every coefficient field, including E and L. -/
  composition : ∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F],
    IntegralComparisonCompositionLaws l F D
  /-- The scalar/composition equation already holds on entire quotient diagrams. -/
  systemScalarComposition : ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (N : coefficientSequenceModules l E V),
    (integralComparisonSequenceScalarModel.{u, u} l E L ι Z).E.map
        ((integralComparisonSequenceComposition.{u, u} l E h k).hom.app N) ≫
        (integralComparisonSequenceScalarPullback.{u, u} l E L ι h).hom.app
          ((integralComparisonSequencePullback.{u, u} l E k).obj N) ≫
        (integralComparisonSequencePullback.{u, u} l L h).map
          ((integralComparisonSequenceScalarPullback.{u, u} l E L ι k).hom.app N) =
      (integralComparisonSequenceScalarPullback.{u, u} l E L ι (h ≫ k)).hom.app N ≫
        (integralComparisonSequenceComposition.{u, u} l L h k).hom.app
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι V).E.obj N)
  /-- Scalar comparison is natural for all derived constructible morphisms. -/
  naturality : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K J : sfIntegralConstructibleCategory l E Y) (r : K ⟶ J),
    (integralScalarExtension l E L ι X).map ((integralDerivedPullback l E f).map r.hom) ≫
        (integralComparisonScalar l E L ι D f J).hom =
      (integralComparisonScalar l E L ι D f K).hom ≫
        (integralDerivedPullback l L f).map ((integralScalarExtension l E L ι Y).map r.hom)
  /-- The node's displayed equation, with its specified integral families. -/
  scalarComposition : ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
    integralComparisonScalarSquareLeft l E L ι D h k K =
      integralComparisonScalarSquareRight l E L ι D h k K
  /-- The same equation in raw rationalization, without a perfectness restriction. -/
  rationalScalarComposition : ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
    (sfRationalConstructibleLocalization l L Z).map
        (integralComparisonScalarSquareLeft l E L ι D h k K) =
      (sfRationalConstructibleLocalization l L Z).map
        (integralComparisonScalarSquareRight l E L ι D h k K)
  /-- The scalar comparison respects identity scheme maps before realization. -/
  systemScalarSchemeUnit : ∀ (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (N : coefficientSequenceModules l E X),
    (integralComparisonSequenceScalarPullback.{u, u} l E L ι (𝟙 X)).hom.app N ≫
        (integralComparisonSequenceUnit.{u, u} l L X).hom.app
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι X).E.obj N) =
      (integralComparisonSequenceScalarModel.{u, u} l E L ι X).E.map
        ((integralComparisonSequenceUnit.{u, u} l E X).hom.app N)
  /-- Realized scalar comparison respects the specified completed pullback unit. -/
  scalarSchemeUnit : ∀ (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X),
    (integralComparisonScalar l E L ι D (𝟙 X) K).hom ≫
        (integralComparisonUnit l L D X
          ((integralComparisonConstructibleScalar l E L ι X).obj K)).hom =
      (integralScalarExtension l E L ι X).map (integralComparisonUnit l E D X K).hom
  /-- Identity coefficients give multiplication on systems. -/
  systemScalarIdentity : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y),
    (integralComparisonSequenceScalarPullback.{u, u} l E E (AlgHom.id ℚ_[l] E) f).hom.app N ≫
        (integralComparisonSequencePullback.{u, u} l E f).map
          ((integralComparisonSequenceScalarUnit.{u, u} l E Y).hom.app N) =
      (integralComparisonSequenceScalarUnit.{u, u} l E X).hom.app
        ((integralComparisonSequencePullback.{u, u} l E f).obj N)
  /-- Identity coefficients give the identity under multiplication and completeness. -/
  scalarIdentity : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralComparisonScalar l E E (AlgHom.id ℚ_[l] E) D f K).hom ≫
        (integralDerivedPullback l E f).map (integralComparisonScalarUnit l E Y K).hom =
      (integralComparisonScalarUnit l E X ((constructibleIntegralPullback l E f).obj K)).hom
  /-- Scalar associativity is an equation on systems with the actual tensor associator. -/
  systemScalarTower : ∀ (M : Type u) [Field M] [Algebra ℚ_[l] M]
    [FiniteDimensional ℚ_[l] M] (j : L →ₐ[ℚ_[l]] M)
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (N : coefficientSequenceModules l E Y),
    (integralComparisonSequenceScalarModel.{u, u} l L M j X).E.map
        ((integralComparisonSequenceScalarPullback.{u, u} l E L ι f).hom.app N) ≫
        (integralComparisonSequenceScalarPullback.{u, u} l L M j f).hom.app
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj N) ≫
        (integralComparisonSequencePullback.{u, u} l M f).map
          ((integralComparisonSequenceScalarComposition.{u, u} l E L ι M j Y).hom.app N) =
      (integralComparisonSequenceScalarComposition.{u, u} l E L ι M j X).hom.app
          ((integralComparisonSequencePullback.{u, u} l E f).obj N) ≫
        (integralComparisonSequenceScalarPullback.{u, u} l E M (j.comp ι) f).hom.app N
  /-- Its realization uses the ordinary derived associator conjugated by chi. -/
  scalarTower : ∀ (M : Type u) [Field M] [Algebra ℚ_[l] M]
    [FiniteDimensional ℚ_[l] M] (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralScalarExtension l L M j X).map (integralComparisonScalar l E L ι D f K).hom ≫
        (integralComparisonScalar l L M j D f
          ((integralComparisonConstructibleScalar l E L ι Y).obj K)).hom ≫
        (integralDerivedPullback l M f).map
          (integralComparisonScalarAssociator l E L ι M j Y K).hom =
      (integralComparisonScalarAssociator l E L ι M j X
        ((constructibleIntegralPullback l E f).obj K)).hom ≫
        (integralComparisonScalar l E M (j.comp ι) D f K).hom

end WeilConjectures
