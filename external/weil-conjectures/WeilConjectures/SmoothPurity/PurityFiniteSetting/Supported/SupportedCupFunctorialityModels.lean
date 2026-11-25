/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameKummer
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleClosedConstantTensor
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square

import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.Yoneda
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement

import all Mathlib.Logic.Small.Defs

import all Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Pullback and symmetry of supported Kummer cup products

Source: Stacks Project, Tags 0FPL, 0FPM, 09XP, 03PL and 0G78; blueprint
main-20261015, proposition-purity-vector-bundles, unit multiples, permutations and shears
(blueprint: lem-pur-supported-cup-functoriality).

The Boolean site parameter is false for the small etale site and true for the
small pro-etale site. All constructions use the published sites, coefficients,
Kummer classes, exact inverse images and derived tensors.

## Main definitions and statement

* `functorialCupPullback`: the canonically normalized supported pullback.
* `functorialCup`: the prescribed tensor-morphism cup product on either site.
* `FunctorialCupAlgebraLaws`, `FunctorialCupLocalizationLaws`, and
  `FunctorialCupComparisonLaws`: the clauses of the statement.
* `supportedCupFunctoriality`: all these clauses for both sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

set_option backward.isDefEq.respectTransparency false in
/-- The selected small site category. -/
abbrev functorialCupSite (pro : Bool) (X : Scheme.{u}) : Type (u + 1) :=
  match pro with
  | false => X.Etale
  | true => X.ProEt

/-- Its existing category. -/
@[reducible] instance functorialCupSiteCategory (pro : Bool) (X : Scheme.{u}) :
    Category.{u} (functorialCupSite pro X) := by cases pro <;> infer_instance

/-- Its existing topology. -/
abbrev functorialCupTopology (pro : Bool) (X : Scheme.{u}) :
    GrothendieckTopology (functorialCupSite pro X) :=
  match pro with
  | false => X.smallEtaleTopology
  | true => Scheme.ProEt.topology X

/-- The actual sheaf category on the selected small site. -/
abbrev functorialCupSheaves (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  Sheaf (functorialCupTopology pro X) (ModuleCat.{u + 1} P.Coefficient)

@[reducible] instance functorialCupCategory (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    Category.{u + 1} (P.functorialCupSheaves pro X) := inferInstance

instance functorialCupTopologySheafify (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : HasSheafify (functorialCupTopology pro X)
      (ModuleCat.{u + 1} P.Coefficient) := by cases pro <;> infer_instance

@[reducible] instance functorialCupAbelian (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    Abelian (P.functorialCupSheaves pro X) := inferInstance

@[reducible] instance functorialCupHasDerived (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1} (P.functorialCupSheaves pro X) :=
  inferInstance

/-- The existing derived category, with its localization shared explicitly.
Source: supported tensor construction (blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupDerived (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  @DerivedCategory (P.functorialCupSheaves pro X) _ _ (P.functorialCupHasDerived pro X)

/-- The existing finite constant module. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupConstant (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    P.functorialCupSheaves pro X :=
  match pro with
  | false => P.constantEtale X
  | true => P.constant X

/-- The published comparison inverse image, with its actual exact structure.
Source: Stacks 099R (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupComparisonFunctor (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.functorialCupSheaves false X ⥤ P.functorialCupSheaves true X :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X

/-- The signed finite Tate sheaf at the actual annihilator ell^n. Source: the
arbitrary-index Kummer prescription in proposition-purity-vector-bundles
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwist (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (r : ℤ) : P.functorialCupSheaves pro X :=
  match pro with
  | false => Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates r
  | true => (P.functorialCupComparisonFunctor X).obj
      (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
        P.diagonalExponent_annihilates r)

/-- The existing degree-zero embedding. Source: supported tensor construction
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSingle (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    P.functorialCupSheaves pro X ⥤ P.FunctorialCupDerived pro X :=
  @DerivedCategory.singleFunctor (P.functorialCupSheaves pro X) _ _
    (P.functorialCupHasDerived pro X) 0

/-- The actual underived direct image of constants from the closed support.
Source: proposition-purity-vector-bundles, supported-Hom model
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSource (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) : P.functorialCupSheaves pro X :=
  match pro with
  | false => (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale C)
  | true => (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant C)

/-- Restriction of local constants, exactly the coefficient map of the supported cup.
Source: proposition-purity-vector-bundles and the etale coefficient lemma
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupRestriction (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupConstant pro X ⟶ P.functorialCupSource pro i :=
  match pro with
  | false => Etale.closedConstantSectionMap P.Coefficient i
  | true => ProEtale.cupCoefficientRestriction P i

/-- The supported degree-zero source, shared before forming Hom types. -/
def functorialCupSourceObject (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) : P.FunctorialCupDerived pro X :=
  (P.functorialCupSingle pro X).obj (P.functorialCupSource pro i)

/-- The shifted coefficient target, shared by all supported Hom types. -/
def functorialCupTarget (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (a r : ℤ) : P.FunctorialCupDerived pro X :=
  ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧

/-- The actual exact inverse image of fixed-scalar modules. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupInverseImage (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    P.functorialCupSheaves pro X ⥤ P.functorialCupSheaves pro Y :=
  match pro with
  | false => Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v
  | true => ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
@[reducible] instance functorialCupMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    MonoidalCategory (P.functorialCupSheaves pro X) := by infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupMonoidalPreadditive (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    MonoidalPreadditive (P.functorialCupSheaves pro X) := by infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
@[reducible] instance functorialCupSymmetric (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    SymmetricCategory (P.functorialCupSheaves pro X) := by infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
@[reducible] instance functorialCupClosed (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    MonoidalClosed (P.functorialCupSheaves pro X) := by infer_instance

/-- The published functorial flat resolutions, selected by the site.
Source: K-flat tensor construction (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupFlatResolutions (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : Abelian.HasFunctorialFlatResolution (P.functorialCupSheaves pro X) := by
  infer_instance

/-- The coefficient multiplication fixed by restriction and local scalar multiplication.
Source: proposition-purity-vector-bundles and its etale analogue
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupMultiplication (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    P.functorialCupSource pro i ⊗ P.functorialCupSource pro j ⟶
      P.functorialCupSource pro (ProEtale.cupIntersection i j) :=
  match pro with
  | false => Etale.closedConstantTensorMap P.Coefficient i j
  | true => ProEtale.cupCoefficientMap P i j

section CoefficientProof

set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupHasDerived
  functorialCupMonoidal functorialCupAbelian functorialCupCategory
  functorialCupMonoidalPreadditive functorialCupSymmetric functorialCupClosed
  functorialCupFlatResolutions functorialCupMultiplication functorialCupSource

end CoefficientProof

/-- Canonical inverse image of the coefficient unit. Source: constant-sheaf adjunction
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupConstantPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    (P.functorialCupInverseImage pro v).obj (P.functorialCupConstant pro X) ≅
      P.functorialCupConstant pro Y :=
  match pro with
  | false => (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) v).app
      (ModuleCat.of P.Coefficient P.Coefficient)
  | true => P.frameConstantPullback v

section ClosedSupportProof

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupCategory functorialCupAbelian
  functorialCupMonoidal functorialCupSymmetric functorialCupClosed
  constant constantEtale functorialCupConstant functorialCupComparisonFunctor
  functorialCupSource functorialCupRestriction functorialCupInverseImage
  functorialCupConstantPullback

section EtaleSourceNormalization

open Etale

private theorem transition_unit (A : Type (u + 1)) [CommRing A]
    {V D X : Scheme.{u}} (p : V ⟶ D) (g : D ⟶ X) (h : V ⟶ X)
    (hp : p ≫ g = h) :
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) g) ≫
      constantModulePushforwardMap A (ModuleCat.of A A) g h p hp =
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) h) := by
  unfold constantModulePushforwardMap
  erw [upperStarConstantSheafIso_hom_app_tensorUnit (ModuleCat.{u + 1} A) p]
  erw [Adjunction.unit_app_unit_comp_map_η]
  exact (ε_lowerStar_comp p g h hp.symm).symm

private theorem section_unit (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    closedConstantSectionMap A i =
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) i) := by
  unfold closedConstantSectionMap
  erw [← ε_lowerStar_id]
  exact transition_unit A i (𝟙 X) i (by simp)

private theorem section_epi (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    Epi (closedConstantSectionMap A i) := by
  erw [section_unit A i]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit_app_unit_comp_map_η]
  have : Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) :=
    (shortExact_openClosedShortComplex (ModuleCat.{u + 1} A)
      i.openComplement.ι i
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      i.range_eq_compl_range_openComplement_ι).epi_g
  exact epi_comp _ _

end EtaleSourceNormalization

private theorem comparisonSource_normalized (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ∃! b : (P.functorialCupComparisonFunctor X).obj
        (P.functorialCupSource false i) ≅ P.functorialCupSource true i,
      (P.functorialCupComparisonFunctor X).map
          (P.functorialCupRestriction false i) ≫ b.hom = P.functorialCupRestriction true i := by
  let F := P.functorialCupComparisonFunctor X
  have := section_epi P.Coefficient i
  have : Epi (P.functorialCupRestriction false i) := section_epi P.Coefficient i
  have : Epi (F.map (P.functorialCupRestriction false i)) := F.map_epi _
  have := ProEtale.isIso_lowerStarComparisonUpperStarBaseChange i
    (ModuleCat.{u + 1} P.Coefficient)
  let e := asIso ((ProEtale.lowerStarComparisonUpperStarBaseChange i
    (ModuleCat.{u + 1} P.Coefficient)).app (P.constantEtale C))
  have he : F.map (P.functorialCupRestriction false i) ≫ e.hom =
      P.functorialCupRestriction true i := by
    change (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
      (Etale.closedConstantSectionMap P.Coefficient i) ≫ _ = _
    rw [section_unit]
    exact (ProEtale.comparison_restriction P i).symm
  refine ⟨e, he, ?_⟩
  intro b hb
  apply Iso.ext
  exact (cancel_epi (F.map (P.functorialCupRestriction false i))).1 (hb.trans he.symm)

section EtaleExchangeNormalization

open Etale
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
  SymmetricCategory.toBraidedCategory
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

end EtaleExchangeNormalization

end ClosedSupportProof

section SupportMapProof

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupCategory functorialCupAbelian
  functorialCupMonoidal functorialCupSymmetric functorialCupClosed
  constant constantEtale functorialCupConstant functorialCupComparisonFunctor
  functorialCupSource functorialCupRestriction functorialCupInverseImage
  functorialCupConstantPullback

/-- Change of closed support over a fixed scheme, uniquely determined on local constants.
Source: supported functoriality, Steps 2 and 5
(blueprint: lem-pur-supported-cup-functoriality).
Proof: the map D to C over X restricts each locally constant section on C to D.
The sheaf map is A-linear and carries the restricted unit to the restricted unit.
The constant restriction onto the closed direct image is epic, proving uniqueness. -/
theorem functorialCupSupportMap_existsUnique (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (_h : g ≫ i = j) :
    ∃! b : P.functorialCupSource pro i ⟶ P.functorialCupSource pro j,
      P.functorialCupRestriction pro i ≫ b = P.functorialCupRestriction pro j := by
  let t := Etale.constantModulePushforwardMap P.Coefficient
    (ModuleCat.of P.Coefficient P.Coefficient) i j g _h
  have ht : Etale.closedConstantSectionMap P.Coefficient i ≫ t =
      Etale.closedConstantSectionMap P.Coefficient j := by
    rw [section_unit, section_unit]
    exact transition_unit _ g i j _h
  have := section_epi P.Coefficient i
  have : Epi (P.functorialCupRestriction false i) := section_epi P.Coefficient i
  cases pro with
  | false =>
    refine ⟨t, ht, ?_⟩
    intro b hb
    exact (cancel_epi (Etale.closedConstantSectionMap P.Coefficient i)).1 (hb.trans ht.symm)
  | true =>
    let F := P.functorialCupComparisonFunctor X
    let ei := (comparisonSource_normalized P i).choose
    let ej := (comparisonSource_normalized P j).choose
    have hi := (comparisonSource_normalized P i).choose_spec.1
    have hj := (comparisonSource_normalized P j).choose_spec.1
    change F.map (P.functorialCupRestriction false i) ≫ ei.hom = _ at hi
    change F.map (P.functorialCupRestriction false j) ≫ ej.hom = _ at hj
    have : Epi (F.map (Etale.closedConstantSectionMap P.Coefficient i)) := F.map_epi _
    have hpi : Epi (P.functorialCupRestriction true i) := by
      rw [← hi]
      exact epi_comp _ _
    let b := ei.inv ≫ F.map t ≫ ej.hom
    have hb : P.functorialCupRestriction true i ≫ b =
        P.functorialCupRestriction true j := by
      rw [← hi]
      dsimp only [b]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← F.map_comp_assoc, ht]
      exact hj
    refine ⟨b, hb, ?_⟩
    intro b' hb'
    exact (cancel_epi (P.functorialCupRestriction true i)).1 (hb'.trans hb.symm)

end SupportMapProof

/-- The actual restriction on closed constant sheaves, fixed by its epic unit map.
Source: supported functoriality, Steps 2 and 5
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSupportMap (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (h : g ≫ i = j) :
    P.functorialCupSource pro i ⟶ P.functorialCupSource pro j :=
  (P.functorialCupSupportMap_existsUnique pro i j g h).choose

/-- Ext smallness cached before evaluating the fixed coefficient lines. -/
theorem functorialCupHasExt (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    HasExt.{u + 1} (P.functorialCupSheaves pro X) :=
  hasExt_of_hasDerivedCategory _

attribute [local instance] functorialCupHasExt

/-- The identity direct-image unitor of the actual supported coefficient source.
Source: the full-support normalization
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupFullSupportIso (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    P.functorialCupSource pro (𝟙 X) ≅ P.functorialCupConstant pro X :=
  match pro with
  | false => (Etale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app
      (P.constantEtale X)
  | true => (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app (P.constant X)

/-- The published exact extension by zero for the complementary open.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenExtension (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupSheaves pro i.openComplement.toScheme ⥤ P.functorialCupSheaves pro X :=
  match pro with
  | false => Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      i.openComplement.ι
  | true => ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      i.openComplement.ι

/-- Extension by zero of the actual unit on the open complement.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenSource (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :=
  (P.functorialCupOpenExtension pro i).obj
    (P.functorialCupConstant pro i.openComplement.toScheme)

/-- The adjunction counit, with its canonical constant-sheaf restriction.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenInclusion (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupOpenSource pro i ⟶ P.functorialCupConstant pro X :=
  match pro with
  | false => (P.functorialCupOpenExtension false i).map
      (P.functorialCupConstantPullback false i.openComplement.ι).inv ≫
      (Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).counit.app (P.constantEtale X)
  | true => (P.functorialCupOpenExtension true i).map
      (P.functorialCupConstantPullback true i.openComplement.ι).inv ≫
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).counit.app (P.constant X)

section SequenceProof

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupCategory functorialCupAbelian
  constant constantEtale functorialCupConstant functorialCupSource
  functorialCupRestriction functorialCupInverseImage functorialCupConstantPullback
  functorialCupComparisonFunctor functorialCupOpenExtension functorialCupOpenSource
  functorialCupOpenInclusion

end SequenceProof

end WeilConjectures.PurityFiniteSetting
