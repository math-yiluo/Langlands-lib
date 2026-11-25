/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
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
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedSupport
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.SmoothPurity.Compact.CompactSupportRepresentativeIndependence
public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
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
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportRoosCofinality

import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import all WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction

/-! # Integral compact-support coefficient data

The definitions that other statements use
(moved out of `IntegralCompactSupportCoefficientComparison`,
blueprint: def-pur-integral-compact-support-coefficient-data); the lemma's theorems stay there.

Source: Weil blueprint, theorem-smooth-purity-all-admissible-coefficients, Step 3; Bhatt--Scholze,
Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data).

## Main statements

* `recordedComparisonIso`: the canonical comparison on the recorded support functors.
* `comparisonIso`: its ambient proper/open presentation on the finite-Tor domain.
* `integralCoefficientComparison`: invertibility and constructible completeness.
* `comparison_reduction`, `comparison_quotients`, `comparison_strict_towers`:
  the actual finite maps and strict Roos presentations.
* `comparison_projection`, `comparison_commShift`, `comparison_refinement`:
  projection, shift and normalized compactification compatibility.
* `comparison_identity`, `comparison_composition`: the scalar unit and associativity laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures.PurCompactSupport

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  proEtaleRingRestrictionPullbackInv proEtaleCanonicalTensorComparison

/-- Ring sheaves and their inverse-image identifications, used only to organize the
specified completed and finite coefficient constructions below.
Source: Bhatt--Scholze, Sections 6.7--6.8
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
structure Coefficients where
  ring : ∀ W : Scheme.{u}, Sheaf (ProEt.topology W) CommRingCat.{u + 1}
  pull : ∀ {U V : Scheme.{u}} (g : U ⟶ V),
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (ring V) ≅ ring U

/-- A compatible map of these coefficient sheaves. The instances below use the actual
completed inclusions and quotient maps, rather than supplying an arbitrary map.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
structure Change (R S : Coefficients.{u}) where
  map : ∀ W : Scheme.{u}, R.ring W ⟶ S.ring W
  square : ∀ {U V : Scheme.{u}} (g : U ⟶ V),
    (R.pull g).hom ≫ map U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (map V) ≫ (S.pull g).hom

/-- Exact open extension for the specified coefficient identification.
Source: Stacks Tags 03DI, 03DJ
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
abbrev openExtension (R : Coefficients.{u}) {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] :=
  proEtaleRingOpenExtension j (R.ring V) (R.ring U) (R.pull j)

/-- Its specified adjunction to restriction.
Source: Stacks Tag 03DI
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openAdjunction (R : Coefficients.{u}) {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] :
    openExtension R j ⊣ proEtaleRingModulePullback j (R.ring V) (R.ring U) (R.pull j) :=
  Adjunction.ofIsRightAdjoint _

/-- The open scalar-restriction mate, determined by the open adjunction units.
Source: Stacks Tags 03DI, 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openRestrictionMap {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    proEtaleRingRestrictScalars (a.map U) ⋙ openExtension R j ⟶
      openExtension S j ⋙ proEtaleRingRestrictScalars (a.map V) :=
  letI := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  ((mateEquiv (openAdjunction S j) (openAdjunction R j)).symm
    (TwoSquare.mk _ _ _ _ (inv (proEtaleRingRestrictionPullbackInv
      j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)))))

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  SheafOfModules.localizedSystemExtensionAdditive SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
/-- The open mate is invertible. On extension-by-zero summands both it and its inverse
are identity on the underlying section; scalar actions agree by the coefficient square.
Source: Stacks Tag 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: identify open extension with an equivalence followed by slice extension. The
slice extension has invertible unit because the open object is subterminal, so both
open extensions are fully faithful. The sectionwise scalar/slice-extension isomorphism
shows that scalar restriction of an extended object is still extended. The counit on
this object is therefore invertible. The mate formula expresses the specified map as
extension of the scalar-restricted unit and the inverse restriction square, followed by
that counit. All three factors are invertible. -/
theorem openRestrictionMap_isIso {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    IsIso (openRestrictionMap a j) := by
  obtain ⟨eR, ⟨hR⟩⟩ := proEtaleOpen_slicePresentation j (R.ring V) (R.ring U) (R.pull j)
  obtain ⟨eS, ⟨hS⟩⟩ := proEtaleOpen_slicePresentation j (S.ring V) (S.ring U) (S.pull j)
  let LR := SheafOfModules.localizedModuleExtension.{u} (R.ring V) (ProEt.mk j)
  let LS := SheafOfModules.localizedModuleExtension.{u} (S.ring V) (ProEt.mk j)
  let adjR := openAdjunction R j
  let adjS := openAdjunction S j
  letI := SheafOfModules.localizedUnit_isIso j (R.ring V)
  letI := SheafOfModules.localizedUnit_isIso j (S.ring V)
  letI : LR.Full :=
    (SheafOfModules.localizedModuleAdjunctionIndependent
      (R.ring V) (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit.full
  letI : LR.Faithful :=
    (SheafOfModules.localizedModuleAdjunctionIndependent
      (R.ring V) (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit.faithful
  letI : LS.Full :=
    (SheafOfModules.localizedModuleAdjunctionIndependent
      (S.ring V) (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit.full
  letI : LS.Faithful :=
    (SheafOfModules.localizedModuleAdjunctionIndependent
      (S.ring V) (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit.faithful
  letI : (openExtension R j).Full := Functor.Full.of_iso hR.symm
  letI : (openExtension R j).Faithful := Functor.Faithful.of_iso hR.symm
  letI : (openExtension S j).Full := Functor.Full.of_iso hS.symm
  letI : (openExtension S j).Faithful := Functor.Faithful.of_iso hS.symm
  letI : IsIso adjS.unit := adjS.unit_isIso_of_L_fully_faithful
  obtain ⟨_, _, scalarIso, _, _⟩ :=
    SheafOfModules.RingedOpenScalar.comparison.{u + 1, u, 0, u + 2}
      (ProEt.mk j) (a.map V)
  letI := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hs : LR.essImage ((proEtaleRingRestrictScalars (a.map V)).obj
      ((openExtension S j).obj M)) := by
    refine Functor.essImage.ofIso
      ((scalarIso.app (eS.functor.obj M)).symm ≪≫
        (proEtaleRingRestrictScalars (a.map V)).mapIso (hS.app M).symm) ?_
    exact LR.obj_mem_essImage _
  have ht : (eR.functor ⋙ LR).essImage
      ((proEtaleRingRestrictScalars (a.map V)).obj ((openExtension S j).obj M)) :=
    Functor.essImage_comp_apply_of_essSurj.mpr hs
  haveI : IsIso (adjR.counit.app
      ((proEtaleRingRestrictScalars (a.map V)).obj ((openExtension S j).obj M))) :=
    adjR.isIso_counit_app_iff_mem_essImage.mpr (Functor.essImage.ofNatIso hR.symm ht)
  let t := inv (proEtaleRingRestrictionPullbackInv
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j))
  change IsIso
    (𝟙 _ ≫ (openExtension R j).map
      ((proEtaleRingRestrictScalars (a.map U)).map (adjS.unit.app M)) ≫
      (openExtension R j).map (𝟙 _) ≫
      (openExtension R j).map (t.app ((openExtension S j).obj M)) ≫
      (openExtension R j).map (𝟙 _) ≫
      adjR.counit.app
        ((proEtaleRingRestrictScalars (a.map V)).obj ((openExtension S j).obj M)) ≫ 𝟙 _)
  infer_instance

attribute [instance] openRestrictionMap_isIso

/-- Exact descent of the specified open coefficient square.
Source: Stacks Tag 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openRestriction {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
  Functor.mapDerivedCategorySquareIso (asIso (openRestrictionMap a j))

/-- Separately derived proper image after exact extension by zero.
Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def image (R : Coefficients.{u}) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (openExtension R c.i).mapDerivedCategory ⋙
    proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)

/-- Compact-support restriction: the open comparison followed by the canonical
K-injective direct-image comparison. This fixes the normalization before transposition.
Source: Stacks Tags 03DI, 0D6E
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def restriction {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    pbcDerivedRestrict (a.map X) ⋙ image R c ≅
      image S c ⋙ pbcDerivedRestrict (a.map Y) :=
  Functor.isoWhiskerRight (openRestriction a c.i)
      (proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)) ≪≫
    Functor.isoWhiskerLeft (openExtension S c.i).mapDerivedCategory
      (proEtaleRingRestrictionDerivedDirectImage c.g
        (R.ring Y) (S.ring Y) (R.ring c.Z) (S.ring c.Z)
        (a.map Y) (a.map c.Z) (R.pull c.g) (S.pull c.g) (a.square c.g)).symm

/-- The scalar comparison is the mate of the specified restriction square under the
canonical tensor-unit normalized scalar adjunctions. It therefore has precisely source
C_Y P_R and target P_S C_X.
Source: Stacks Tags 07A6, 0GL6
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def comparison {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    image R c ⋙ pbcDerivedExtend (a.map Y) ⟶
      pbcDerivedExtend (a.map X) ⋙ image S c :=
  ((mateEquiv (pbcDerivedScalarAdjunction (a.map X))
    (pbcDerivedScalarAdjunction (a.map Y))).symm
      (TwoSquare.mk _ _ _ _ (restriction a c).hom))

/-- The canonical composition of module direct images, fixed on every section.
Source: Stacks Tags 03D8, 0D6D
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: the fibre-product pasting isomorphism identifies test objects of the two
direct images. Pulling sections across it gives a natural bijection. Coefficient
compatibility makes it linear. Its inverse uses the inverse pasting isomorphism;
sectionwise faithfulness proves uniqueness. -/
theorem modulePushComposition_existsUnique (R : Coefficients.{u})
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :
    ∃! d : proEtaleRingModuleDirectImage h (R.ring V) (R.ring U) (R.pull h) ⋙
        proEtaleRingModuleDirectImage k (R.ring W) (R.ring V) (R.pull k) ≅
          proEtaleRingModuleDirectImage (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)),
      ∀ (N : pbcModules U (R.ring U)) (T : W.ProEt)
        (m : ((proEtaleRingModuleDirectImage h (R.ring V) (R.ring U) (R.pull h) ⋙
          proEtaleRingModuleDirectImage k (R.ring W) (R.ring V) (R.pull k)).obj N).val.obj
            (op T)),
        (d.hom.app N).val.app (op T) m =
          N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app T).op m := by
  obtain ⟨_, _, _, _, _, _, d, hd, _⟩ :=
    proEtaleRingDerivedPullbackComposition h k (R.ring W) (R.ring V) (R.ring U)
      (R.pull k) (R.pull h) (R.pull (h ≫ k)) hc
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact (he N T.unop m).trans (hd N T.unop m).symm

/-- Exact derived pullback composition, conjugate to sectionwise direct-image pasting.
Source: Stacks Tags 03D8, 0D6D
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def geometricPullComposition (R : Coefficients.{u})
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :
    proEtaleRingDerivedPullback (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)) ≅
      proEtaleRingDerivedPullback k (R.ring W) (R.ring V) (R.pull k) ⋙
        proEtaleRingDerivedPullback h (R.ring V) (R.ring U) (R.pull h) :=
  Functor.mapDerivedCategoryNatIso
    ((conjugateIsoEquiv
      ((proEtaleRingModuleAdjunction k (R.ring W) (R.ring V) (R.pull k)).comp
        (proEtaleRingModuleAdjunction h (R.ring V) (R.ring U) (R.pull h)))
      (proEtaleRingModuleAdjunction (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)))).symm
      (modulePushComposition_existsUnique R h k hc).exists.choose) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The fixed geometric pullback, with its original small-site universes.
Source: Stacks Tag 03D8
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
abbrev pull (R : Coefficients.{u}) {U V : Scheme.{u}} (g : U ⟶ V) :=
  proEtaleRingDerivedPullback g (R.ring V) (R.ring U) (R.pull g)

/-- Separately derived geometric direct image.
Source: Stacks Tag 07A5
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
abbrev push (R : Coefficients.{u}) {U V : Scheme.{u}} (g : U ⟶ V) :=
  proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g)

/-- The exact derived open adjunction, with its inherited unit normalization.
Source: Stacks Tag 03DI
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openDerivedAdjunction (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] : (openExtension R j).mapDerivedCategory ⊣ pull R j :=
  let J := openExtension R j
  let P := proEtaleRingModulePullback j (R.ring V) (R.ring U) (R.pull j)
  letI : CatCommSq (J.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q J.mapDerivedCategory := ⟨J.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (P.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q P.mapDerivedCategory := ⟨P.mapDerivedCategoryFactors.symm⟩
  ((openAdjunction R j).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    J.mapDerivedCategory P.mapDerivedCategory

/-- The open projection inverse is the adjoint of the open unit tensored with identity,
followed by inverse tensor pullback. Its inverse is the canonical open projection map.
Source: Stacks Tags 03DI, 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openProjectionInverse (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    (M : DerivedCategory (pbcModules U (R.ring U)))
    (N : DerivedCategory (pbcModules V (R.ring V))) :
    (openExtension R j).mapDerivedCategory.obj (a.tensor.obj (M, (pull R j).obj N)) ⟶
      b.tensor.obj ((openExtension R j).mapDerivedCategory.obj M, N) :=
  ((openDerivedAdjunction R j).homEquiv _ _).symm
    (a.tensor.map (Prod.mkHom ((openDerivedAdjunction R j).unit.app M) (𝟙 _)) ≫
      (proEtaleCanonicalTensorComparison j (R.ring V) (R.ring U) (R.pull j) b a).inv.app
        ((openExtension R j).mapDerivedCategory.obj M, N))

private theorem openProjectionInverse_naturality (R : Coefficients.{u})
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    {M M' : DerivedCategory (pbcModules U (R.ring U))}
    {N N' : DerivedCategory (pbcModules V (R.ring V))} (f : M ⟶ M') (g : N ⟶ N') :
    (openExtension R j).mapDerivedCategory.map
        (a.tensor.map (Prod.mkHom f ((pull R j).map g))) ≫
      openProjectionInverse R j a b M' N' =
    openProjectionInverse R j a b M N ≫
      b.tensor.map (Prod.mkHom ((openExtension R j).mapDerivedCategory.map f) g) := by
  let J := (openExtension R j).mapDerivedCategory
  let P := pull R j
  let adj := openDerivedAdjunction R j
  let e := proEtaleCanonicalTensorComparison j (R.ring V) (R.ring U) (R.pull j) b a
  apply adj.homEquiv_naturality_right_square
  change a.tensor.map (Prod.mkHom f (P.map g)) ≫
      (a.tensor.map (Prod.mkHom (adj.unit.app M') (𝟙 _)) ≫ e.inv.app (J.obj M', N')) =
    (a.tensor.map (Prod.mkHom (adj.unit.app M) (𝟙 _)) ≫ e.inv.app (J.obj M, N)) ≫
      P.map (b.tensor.map (Prod.mkHom (J.map f) g))
  have hn : Prod.mkHom f (P.map g) ≫ Prod.mkHom (adj.unit.app M') (𝟙 _) =
      Prod.mkHom (adj.unit.app M) (𝟙 _) ≫ (P.prod P).map (Prod.mkHom (J.map f) g) := by
    ext
    · exact adj.unit.naturality f
    · simp
  rw [← Category.assoc, ← a.tensor.map_comp, hn, a.tensor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  exact e.inv.naturality (Prod.mkHom (J.map f) g)

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  SheafOfModules.localizedSystemExtensionAdditive SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem openExtension_derivedSlicePresentation (R : Coefficients.{u})
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    ∃ e : DerivedCategory (pbcModules U (R.ring U)) ≌
        DerivedCategory (SheafOfModules.{u + 1} (((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.ring V)).over
            (ProEt.mk j))),
      Nonempty ((openExtension R j).mapDerivedCategory ≅ e.functor ⋙
        (SheafOfModules.localizedModuleExtension.{u} (R.ring V) (ProEt.mk j)).mapDerivedCategory)
        := by
  obtain ⟨e, ⟨he⟩⟩ := proEtaleOpen_slicePresentation j (R.ring V) (R.ring U) (R.pull j)
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  letI : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  exact ⟨e.mapDerivedCategory,
    ⟨Functor.mapDerivedCategoryNatIso he ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm⟩⟩

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  SheafOfModules.localizedSystemExtensionAdditive SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem sliceTensor_supported {V : Scheme.{u}}
    (R : Sheaf (ProEt.topology V) CommRingCat.{u + 1}) (W : V.ProEt)
    (a : ProEtaleTensorModel V R)
    (E : DerivedCategory (SheafOfModules.{u + 1}
      (((sheafCompose (ProEt.topology V)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over W)))
    (F : DerivedCategory (pbcModules V R)) :
    (SheafOfModules.localizedModuleExtension.{u} R W).mapDerivedCategory.essImage
      (a.tensor.obj ((SheafOfModules.localizedModuleExtension.{u} R W).mapDerivedCategory.obj E,
        F)) := by
  let L := SheafOfModules.localizedModuleExtension.{u} R W
  let P := DerivedCategory.Q.objPreimage E
  let N := DerivedCategory.Q.objPreimage F
  obtain ⟨Q, q, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients N
  haveI : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  let hQ : proEtaleFlatRepresentatives V R Q := ⟨hk, fun n ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (Q.X n)).symm (hf n)⟩
  let eF : DerivedCategory.Q.obj Q ≅ F :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso F
  let eE : L.mapDerivedCategory.obj E ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P) :=
    L.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
      L.mapDerivedCategoryFactors.app P
  obtain ⟨mixed, _⟩ := (proEtaleMixedTensor_existsUnique R a
    ((L.mapHomologicalComplex (.up ℤ)).obj P) Q hQ).exists
  obtain ⟨totalIso⟩ := SheafOfModules.extension_total_iso R W P Q
  let Z := (AlgebraicGeometry.Scheme.ProjectionRestriction.total (R.over W)).obj
    (P, ((SheafOfModules.localizedModuleRestriction.{u} R W).mapHomologicalComplex (.up ℤ)).obj Q)
  let e : a.tensor.obj (L.mapDerivedCategory.obj E, F) ≅
      L.mapDerivedCategory.obj (DerivedCategory.Q.obj Z) :=
    a.tensor.mapIso (Iso.prod eE eF.symm) ≪≫ mixed ≪≫
      DerivedCategory.Q.mapIso totalIso.symm ≪≫ (L.mapDerivedCategoryFactors.app Z).symm
  exact Functor.essImage.ofIso e.symm (L.mapDerivedCategory.obj_mem_essImage _)

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  SheafOfModules.localizedSystemExtensionAdditive SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
/-- The open projection inverse is invertible.
Source: Stacks Tag 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: identify derived open extension with a derived equivalence followed by exact
slice extension. Its unit is invertible by subterminality. Resolve only the ambient
tensor factor by a flat K-flat complex; the mixed representative comparison and the
ordinary slice-extension tensor isomorphism show that tensoring any extended object
remains in the essential image of extension. Thus the counit on the target tensor is
invertible. The defining adjunct is invertible, since it is the unit tensored with the
identity followed by the inverse tensor-pullback comparison. Its transpose is extension
of that adjunct followed by the invertible counit, hence is invertible. -/
theorem openProjectionInverse_isIso (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    (M : DerivedCategory (pbcModules U (R.ring U)))
    (N : DerivedCategory (pbcModules V (R.ring V))) :
    IsIso (openProjectionInverse R j a b M N) := by
  obtain ⟨e, ⟨he⟩⟩ := openExtension_derivedSlicePresentation R j
  let L := (SheafOfModules.localizedModuleExtension.{u} (R.ring V)
    (ProEt.mk j)).mapDerivedCategory
  let adjL := SheafOfModules.localizedModuleDerivedAdjunction.{u} (R.ring V) (ProEt.mk j)
  letI : IsIso adjL.unit := SheafOfModules.localizedDerivedUnit_isIso j (R.ring V)
  letI : L.Full := adjL.fullyFaithfulLOfIsIsoUnit.full
  letI : L.Faithful := adjL.fullyFaithfulLOfIsIsoUnit.faithful
  letI : (openExtension R j).mapDerivedCategory.Full := Functor.Full.of_iso he.symm
  letI : (openExtension R j).mapDerivedCategory.Faithful := Functor.Faithful.of_iso he.symm
  let adj := openDerivedAdjunction R j
  letI : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  have hs : L.essImage
      (b.tensor.obj ((openExtension R j).mapDerivedCategory.obj M, N)) :=
    Functor.essImage.ofIso
      (b.tensor.mapIso (Iso.prod (he.app M).symm (Iso.refl N)))
      (sliceTensor_supported (R.ring V) (ProEt.mk j) b (e.functor.obj M) N)
  have ht : (e.functor ⋙ L).essImage
      (b.tensor.obj ((openExtension R j).mapDerivedCategory.obj M, N)) :=
    Functor.essImage_comp_apply_of_essSurj.mpr hs
  haveI : IsIso (adj.counit.app
      (b.tensor.obj ((openExtension R j).mapDerivedCategory.obj M, N))) :=
    adj.isIso_counit_app_iff_mem_essImage.mpr (Functor.essImage.ofNatIso he.symm ht)
  let q := Prod.mkHom (adj.unit.app M) (𝟙 ((pull R j).obj N))
  haveI : IsIso q := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  change IsIso ((adj.homEquiv _ _).symm
    (a.tensor.map q ≫
      (proEtaleCanonicalTensorComparison j (R.ring V) (R.ring U) (R.pull j) b a).inv.app
        ((openExtension R j).mapDerivedCategory.obj M, N)))
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The specified open projection isomorphism.
Source: Stacks Tag 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openProjectionIso (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    (M : DerivedCategory (pbcModules U (R.ring U)))
    (N : DerivedCategory (pbcModules V (R.ring V))) :=
  (@asIso _ _ _ _ (openProjectionInverse R j a b M N)
    (openProjectionInverse_isIso R j a b M N)).symm

/-- Curried presentation of the already supplied actual derived tensor model.
Source: Stacks Tag 07A4
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
abbrev tensorCurried {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : ProEtaleTensorModel W R) :=
  Functor.curry.obj a.tensor

/-- The open projection followed by the specified f=pj pullback identification.
Source: blueprint def-exchange-projection, gamma
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def projectionOpenFactor (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : ProEtaleTensorModel X (R.ring X)) (b : ProEtaleTensorModel c.Z (R.ring c.Z))
    (hc : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (M : DerivedCategory (pbcModules X (R.ring X)))
    (N : DerivedCategory (pbcModules Y (R.ring Y))) :=
  openProjectionIso R c.i a b M ((pull R c.g).obj N) ≪≫
    (openExtension R c.i).mapDerivedCategory.mapIso
      (a.tensor.mapIso (Iso.prod (Iso.refl M)
        (((geometricPullComposition R c.i c.g hc).symm ≪≫
          eqToIso (congrArg (fun g : X ⟶ Y ↦ pull R g) c.comm.symm)).app N)))

/-- The supplied-domain comparison types of def-exchange-projection, fixed componentwise
by the canonical tensor-pullback and open projection constructions above.
Source: blueprint def-exchange-projection, supplied-domain paragraph
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
structure ProjectionComparisons (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : ProEtaleTensorModel X (R.ring X)) (b : ProEtaleTensorModel c.Z (R.ring c.Z))
    (d : ProEtaleTensorModel Y (R.ring Y))
    (hc : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i)) where
  tensorPullback :
    (Functor.postcompose₂.obj (pull R c.g)).obj (tensorCurried d) ≅
      (((Functor.whiskeringLeft₂ _).obj (pull R c.g)).obj (pull R c.g)).obj (tensorCurried b)
  openProjection :
    (((Functor.whiskeringLeft₂ _).obj (openExtension R c.i).mapDerivedCategory).obj
        (pull R c.g)).obj (tensorCurried b) ≅
      (Functor.postcompose₂.obj (openExtension R c.i).mapDerivedCategory).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj (pull R f)).obj (tensorCurried a))
  tensorPullback_eq : ∀ M N,
    (tensorPullback.hom.app M).app N =
      (proEtaleCanonicalTensorComparison c.g (R.ring Y) (R.ring c.Z) (R.pull c.g) d b).hom.app
        (M, N)
  openProjection_eq : ∀ M N,
    (openProjection.hom.app M).app N = (projectionOpenFactor R c a b hc M N).hom

set_option linter.unusedVariables false in
/-- These comparison data exist uniquely, since their components were independently fixed.
Source: Stacks Tags 07A4, 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: curry the canonical natural tensor-pullback comparison. Naturality of the open
unit and tensor comparison makes openProjectionInverse natural; its inverse and
pullback composition remain natural. Curry their composite to obtain gamma.
The two displayed component identities hold by construction. Natural transformations
are determined by components, and currying is faithful, so the data are unique. -/
theorem projectionComparisons_existsUnique (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : ProEtaleTensorModel X (R.ring X)) (b : ProEtaleTensorModel c.Z (R.ring c.Z))
    (d : ProEtaleTensorModel Y (R.ring Y))
    (hc : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i)) :
    ∃! data : ProjectionComparisons R c a b d hc, True := by
  let J := (openExtension R c.i).mapDerivedCategory
  let P := pull R c.g
  let I := pull R c.i
  let F := pull R f
  let e : P ⋙ I ≅ F := (geometricPullComposition R c.i c.g hc).symm ≪≫
    eqToIso (congrArg (fun g : X ⟶ Y ↦ pull R g) c.comm.symm)
  let betaInv : ((𝟭 _).prod I ⋙ a.tensor) ⋙ J ≅ J.prod (𝟭 _) ⋙ b.tensor :=
    NatIso.ofComponents (fun MN ↦ (openProjectionIso R c.i a b MN.1 MN.2).symm)
      (fun h ↦ openProjectionInverse_naturality R c.i a b h.1 h.2)
  let beta : J.prod P ⋙ b.tensor ≅ ((𝟭 _).prod (P ⋙ I) ⋙ a.tensor) ⋙ J :=
    Functor.isoWhiskerLeft ((𝟭 _).prod P) betaInv.symm
  let eta : (𝟭 (DerivedCategory (pbcModules X (R.ring X)))).prod (P ⋙ I) ≅
      (𝟭 (DerivedCategory (pbcModules X (R.ring X)))).prod F :=
    NatIso.ofComponents (fun MN ↦ Iso.prod (Iso.refl MN.1) (e.app MN.2)) (by
      intro MN MN' h
      ext
      · simp
      · exact e.hom.naturality h.2)
  let gamma : J.prod P ⋙ b.tensor ≅ ((𝟭 _).prod F ⋙ a.tensor) ⋙ J :=
    beta ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerRight eta a.tensor) J
  let tau :=
    proEtaleCanonicalTensorComparison c.g (R.ring Y) (R.ring c.Z) (R.pull c.g) d b
  let data : ProjectionComparisons R c a b d hc :=
    { tensorPullback := NatIso.ofComponents
        (fun M ↦ NatIso.ofComponents (fun N ↦ tau.app (M, N)) (by
          intro N N' h
          simpa using tau.hom.naturality (Prod.mkHom (𝟙 M) h))) (by
          intro M M' h
          ext N
          simpa using tau.hom.naturality (Prod.mkHom h (𝟙 N)))
      openProjection := NatIso.ofComponents
        (fun M ↦ NatIso.ofComponents (fun N ↦ gamma.app (M, N)) (by
          intro N N' h
          simpa using gamma.hom.naturality (Prod.mkHom (𝟙 M) h))) (by
          intro M M' h
          ext N
          simpa using gamma.hom.naturality (Prod.mkHom h (𝟙 N)))
      tensorPullback_eq := fun M N ↦ rfl
      openProjection_eq := fun M N ↦ rfl }
  refine ⟨data, trivial, ?_⟩
  intro data' _
  have ht : data'.tensorPullback = data.tensorPullback := by
    apply Iso.ext
    ext M N
    exact (data'.tensorPullback_eq M N).trans (data.tensorPullback_eq M N).symm
  have ho : data'.openProjection = data.openProjection := by
    apply Iso.ext
    ext M N
    exact (data'.openProjection_eq M N).trans (data.openProjection_eq M N).symm
  cases data' with
  | mk t o ht' ho' =>
    dsimp only at ht ho
    cases ht
    cases ho
    rfl

/-- The actual compact-support projection from def-exchange-projection, using its
existing supplied-domain construction and the uniquely normalized comparison data.
Source: blueprint def-exchange-projection, projection formula
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def projectionMap (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : ProEtaleTensorModel X (R.ring X)) (b : ProEtaleTensorModel c.Z (R.ring c.Z))
    (d : ProEtaleTensorModel Y (R.ring Y))
    (hc : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i)) :=
  let data := (projectionComparisons_existsUnique R c a b d hc).exists.choose
  SuppliedExchangeProjection.compactificationProjectionFromData
    (openExtension R c.i).mapDerivedCategory (pull R f)
    (pull R c.g) (push R c.g)
    (proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z) (R.pull c.g))
    (tensorCurried a) (tensorCurried b) (tensorCurried d) data.tensorPullback data.openProjection

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The inverse-image coefficient map adjoint to the canonical completed direct-image map.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def completedPullMap {U V : Scheme.{u}} (g : U ⟶ V) :=
  ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
    (sfCompletedCoefficientMap l E g)

private theorem completedPull_projection {U V : Scheme.{u}} (g : U ⟶ V) (n : ℕ) :
    completedPullMap l E g ≫ completedIntegralCommRingProjectionUnrestricted l E U n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (completedIntegralCommRingProjectionUnrestricted l E V n) ≫
      proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  change (adj.homEquiv _ _).symm _ ≫ _ = _ ≫ (adj.homEquiv _ _).symm _
  rw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_left_symm]
  exact congrArg (adj.homEquiv _ _).symm
    ((sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec n)

private theorem completed_hom_ext {W : Scheme.{u}}
    {T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    {a b : T ⟶ completedIntegralCommRingSheafUnrestricted l E W}
    (h : ∀ n : ℕ, a ≫ completedIntegralCommRingProjectionUnrestricted l E W n =
      b ≫ completedIntegralCommRingProjectionUnrestricted l E W n) : a = b := by
  let H := sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply H.map_injective
  apply limit.hom_ext
  intro n
  exact congrArg H.map (h n.unop)

/-- Canonical inverse image of the completed coefficient sheaf is invertible.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: the profinite-coefficient inverse-image theorem identifies the pullback of the
finite quotient system with the source quotient system, compatibly with projections.
The inverse limit and its constant-section maps identify its completed comparison
with the adjoint of sfCompletedCoefficientMap, since every projection agrees. -/
theorem completedPullMap_isIso {U V : Scheme.{u}} (g : U ⟶ V) :
    IsIso (completedPullMap l E g) := by
  have he : completedPullMap l E g = (coefficient_inverse_image_iso l E g).hom := by
    apply ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).injective
    change (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
        (sfCompletedCoefficientMap l E g)) = _
    rw [Equiv.apply_symm_apply]
    exact (coefficient_direct_image_eq l E g).symm
  rw [he]
  infer_instance

attribute [instance] completedPullMap_isIso

/-- The specified completed coefficient system, with no identification with a discrete
constant integral sheaf. Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def completed : Coefficients.{u} where
  ring := completedIntegralCommRingSheafUnrestricted l E
  pull g := asIso (completedPullMap l E g)

/-- Completed coefficient inverse-image identifications respect composition.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: take adjoints and compose with all finite projections. Both sides become the
same constant quotient pullback-composition map. Its constant-section normalization
identifies them, and the completed projections are jointly monic. -/
theorem completedPull_comp {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) :
    (completed l E).pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      ((completed l E).ring W) ((completed l E).ring V) ((completed l E).ring U)
        ((completed l E).pull k) ((completed l E).pull h) := by
  apply Iso.ext
  apply completed_hom_ext l E
  intro n
  change completedPullMap l E (h ≫ k) ≫ _ =
    ((proEtaleRingInverseImageComp h k).hom.app _ ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map (completedPullMap l E k) ≫
        completedPullMap l E h) ≫ _
  rw [completedPull_projection]
  simp only [Category.assoc]
  rw [completedPull_projection, ← Functor.map_comp_assoc, completedPull_projection,
    Functor.map_comp]
  have hn := (proEtaleRingInverseImageComp h k).hom.naturality
    (completedIntegralCommRingProjectionUnrestricted l E W n)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, ← hn]
  simp only [Category.assoc]
  congr 1
  exact proEtaleConstantComparison_comp h k _

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Compatibility of the actual completed coefficient inclusion with inverse image.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: take adjoints and compose with each target finite projection. The completed
structure maps become their constant quotient maps and both routes are induced by
the same inclusion of integer rings. The inverse-limit projections are jointly monic. -/
theorem completedChange_square {U V : Scheme.{u}} (g : U ⟶ V) :
    ((completed l E).pull g).hom ≫ completedCoefficientMap l E F i U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (completedCoefficientMap l E F i V) ≫ ((completed l F).pull g).hom := by
  apply completed_hom_ext l F
  intro n
  change (completedPullMap l E g ≫ completedCoefficientMap l E F i U) ≫ _ =
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (completedCoefficientMap l E F i V) ≫ completedPullMap l F g) ≫ _
  have hp (W : Scheme.{u}) : completedCoefficientMap l E F i W ≫
      completedIntegralCommRingProjectionUnrestricted l F W n =
    completedIntegralCommRingProjectionUnrestricted l E W n ≫
      integralScalarQuotientSheafMap l E F i W n :=
    (completedCoefficientMap_existsUnique l E F i W).exists.choose_spec n
  simp only [Category.assoc]
  rw [hp, ← Category.assoc, completedPull_projection, Category.assoc]
  have hn := proEtaleConstantInverseImageMap_naturality g
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
        ((integralScalarQuotientMap l E F i n).comp
          (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom)))
  change (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (integralScalarQuotientSheafMap l E F i V n) ≫ _ =
    _ ≫ integralScalarQuotientSheafMap l E F i U n at hn
  rw [← hn]
  rw [completedPull_projection, ← Functor.map_comp_assoc, ← hp, Functor.map_comp]
  simp only [Category.assoc]

/-- The finite quotient coefficient system at the positive exponent n.
Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def finite (n : ℕ) (hn : 1 ≤ n) : Coefficients.{u} where
  ring W := proEtaleConstantRing W (Padic.coefficientExtensionRing l E n)
  pull g := @sfConstantCoefficientIso _ _ g (Padic.coefficientExtensionRing l E n) _
    (Padic.finite_coefficientExtensionRing l E n hn)

/-- The completed coefficient projection at an arbitrary positive exponent.
Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def projection (n : ℕ) (hn : 1 ≤ n) (W : Scheme.{u}) :
    (completed l E).ring W ⟶ (finite l E n hn).ring W :=
  completedIntegralCommRingProjectionUnrestricted l E W (n - 1) ≫
    eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
      (Padic.coefficientExtensionRing l E k)) (Nat.sub_add_cancel hn))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))] [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

end WeilConjectures.PurCompactSupport
