/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor
import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportRestrictionComposition

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
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import all WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import all WeilConjectures.SixFunctors.Supporting.WfConstructibleTensorKoszulUnit
import WeilConjectures.SixFunctors.CompactSupportCoefficientTensor.ProjectionTensorCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.DimensionFiniteTypeField
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportRestrictionShift
import WeilConjectures.SmoothPurity.PurCompactSupport.FiniteProperComparisonIso
import WeilConjectures.SmoothPurity.Completed.CompletedQuotientProperMate
import WeilConjectures.SmoothPurity.PurCompactSupport.FiniteFreeRestrictionDirectImageMate
import WeilConjectures.SmoothPurity.Integral.IntegralProperOpenDerivedLimit
import WeilConjectures.SmoothPurity.Finite.FiniteTorIntegralCompletedScalarExtension
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import all WeilConjectures.CategoryTheory.SmoothPurity.AdicBasisLimit
import WeilConjectures.CategoryTheory.Constant.ConstantSpecifiedBasis

/-! # Integral compact-support coefficient comparison

Source: Weil blueprint, theorem-smooth-purity-all-admissible-coefficients, Step 3; Bhatt--Scholze,
Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).

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
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures.PurCompactSupport
attribute [local instance 100000] CategoryTheory.HasSheafify.isRightAdjoint
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
attribute [local irreducible] CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification
  AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
  AlgebraicGeometry.Scheme.completedAdicChange AlgebraicGeometry.Scheme.reductionChange
  CategoryTheory.Localization.Monoidal.tensorBifunctor
  HasDerivedCategory.standard CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor

attribute [local instance 100000] coefficientSiteSmall coefficientRingSheafify
  coefficientAbSheafify coefficientAbLocallyBijective

private theorem scalarKanCommShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

-- The comparison determines the shift structure by Kan uniqueness, degree by degree.
private theorem scalarRightKanShift_unique
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ]
    {E : Type*} [Category* E] [HasShift E ℤ]
    (F : C ⥤ E) [F.CommShift ℤ] (Q : C ⥤ D) [Q.CommShift ℤ]
    (LF : D ⥤ E) (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α]
    (s t : LF.CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift α ℤ)
    (ht : letI := t; NatTrans.CommShift α ℤ) : s = t := by
  have square (q : LF.CommShift ℤ) (hq : letI := q; NatTrans.CommShift α ℤ)
      (n : ℤ) (X : C) :
      LF.map ((Q.commShiftIso n).hom.app X) ≫
          (Functor.commShiftIso LF (self := q) n).hom.app (Q.obj X) ≫
            (shiftFunctor E n).map (α.app X) =
        α.app ((shiftFunctor C n).obj X) ≫ (F.commShiftIso n).hom.app X := by
    let := q
    have := hq
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm α n X
  have he (n : ℤ) : Functor.commShiftIso LF (self := s) n =
      Functor.commShiftIso LF (self := t) n := by
    apply Iso.ext
    apply Functor.kanShiftHom_ext F Q LF α n
    intro X
    apply (cancel_epi (LF.map ((Q.commShiftIso n).hom.app X))).1
    simpa only [Category.assoc] using (square s hs n X).trans (square t ht n X).symm
  exact scalarKanCommShift_ext s t he

private theorem inverse_mate_shift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {G : C ⥤ D} {H : E ⥤ F} {L₁ : C ⥤ E} {R₁ : E ⥤ C}
    {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    [G.CommShift ℤ] [H.CommShift ℤ] [L₁.CommShift ℤ] [R₁.CommShift ℤ]
    [L₂.CommShift ℤ] [R₂.CommShift ℤ]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) [a.CommShift ℤ] [b.CommShift ℤ]
    (t : TwoSquare R₁ H G R₂) [NatTrans.CommShift t ℤ] :
    NatTrans.CommShift ((mateEquiv a b).symm t) ℤ := by
  change NatTrans.CommShift
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight a.unit (G ⋙ L₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
      Functor.whiskerRight (Functor.whiskerLeft L₁ t) L₂ ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (L₁ ⋙ H) b.counit ≫
      (Functor.rightUnitor _).hom) ℤ
  infer_instance

/-- Normalization of a shift structure by the actual universal scalar counit.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def IsScalarShiftNormalized {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (s : (pbcDerivedExtend a).CommShift ℤ) : Prop :=
  letI := s
  (pbcExtensionCounit a).CommShift ℤ

/-- The derived scalar counit uniquely normalizes its shift structure.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: ordinary additive scalar extension commutes with shifts degreewise. The
universal left-derived counit lifts this square uniquely to the localization.
The lifted squares satisfy zero and addition because their composites with the
universal counit do. This gives existence, and the same uniqueness gives uniqueness. -/
theorem scalarCommShift_existsUnique {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ∃! s : (pbcDerivedExtend a).CommShift ℤ, IsScalarShiftNormalized a s := by
  have := pbcDerivedExtension_universal a
  have hkan := Functor.IsLeftDerivedFunctor.isRightKanExtension
    (pbcDerivedExtend a) (pbcExtensionCounit a)
    (HomotopyCategory.quasiIso (pbcModules W R) (.up ℤ))
  have := hkan
  obtain ⟨s, hs⟩ := Functor.rightKanExtension_coherentShift _
    DerivedCategory.Qh (pbcDerivedExtend a) (pbcExtensionCounit a) hkan
  exact ⟨s, hs, fun t ht ↦ scalarRightKanShift_unique _ _ _ _ t s ht hs⟩

/-- The scalar shift is fixed by its universal derived counit.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
instance scalarCommShift {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (pbcDerivedExtend a).CommShift ℤ :=
  (scalarCommShift_existsUnique a).exists.choose

/-- The shift on compact support is exact open descent followed by the canonical
K-injective proper-image shift. Source: Stacks Tags 03DI, 070K
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
instance imageCommShift (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (image R c).CommShift ℤ := by
  unfold image
  infer_instance

/-- The scalar mate commutes with the canonical shift comparisons.
Source: Stacks Tag 07A6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: on complexes the coefficient maps are degreewise and commute with shift without
an extra sign. The exact open comparison and the right-derived proper comparison
preserve their universal counits and units. Transpose this identity under the derived
scalar adjunctions; the triangle identities give precisely NatTrans.CommShift. -/
theorem comparison_commShift {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (comparison a c).CommShift ℤ := by
  letI : (pbcDerivedRestrict (a.map X)).CommShift ℤ :=
    Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt (pbcRestrict (a.map X))
  letI : (pbcDerivedRestrict (a.map Y)).CommShift ℤ :=
    Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt (pbcRestrict (a.map Y))
  letI : NatTrans.CommShift (pbcExtensionCounit (a.map X)) ℤ :=
    (scalarCommShift_existsUnique (a.map X)).exists.choose_spec
  letI : NatTrans.CommShift (pbcExtensionCounit (a.map Y)) ℤ :=
    (scalarCommShift_existsUnique (a.map Y)).exists.choose_spec
  have hAdjX := restrictionScalarAdjunction_shift (a.map X)
  have hAdjY := restrictionScalarAdjunction_shift (a.map Y)
  letI : (pbcDerivedScalarAdjunction (a.map X)).CommShift ℤ := hAdjX
  letI : (pbcDerivedScalarAdjunction (a.map Y)).CommShift ℤ := hAdjY
  letI : (image R c).CommShift ℤ := imageCommShift R c
  letI : (image S c).CommShift ℤ := imageCommShift S c
  have hres : NatTrans.CommShift (restriction a c).hom ℤ :=
    restriction_commShift a c
  unfold comparison
  exact inverse_mate_shift
    (pbcDerivedScalarAdjunction (a.map X))
    (pbcDerivedScalarAdjunction (a.map Y))
    (TwoSquare.mk _ _ _ _ (restriction a c).hom)
/-- Ordinary tensor associativity, fixed by the two tensor-unit normalized adjunctions.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def tensorComposition {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (d : R ⟶ T) (h : a ≫ b = d) :
    pbcDerivedExtend a ⋙ pbcDerivedExtend b ≅ pbcDerivedExtend d :=
  (((pbcDerivedScalarAdjunction a).comp (pbcDerivedScalarAdjunction b)).ofNatIsoRight
    (pbcDerivedRestrictComp a b d h)).leftAdjointUniq (pbcDerivedScalarAdjunction d)

/-- Scalar composition, including quotient reductions, for the specified mates.
Source: Stacks Tag 07A6, mate pasting
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: transpose under the scalar adjunctions. The tensor-composition maps carry the
successive units to the direct unit. The proper restriction comparisons compose
because their ordinary maps are identity on sections and their derived units agree.
The open comparisons compose by their unit normalization. Thus the two transposes
are equal. The Hom adjunction is bijective, which proves the displayed equality. -/
theorem comparison_composition {R S T : Coefficients.{u}}
    (a : Change R S) (b : Change S T) (d : Change R T)
    (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (pbcDerivedExtend (b.map Y)).map ((comparison a c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (a.map X)).obj M) ≫
        (image T c).map ((tensorComposition (a.map X) (b.map X) (d.map X) (h X)).hom.app M) =
      (tensorComposition (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.app
          ((image R c).obj M) ≫ (comparison d c).app M :=
  CategoryTheory.mateEquiv_symm_app_comp_leftAdjointUniq (image R c) (image S c) (image T c)
    (pbcDerivedScalarAdjunction (a.map X)) (pbcDerivedScalarAdjunction (b.map X))
    (pbcDerivedScalarAdjunction (d.map X)) (pbcDerivedScalarAdjunction (a.map Y))
    (pbcDerivedScalarAdjunction (b.map Y)) (pbcDerivedScalarAdjunction (d.map Y))
    (pbcDerivedRestrictComp (a.map X) (b.map X) (d.map X) (h X))
    (pbcDerivedRestrictComp (a.map Y) (b.map Y) (d.map Y) (h Y))
    (restriction a c).hom (restriction b c).hom (restriction d c).hom
    (fun N ↦ restriction_comp a b d h c N) M

/-- Identity scalar restriction has the identity section functions, uniquely.
Source: Stacks Tag 03DA
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: the restricted action along identity is the original action. Identity on the
underlying abelian sheaf is linear and natural. Sectionwise faithfulness gives uniqueness. -/
theorem restrictIdentity_existsUnique {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    ∃! e : pbcRestrict (𝟙 R) ≅ 𝟭 _,
      ∀ (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        (e.hom.app M).val.app U x = x := by
  let eM (M : pbcModules W R) : (pbcRestrict (𝟙 R)).obj M ≅ M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App (RingHom.id (R.obj.obj U)) rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))
  let e : pbcRestrict (𝟙 R) ≅ 𝟭 _ :=
    NatIso.ofComponents eM (fun f ↦ by ext U x; rfl)
  refine ⟨e, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e' he'
    apply Iso.ext
    ext M U x
    exact he' M U x

/-- The multiplication unit C_R,R is conjugate to identity scalar restriction.
Source: Stacks Tags 03DA, 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def tensorIdentity {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    pbcDerivedExtend (𝟙 R) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (pbcDerivedScalarAdjunction (𝟙 R))
    (Adjunction.id : (𝟭 (DerivedCategory (pbcModules W R))) ⊣ 𝟭 _)).symm
      (Functor.mapDerivedCategoryNatIso (restrictIdentity_existsUnique R).exists.choose ≪≫
        Functor.mapDerivedCategoryIdIso _)).symm

section IdentityProof

attribute [local irreducible] pbcDerivedScalarAdjunction tensorComposition tensorIdentity

private theorem derivedRestriction_left_unit
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (U : A ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (ρ : U ≅ 𝟭 A) :
    Functor.mapDerivedCategoryCompIso U U ≪≫
        Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft U ρ) =
      Functor.isoWhiskerLeft U.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso A) ≪≫
        Functor.rightUnitor U.mapDerivedCategory := by
  apply Iso.ext
  ext X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft U ρ) X
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id U) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hn hu
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U U).inv.app X)).mp
  rw [Iso.inv_hom_id_app_assoc]
  simp only [← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  simp only [NatTrans.id_app] at hu
  rw [reassoc_of% hu]
  erw [Category.comp_id, Category.comp_id]

private theorem identityConjugate {A : Type*} [Category A]
    {F U : A ⥤ A} (a : F ⊣ U) (e : U ≅ 𝟭 A) :
    a.leftAdjointIdIso e = ((conjugateIsoEquiv a Adjunction.id).symm e).symm := by
  rfl

private theorem normalizedComparison_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {U : B ⥤ A} {V : C ⥤ B} {W : C ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (d : V ⋙ U ≅ W) :
    ((a.comp b).ofNatIsoRight d).leftAdjointUniq c =
      a.leftAdjointCompIso b c d := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, Adjunction.leftAdjointCompIso_hom_app,
    conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight_counit, NatTrans.id_app,
    NatTrans.comp_app, Functor.whiskerRight_app]
  rw [(F ⋙ G).map_id, Category.id_comp, Adjunction.comp_counit_app]
  simp only [Functor.comp_map]

private theorem tensorComposition_identity_left {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (K : DerivedCategory (pbcModules W R)) :
    (tensorComposition (𝟙 R) (𝟙 R) (𝟙 R)
      (Category.id_comp _)).hom.app K =
      (pbcDerivedExtend (𝟙 R)).map ((tensorIdentity R).hom.app K) := by
  let ρ := (restrictIdentity_existsUnique R).exists.choose
  let δ := Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso _
  have he : pbcRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcRestrict (𝟙 R)) ρ := by
    apply Iso.ext
    ext M U x
    exact (pbcRestrictComp_exists (𝟙 R) (𝟙 R) (𝟙 R)
      (Category.id_comp _)).exists.choose_spec M U x |>.trans
        ((restrictIdentity_existsUnique R).exists.choose_spec M U x).symm
  have hd : pbcDerivedRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcDerivedRestrict (𝟙 R)) δ ≪≫
        Functor.rightUnitor (pbcDerivedRestrict (𝟙 R)) := by
    unfold pbcDerivedRestrictComp
    rw [he]
    exact derivedRestriction_left_unit (pbcRestrict (𝟙 R)) ρ
  have h := congrArg (fun e ↦ e.hom.app K)
    (Adjunction.leftAdjointCompIso_id_comp (pbcDerivedScalarAdjunction (𝟙 R))
      (pbcDerivedScalarAdjunction (𝟙 R)) _ δ hd)
  have hn := normalizedComparison_eq (pbcDerivedScalarAdjunction (𝟙 R))
    (pbcDerivedScalarAdjunction (𝟙 R)) (pbcDerivedScalarAdjunction (𝟙 R))
    (pbcDerivedRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _))
  unfold tensorComposition
  change ((((pbcDerivedScalarAdjunction (𝟙 R)).comp
    (pbcDerivedScalarAdjunction (𝟙 R))).ofNatIsoRight
      (pbcDerivedRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _))).leftAdjointUniq
        (pbcDerivedScalarAdjunction (𝟙 R))).hom.app K = _
  rw [hn]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
  erw [Category.comp_id] at h
  have hu : (pbcDerivedScalarAdjunction (𝟙 R)).leftAdjointIdIso δ =
      tensorIdentity R := by
    unfold tensorIdentity
    exact identityConjugate _ _
  rw [hu] at h
  exact h

private theorem tensorComposition_identity_left_of_eq {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) (a : R ⟶ R)
    (ha : a = 𝟙 R) (hc : a ≫ a = a) (K : DerivedCategory (pbcModules W R)) :
    (tensorComposition a a a hc).hom.app K =
      (pbcDerivedExtend a).map
        ((eqToIso (congrArg (fun a ↦ pbcDerivedExtend a) ha) ≪≫
          tensorIdentity R).hom.app K) := by
  cases ha
  rw [eqToIso_refl, Iso.refl_trans]
  exact tensorComposition_identity_left R K

private theorem identity_inverseMate_isIso
    {C D : Type*} [Category C] [Category D]
    {L₁ R₁ : C ⥤ C} {L₂ R₂ : D ⥤ D} {G : C ⥤ D}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (eL : L₁ ≅ 𝟭 C) (eR : R₂ ≅ 𝟭 D)
    (t : R₁ ⋙ G ≅ G ⋙ R₂) :
    IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ t.hom))) := by
  letI : L₁.Full := Functor.Full.of_iso eL.symm
  letI : L₁.Faithful := Functor.Faithful.of_iso eL.symm
  letI : R₂.Full := Functor.Full.of_iso eR.symm
  letI : R₂.Faithful := Functor.Faithful.of_iso eR.symm
  haveI : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  haveI : IsIso b.counit := b.counit_isIso_of_R_fully_faithful
  rw [mateEquiv_symm_apply]
  infer_instance

/-- Multiplication normalizes the identity coefficient comparison.
Source: Stacks Tags 03DA, 07A6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: transpose the identity coefficient square. Its section maps are identities,
its proper derived comparison preserves the derived unit, and its open mate
preserves the open unit. The scalar multiplication iso is their conjugate, so the
two composites have identical transposes and hence are equal. -/
theorem comparison_identity {R : Coefficients.{u}} (a : Change R R)
    (h : ∀ W : Scheme.{u}, a.map W = 𝟙 (R.ring W))
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (comparison a c).app M ≫ (image R c).map
        ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (h X)) ≪≫
          tensorIdentity (R.ring X)).hom.app M) =
      (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (h Y)) ≪≫
        tensorIdentity (R.ring Y)).hom.app ((image R c).obj M) := by
  let v (W : Scheme.{u}) :=
    eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (h W)) ≪≫ tensorIdentity (R.ring W)
  have hi : IsIso (comparison a c) := by
    let ρY := Functor.mapDerivedCategoryNatIso
      (restrictIdentity_existsUnique (R.ring Y)).exists.choose ≪≫
        Functor.mapDerivedCategoryIdIso _
    let eR : pbcDerivedRestrict (a.map Y) ≅ 𝟭 _ :=
      eqToIso (congrArg (fun φ ↦ pbcDerivedRestrict φ) (h Y)) ≪≫ ρY
    exact identity_inverseMate_isIso
      (pbcDerivedScalarAdjunction (a.map X)) (pbcDerivedScalarAdjunction (a.map Y))
      (v X) eR (restriction a c)
  have hc (W : Scheme.{u}) : a.map W ≫ a.map W = a.map W := by
    rw [h W, Category.id_comp]
  have hcomp := comparison_composition a a a hc c M
  rw [tensorComposition_identity_left_of_eq (R.ring X) (a.map X) (h X),
    tensorComposition_identity_left_of_eq (R.ring Y) (a.map Y) (h Y)] at hcomp
  let T := pbcDerivedExtend (a.map Y)
  letI : T.Faithful := Functor.Faithful.of_iso (v Y).symm
  apply T.map_injective
  apply (cancel_mono ((comparison a c).app M)).mp
  have hn := (comparison a c).naturality ((v X).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  change T.map ((comparison a c).app M) ≫ _ ≫ _ =
    T.map ((v Y).hom.app ((image R c).obj M)) ≫ _ at hcomp
  rw [← hn] at hcomp
  simpa only [T, v, Functor.id_obj, Functor.map_comp, Category.assoc] using hcomp

end IdentityProof

attribute [local irreducible] scalarTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Proper derived composition is the conjugate of this normalized pullback composition.
Source: Stacks Tag 0D6D
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def geometricPushComposition (R : Coefficients.{u})
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction k (R.ring W) (R.ring V) (R.pull k)).comp
      (proEtaleRingDerivedAdjunction h (R.ring V) (R.ring U) (R.pull h)))
    (proEtaleRingDerivedAdjunction (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)))
    (geometricPullComposition R h k hc)

/-- Pullback pasting along a refinement, including the equation of its open triangle.
Source: Stacks Tags 03D8, 0D6D
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def refinementPull (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hc : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i)) :
    pull R d.i ≅ pull R r.hom ⋙ pull R c.i :=
  eqToIso (congrArg (fun g : X ⟶ d.Z ↦ pull R g) r.i_hom.symm) ≪≫
    geometricPullComposition R c.i r.hom hc

/-- Restricting the proper refinement image to X, via the proper counit.
This is the normalization used to specify the proper-open comparison.
Source: blueprint prop-compactification-coherence, proof part (a)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def refinementRestriction (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hc : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (pull R d.i).obj ((push R r.hom).obj
        ((openExtension R c.i).mapDerivedCategory.obj M)) ⟶
      (pull R c.i).obj ((openExtension R c.i).mapDerivedCategory.obj M) :=
  (refinementPull R r hc).hom.app _ ≫
    (pull R c.i).map ((proEtaleRingDerivedAdjunction r.hom
      (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit.app _)

/-- The canonical scalar/pullback comparison is the unique left-adjoint comparison
conjugate to the normalized proper-image restriction square.
Source: Stacks Tags 03D8, 06YY, 07A6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def scalarPull {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    pull R g ⋙ pbcDerivedExtend (a.map U) ≅ pbcDerivedExtend (a.map V) ⋙ pull S g :=
  (((proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)).comp
    (pbcDerivedScalarAdjunction (a.map U))).ofNatIsoRight
      (proEtaleRingRestrictionDerivedDirectImage g
        (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).symm).leftAdjointUniq
          ((pbcDerivedScalarAdjunction (a.map V)).comp
            (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g)))

/-- Arithmetic restriction retains precisely the positive exponents e(n+1).
Source: Stacks Tags 0941, 0H9K
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
abbrev retainedTower {A : Type a} [Category.{b} A] [Abelian A]
    (e : ℕ) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  CategoryTheory.StrictTowerArithmetic.index e ⋙ T

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The actual completed coefficient inclusion, with its residue-normalized pullback square.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def completedChange : Change (completed l E) (completed l F) where
  map := completedCoefficientMap l E F i
  square := completedChange_square l E F i

/-- The proper coefficient arrow: its scalar-adjunction mate is the canonical
K-injective restriction comparison. Equivalently its proper-adjunction transpose is
pullback/tensor balancing followed by scalar extension of the proper counit.
Source: Stacks Tags 07A6, 0B56
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def properComparison {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g) ⋙
        pbcDerivedExtend (a.map V) ⟶
      pbcDerivedExtend (a.map U) ⋙
        proEtaleRingDerivedDirectImage g (S.ring V) (S.ring U) (S.pull g) :=
  ((mateEquiv (pbcDerivedScalarAdjunction (a.map U))
    (pbcDerivedScalarAdjunction (a.map V))).symm
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDerivedDirectImage g
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv))

/-- The open coefficient arrow is the mate of the open-unit normalized restriction square.
Source: Stacks Tag 0E8I
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def openComparison {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    (openExtension R j).mapDerivedCategory ⋙ pbcDerivedExtend (a.map V) ⟶
      pbcDerivedExtend (a.map U) ⋙ (openExtension S j).mapDerivedCategory :=
  ((mateEquiv (pbcDerivedScalarAdjunction (a.map U))
    (pbcDerivedScalarAdjunction (a.map V))).symm
      (TwoSquare.mk _ _ _ _ (openRestriction a j).hom))

private theorem doubleInverseMate_isIso
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) :
    IsIso ((mateEquiv a b).symm
      ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))) := by
  have h := 
    (iterated_mateEquiv_conjugateEquiv_symm a b u x (TwoSquare.mk _ _ _ _ q.inv))
  rw [h]
  change IsIso ((conjugateEquiv (a.comp x) (u.comp b)).symm q.inv)
  infer_instance

/-- The canonical open coefficient arrow is an identification, without a flatness
hypothesis on the coefficient map.
Source: Stacks Tag 0E8I
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: the exact-localization mate theorem identifies the specified open restriction
square with the inverse mate of the canonical pullback/restriction isomorphism.
The scalar inverse mate defining openComparison is consequently a double inverse
mate. The iterated-mate identity identifies it with conjugation under the composite
scalar/open adjunctions. Conjugation preserves isomorphisms, as do evaluation functors. -/
theorem openComparison_isIso {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (M : DerivedCategory (pbcModules U (R.ring U))) :
    IsIso ((openComparison a j).app M) := by
  let φ := proEtaleRingRestrictionPullbackInv
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  have : IsIso φ := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  let q := (asIso φ).symm
  have : IsIso ((mateEquiv (openAdjunction S j) (openAdjunction R j)).symm
      (TwoSquare.mk _ _ _ _ q.hom)) := by
    change IsIso (openRestrictionMap a j)
    infer_instance
  have h := (exact_localization_inverse_mate
    (openAdjunction S j) (openAdjunction R j) q).2.1
  have h' : ((mateEquiv (openDerivedAdjunction S j) (openDerivedAdjunction R j)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso q).hom)) =
        (openRestriction a j).hom := h
  unfold openComparison
  rw [← h']
  have hi := doubleInverseMate_isIso
    (pbcDerivedScalarAdjunction (a.map U)) (pbcDerivedScalarAdjunction (a.map V))
    (openDerivedAdjunction S j) (openDerivedAdjunction R j)
    (Functor.mapDerivedCategorySquareIso q).symm
  exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hi M

/-- The ordered proper/open factorization holds before any inverse limit is taken.
It is applied below to each ramified finite quotient.
Source: Stacks Tags 07A6, 0E8I
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: expand the mate defining comparison. Naturality moves the open square across
the proper scalar unit, and the scalar triangle identities cancel the middle counit
and unit. The remaining composite is the proper mate followed by the proper image
of the open mate. These are equations of natural transformations. -/
theorem comparison_factorization {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (pbcModules X (R.ring X))) :
    (comparison a c).app K =
      (properComparison a c.g).app ((openExtension R c.i).mapDerivedCategory.obj K) ≫
        (proEtaleRingDerivedDirectImage c.g (S.ring Y) (S.ring c.Z) (S.pull c.g)).map
          ((openComparison a c.i).app K) := by
  let α := TwoSquare.mk _ _ _ _ (openRestriction a c.i).hom
  let β := TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionDerivedDirectImage c.g
      (R.ring Y) (S.ring Y) (R.ring c.Z) (S.ring c.Z)
      (a.map Y) (a.map c.Z) (R.pull c.g) (S.pull c.g) (a.square c.g)).inv
  let adjX := pbcDerivedScalarAdjunction (a.map X)
  let adjZ := pbcDerivedScalarAdjunction (a.map c.Z)
  let adjY := pbcDerivedScalarAdjunction (a.map Y)
  have hv : TwoSquare.vComp α β = (restriction a c).hom := by
    ext K
    simp only [TwoSquare.vComp, α, β, restriction, TwoSquare.mk,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id]
  have h := mateEquiv_vcomp adjX adjZ adjY
    ((mateEquiv adjX adjZ).symm α) ((mateEquiv adjZ adjY).symm β)
  simp only [Equiv.apply_symm_apply, hv] at h
  have h' := congrArg (fun t ↦ ((mateEquiv adjX adjY).symm t).app K) h
  simpa only [Equiv.symm_apply_apply, α, β, adjX, adjZ, adjY,
    comparison, image, properComparison, openComparison, TwoSquare.hComp, TwoSquare.mk,
    NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id] using h'.symm

attribute [local irreducible] properComparison openComparison

/-- The ramification hypothesis identifies ideals, and does not equate the chosen
uniformizers. Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def Ramification (e : ℕ) : Prop :=
  Ideal.map (integralScalarIntegerInclusion l E F i)
      (Padic.coefficientExtensionIdeal l E 1) =
    Padic.coefficientExtensionIdeal l F e

/-- A source uniformizer power is killed in the retained target quotient.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: map the source principal ideal through the integer inclusion and use the
ramification ideal equality. Taking nth powers gives the ideal generated by the
eth times nth target uniformizer power. Its image in the displayed quotient is zero. -/
theorem ramifiedKernel (e : ℕ) (he : Ramification l E F i e) (n : ℕ)
    (x : Padic.coefficientExtensionIntegers l E)
    (hx : x ∈ Padic.coefficientExtensionIdeal l E n) :
    Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (e * n))
      (integralScalarIntegerInclusion l E F i x) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hmap : Ideal.map (integralScalarIntegerInclusion l E F i)
      (Padic.coefficientExtensionIdeal l E n) =
        Padic.coefficientExtensionIdeal l F (e * n) := by
    have he' := he
    change Ideal.map (integralScalarIntegerInclusion l E F i)
      (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1) =
        Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ e at he'
    simp only [pow_one] at he'
    simp only [Padic.coefficientExtensionIdeal, Ideal.map_pow, he', pow_mul]
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ hx

/-- The actual retained quotient inclusion A_E,n to A_F,en.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def ramifiedMap (e : ℕ) (he : Ramification l E F i e) (n : ℕ) :
    Padic.coefficientExtensionRing l E n →+* Padic.coefficientExtensionRing l F (e * n) :=
  Ideal.Quotient.lift (Padic.coefficientExtensionIdeal l E n)
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (e * n))).comp
      (integralScalarIntegerInclusion l E F i))
    (ramifiedKernel l E F i e he n)

/-- The constant-sheaf map induced by the ramified quotient inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def ramifiedSheafMap (e : ℕ) (he : Ramification l E F i e) (n : ℕ)
    (W : Scheme.{u}) :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ramifiedMap l E F i e he n).ulift.{u + 1, u + 1})

/-- The quotient inclusion commutes with the actual constant-ring inverse-image maps.
Source: Stacks Tag 03CO
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: both maps carry a constant section represented by x to the constant section
represented by i(x). Inverse image and sheafification preserve that identity; constant
sections locally generate the constant sheaves, so the maps agree. -/
theorem finiteChange_square (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) (hn : 1 ≤ n) {U V : Scheme.{u}} (g : U ⟶ V) :
    ((finite l E n hn).pull g).hom ≫ ramifiedSheafMap l E F i e he n U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (ramifiedSheafMap l E F i e he n V) ≫
          ((finite l F (e * n) (Nat.mul_pos hepos hn)).pull g).hom := by
  exact (proEtaleConstantInverseImageMap_naturality g
    (CommRingCat.ofHom (ramifiedMap l E F i e he n).ulift.{u + 1, u + 1})).symm

/-- The specified finite coefficient change for the retained levels.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteChange (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) (hn : 1 ≤ n) :
    Change (finite l E n hn) (finite l F (e * n) (Nat.mul_pos hepos hn)) where
  map := ramifiedSheafMap l E F i e he n
  square := finiteChange_square l E F i e he hepos n hn

/-- Completed projections commute with the actual inverse-image identifications.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: under the inverse-image adjunction both maps are the same finite projection
of the canonical completed structure map. The finite projection normalization of
completedPullMap identifies them. -/
theorem projection_square (n : ℕ) (hn : 1 ≤ n)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ((completed l E).pull g).hom ≫ projection l E n hn U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (projection l E n hn V) ≫
        ((finite l E n hn).pull g).hom := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ n =>
    let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
    change (adj.homEquiv _ _).symm (sfCompletedCoefficientMap l E g) ≫
        completedIntegralCommRingProjectionUnrestricted l E U n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (completedIntegralCommRingProjectionUnrestricted l E V n) ≫
        (adj.homEquiv _ _).symm
          (proEtaleCoefficientDirectImageMap g (Padic.coefficientExtensionRing l E (n + 1)))
    rw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_left_symm]
    exact congrArg (adj.homEquiv _ _).symm
      ((sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec n)

/-- Reduction means ordinary derived tensor along the specified limit projection.
Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def reduction (n : ℕ) (hn : 1 ≤ n) : Change (completed l E) (finite l E n hn) where
  map := projection l E n hn
  square := projection_square l E n hn

private theorem quotientSheafFactor (m n k : ℕ) (hn : n ≤ m) (h : k = m + 1)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l F k)
    (hφ : ∀ x : Padic.coefficientExtensionIntegers l E,
      φ (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F k)
          (integralScalarIntegerInclusion l E F i x)) (W : Scheme.{u}) :
    integralScalarQuotientSheafMap l E F i W m =
      compactSupportLevelSheafQuotient l E W m n hn ≫
        (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom φ.ulift.{u + 1, u + 1}) ≫
        eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
          (Padic.coefficientExtensionRing l F k)) h) := by
  subst k
  simp only [eqToHom_refl, Category.comp_id, integralScalarQuotientSheafMap,
    compactSupportLevelSheafQuotient]
  rw [← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  rintro ⟨x⟩
  apply ULift.ext
  induction x using Quotient.inductionOn' with
  | h x => exact (hφ x).symm

/-- The completed inclusion reduces to the specified retained quotient inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: evaluate the two maps on constant integral sections. Both take x to i(x)
modulo the eth times nth target uniformizer power. The quotient lift and the completed
map are normalized by precisely these sections, so the maps agree. -/
theorem ramified_reduction_square (e : ℕ) (he : Ramification l E F i e)
    (hepos : 1 ≤ e) (n : ℕ) (hn : 1 ≤ n) (W : Scheme.{u}) :
    (completedChange l E F i).map W ≫ projection l F (e * n) (Nat.mul_pos hepos hn) W =
      projection l E n hn W ≫ (finiteChange l E F i e he hepos n hn).map W := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ n =>
    have hm : 1 ≤ e * (n + 1) := Nat.mul_pos hepos (Nat.le_add_left 1 n)
    have hmn : n ≤ e * (n + 1) - 1 := by
      have h : n + 1 ≤ e * (n + 1) := by
        calc
          n + 1 = 1 * (n + 1) := (one_mul _).symm
          _ ≤ e * (n + 1) := Nat.mul_le_mul_right _ hepos
      omega
    have hq : integralScalarQuotientSheafMap l E F i W (e * (n + 1) - 1) =
        compactSupportLevelSheafQuotient l E W (e * (n + 1) - 1) n hmn ≫
          ramifiedSheafMap l E F i e he (n + 1) W ≫
          eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
            (Padic.coefficientExtensionRing l F k)) (Nat.sub_add_cancel hm).symm) := by
      exact quotientSheafFactor l E F i _ n _ hmn (Nat.sub_add_cancel hm).symm
        (ramifiedMap l E F i e he (n + 1)) (fun _ ↦ rfl) W
    change completedCoefficientMap l E F i W ≫
        (completedIntegralCommRingProjectionUnrestricted l F W (e * (n + 1) - 1) ≫ _) = _
    have hp : completedCoefficientMap l E F i W ≫
        completedIntegralCommRingProjectionUnrestricted l F W (e * (n + 1) - 1) =
        completedIntegralCommRingProjectionUnrestricted l E W (e * (n + 1) - 1) ≫
          integralScalarQuotientSheafMap l E F i W (e * (n + 1) - 1) :=
      (completedCoefficientMap_existsUnique l E F i W).exists.choose_spec _
    let q : proEtaleConstantRing W (Padic.coefficientExtensionRing l F (e * (n + 1))) ≅
        integralCoefficientCommRingSheaf l F W (e * (n + 1) - 1) :=
      eqToIso (congrArg (fun k ↦ proEtaleConstantRing W
        (Padic.coefficientExtensionRing l F k)) (Nat.sub_add_cancel hm).symm)
    let pE := completedIntegralCommRingProjectionUnrestricted l E W (e * (n + 1) - 1)
    let pF := completedIntegralCommRingProjectionUnrestricted l F W (e * (n + 1) - 1)
    let r := compactSupportLevelSheafQuotient l E W (e * (n + 1) - 1) n hmn
    let φ := ramifiedSheafMap l E F i e he (n + 1) W
    change completedCoefficientMap l E F i W ≫ (pF ≫ q.inv) =
      completedIntegralCommRingProjectionUnrestricted l E W n ≫ φ
    calc
      _ = (completedCoefficientMap l E F i W ≫ pF) ≫ q.inv :=
        (Category.assoc _ _ _).symm
      _ = (pE ≫ integralScalarQuotientSheafMap l E F i W (e * (n + 1) - 1)) ≫
          q.inv := congrArg (fun v : completedIntegralCommRingSheafUnrestricted l E W ⟶
            integralCoefficientCommRingSheaf l F W (e * (n + 1) - 1) ↦ v ≫ q.inv) hp
      _ = (pE ≫ (r ≫ φ ≫ q.hom)) ≫ q.inv :=
        congrArg (fun v : integralCoefficientCommRingSheaf l E W
            (e * (n + 1) - 1) ⟶ integralCoefficientCommRingSheaf l F W
            (e * (n + 1) - 1) ↦ (pE ≫ v) ≫ q.inv) hq
      _ = (pE ≫ r) ≫ φ := by
        simp only [Category.assoc, q.hom_inv_id, Category.comp_id]
      _ = _ := congrArg (fun v : completedIntegralCommRingSheafUnrestricted l E W ⟶
          integralCoefficientCommRingSheaf l E W n ↦ v ≫ φ)
        (compactSupportProjection_comp l E W (e * (n + 1) - 1) n hmn)

/-- Tensor balancing for a commutative coefficient square, with ordinary associators.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def tensorSquare {W : Scheme.{u}}
    {R S A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : A ⟶ B) (r : R ⟶ A) (s : S ⟶ B) (h : a ≫ s = r ≫ b) :
    pbcDerivedExtend a ⋙ pbcDerivedExtend s ≅ pbcDerivedExtend r ⋙ pbcDerivedExtend b :=
  tensorComposition a s (a ≫ s) rfl ≪≫ (tensorComposition r b (a ≫ s) h.symm).symm

/-- Source of the specified finite coefficient comparison, at the positive exponent n+1.
Source: blueprint theorem-smooth-purity-all-admissible-coefficients Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteTensorSource (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) :=
  (pbcDerivedExtend ((finiteChange l E F i e he hepos (n + 1)
    (Nat.le_add_left 1 n)).map Y)).obj
      ((image (finite l E (n + 1) (Nat.le_add_left 1 n)) c).obj
        ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M))

/-- Target of the same finite comparison, before any total inverse limit.
Source: blueprint theorem-smooth-purity-all-admissible-coefficients Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteTensorTarget (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) :=
  (image (finite l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n))) c).obj
    ((pbcDerivedExtend ((finiteChange l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n)).map X)).obj
        ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M))

/-- The finite map itself is the ordered proper mate followed by proper image of the
open coefficient identification. This definition contains both arrows explicitly.
Source: Stacks Tags 07A6, 0B56, 0E8I; blueprint theorem-smooth-purity-all-admissible-coefficients
Step 3 (blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteTensorMap (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    finiteTensorSource l E F i e he hepos n c M ⟶
      finiteTensorTarget l E F i e he hepos n c M :=
  (properComparison (finiteChange l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n)) c.g).app
      ((openExtension (finite l E (n + 1) (Nat.le_add_left 1 n)) c.i).mapDerivedCategory.obj
        ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M)) ≫
    (proEtaleRingDerivedDirectImage c.g
      ((finite l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n))).ring Y)
      ((finite l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n))).ring c.Z)
      ((finite l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n))).pull c.g)).map
      ((openComparison (finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)) c.i).app
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M))

/-- The identified constant-coefficient pushforward has exactly the canonical
constant-section structural map. Equality is of the actual module functors.
Source: Stacks Tags 03DA and 03D6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: transpose the constant inverse-image map under the sheaf adjunction. Its
transpose is the constant direct-image map by the triangle identity. Both module
functors are SheafOfModules.pushforward with this same structure map and base-change
functor; congruence gives the displayed equality, on objects and on maps. -/
theorem finiteDirectImage_eq (n : ℕ) {U V : Scheme.{u}} (g : U ⟶ V) :
    proEtaleRingModuleDirectImage g
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring V)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring U)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull g) =
      proEtaleConstantModuleDirectImage g (Padic.coefficientExtensionRing l E (n + 1)) := by
  have h : proEtaleRingDirectImageMap g
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring V)
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring U)
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull g) =
      proEtaleCoefficientDirectImageMap g (Padic.coefficientExtensionRing l E (n + 1)) := by
    exact ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  unfold proEtaleRingModuleDirectImage proEtaleConstantModuleDirectImage
  rw [h]

/-- The canonical pullback presentation comparison, preserving its constant-section
adjunction. Source: Stacks Tags 03D3 and 03D6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finitePullbackIso (n : ℕ) {U V : Scheme.{u}} (g : U ⟶ V) :=
  ((proEtaleRingModuleAdjunction g
    ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring V)
    ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring U)
    ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull g)).ofNatIsoRight
      (eqToIso (finiteDirectImage_eq l E n g))).leftAdjointUniq
        (sfIntrinsicConstantModuleAdjunction g (Padic.coefficientExtensionRing l E (n + 1)))

/-- The canonical open presentation comparison, determined by the actual open units.
Source: Stacks Tag 03DI
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteOpenIso (n : ℕ) {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
  ((openAdjunction (finite l E (n + 1) (Nat.le_add_left 1 n)) j).ofNatIsoRight
    (finitePullbackIso l E n j)).leftAdjointUniq
      (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)

/-- The finite proper/open realization isomorphism, preserving the open unit and
separately derived proper-image unit. Source: Stacks Tags 03DI and 0D6E
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteImageIso (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    image (finite l E (n + 1) (Nat.le_add_left 1 n)) c ≅
      sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c :=
  letI := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).1
  letI := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  letI := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  letI := (proEtaleConstantModuleDirectImage_additive_leftExact c.g
    (Padic.coefficientExtensionRing l E (n + 1))).1
  Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso (finiteOpenIso l E n c.i)) _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorNatIso (eqToIso (finiteDirectImage_eq l E n c.g)))

attribute [local irreducible] finiteImageIso

/-- The two derived quotient tensors are identified by their tensor-unit normalized
adjunctions to exactly the same scalar restriction, including positive-index transport.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteReductionIso (W : Scheme.{u}) (n : ℕ) :
    pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) W) ≅
      scalarReductionDerivedExtension l E W n :=
  (pbcDerivedScalarAdjunction (projection l E (n + 1) (Nat.le_add_left 1 n) W)).leftAdjointUniq
    (derivedScalarExtensionRestrictionAdjunction l E W n).choose

attribute [local irreducible] finiteReductionIso

/-- The actual quotient between arbitrary positive exponents, using the recorded
strict-tower quotient and only reindexing its positive-level convention.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteQuotient (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m)
    (W : Scheme.{u}) : (finite l E m hm).ring W ⟶ (finite l E n hn).ring W :=
  eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
    (Padic.coefficientExtensionRing l E k)) (Nat.sub_add_cancel hm).symm) ≫
  compactSupportLevelSheafQuotient l E W (m - 1) (n - 1) (Nat.sub_le_sub_right h 1) ≫
  eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
    (Padic.coefficientExtensionRing l E k)) (Nat.sub_add_cancel hn))

private theorem finiteQuotient_eq_map (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : n ≤ m) (W : Scheme.{u}) :
    finiteQuotient l E m n hm hn h W =
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom
          (show Padic.coefficientExtensionRing l E m →+*
              Padic.coefficientExtensionRing l E n from
            Ideal.Quotient.factor (Ideal.pow_le_pow_right h)).ulift.{u + 1, u + 1}) := by
  cases m with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hm)
  | succ m =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
    | succ n => rfl

/-- Finite quotient maps commute with inverse-image identifications.
Source: Stacks Tag 03CO
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: both composites take each locally constant section represented by an integer
x to its residue at exponent n. These sections locally generate the constant ring
sheaf, and inverse image and sheafification preserve this equality. -/
theorem finiteQuotient_square (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ((finite l E m hm).pull g).hom ≫ finiteQuotient l E m n hm hn h U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (finiteQuotient l E m n hm hn h V) ≫ ((finite l E n hn).pull g).hom := by
  rw [finiteQuotient_eq_map, finiteQuotient_eq_map]
  exact (proEtaleConstantInverseImageMap_naturality g _).symm

/-- The coefficient change for a further quotient, with its canonical section map.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteQuotientChange (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m) :
    Change (finite l E m hm) (finite l E n hn) where
  map := finiteQuotient l E m n hm hn h
  square := finiteQuotient_square l E m n hm hn h

/-- The coefficient prime is a unit in the geometric base field.
Source: blueprint def-pur-conventions
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: the finite field k0 has characteristic p because its cardinality is p^a,
and its algebraic closure has the same characteristic. A prime l different from p
therefore has nonzero image in the field k, hence is a unit. -/
theorem coefficientPrimeUnit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  let : Fintype D.k₀ := Fintype.ofFinite _
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : l.Prime) hl.symm)

section CompletedScalarProof

private theorem completedSupportMate_of_finiteFree {R S : Coefficients.{u}}
    (a : Change R S) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (d : ℕ)
    (hfree : Nonempty
      ((pbcRestrict (a.map Y)).obj
          (SheafOfModules.unit ((adicLisseForget Y).obj (S.ring Y))) ≅
        ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget Y).obj (R.ring Y))))
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    IsIso ((comparison a c).app M) := by
  have : IsIso (properComparison a c.g) := by
    unfold properComparison
    exact finiteFreeRestrictionDirectImageMate_isIso a c.g d hfree
  have := openComparison_isIso a c.i M
  rw [comparison_factorization]
  infer_instance

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local semireducible] reductionDerivedChange completedAdicDerivedChange

/-- On the asserted finite-Tor domain the canonical integral coefficient comparison
is invertible, and its actual source and target are constructible complete objects.
The map is ordinary derived tensor, defined above by the normalized scalar adjunction.
The last clause identifies the ambient proper/open realization with the recorded
integral compact-support value, without selecting a new arbitrary limit vertex.
Source: blueprint theorem-smooth-purity-all-admissible-coefficients, Step 3; Bhatt--Scholze,
Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).

Proof: ordinary completed scalar extension preserves integral constructibility and
one uniform finite Tor interval by the finite-free scalar comparison and the finite
quotient scalar Tor theorem. The lower finite-free direct-image column calculation,
transported between scalar adjunctions by conjugation, makes the specified proper
mate invertible. The existing open mate is invertible, and comparison factorization
therefore proves invertibility of their ordered composite. For each coefficient field
the ambient proper/open object is a derived limit of the finite support tower.
The existing derived-limit constructibility theorem makes both output objects
constructible. Finally the recorded integral compact-support object is another
vertex of the same derived-limit triangle, so derived-limit uniqueness up to
isomorphism gives the final existence clause. The remaining declarations below
separately assert the stronger projection and coherence normalizations. -/
theorem integralCoefficientComparison
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    finiteTorConstructibleIntegral l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) ∧
      sfIntegralConstructible l E Y ((image (completed l E) c).obj M) ∧
      sfIntegralConstructible l F Y
        ((image (completed l F) c).obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ∧
      IsIso ((comparison (completedChange l E F i) c).app M) ∧
      Nonempty ((image (completed l E) c).obj M ≅
        (sfIntegralCompactSupportValue l E D.k
          (coefficientPrimeUnit l D hl) c ⟨M, hM.1⟩).obj) := by
  have hF := finiteTorIntegralCompletedScalarExtension D.p l hl E F i X M hM
  let hunit := coefficientPrimeUnit l D hl
  letI : HasCountableProducts (DerivedCategory (scalarReductionSource l E Y)) :=
    integralOperationsDerivedCountableProducts l E Y
  letI : HasCountableProducts (DerivedCategory (scalarReductionSource l F Y)) :=
    integralOperationsDerivedCountableProducts l F Y
  have hlimE := integralProperOpen_isDerivedLimit l E D hunit f c M hM
  have hlimF := integralProperOpen_isDerivedLimit l F D hunit f c _ hF
  have hEout := sfIntegralCompactSupport_constructible l E c D.k hunit
    M hM.1 _ hlimE
  have hFout := sfIntegralCompactSupport_constructible l F c D.k hunit
    _ hF.1 _ hlimF
  have hreal : Nonempty ((image (completed l E) c).obj M ≅
      (sfIntegralCompactSupportValue l E D.k hunit c ⟨M, hM.1⟩).obj) := by
    let h := (exists_isDerivedLimit_and_iso
      (fun n : ℕ ↦ sfCompactSupportTerm l E c M n)
      (fun n : ℕ ↦ sfCompactSupportTransition l E c M n)).1
    exact (exists_isDerivedLimit_and_iso
      (fun n : ℕ ↦ sfCompactSupportTerm l E c M n)
      (fun n : ℕ ↦ sfCompactSupportTransition l E c M n)).2 _ _
        hlimE (Classical.choose_spec h)
  refine ⟨hF, hEout, hFout, ?_, hreal⟩
  exact completedSupportMate_of_finiteFree (completedChange l E F i) c
    (completedScalarRelativeDegree l E F i)
    (finiteFreeCompletedScalarComparison l E F i Y).1 M

end CompletedScalarProof

/-- Completed coefficient multiplication is identity for the identity field inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: every finite projection of the displayed map is the same projection, because
the quotient ring map induced by the identity is identity. Joint monicity proves equality. -/
theorem completedMap_identity (W : Scheme.{u}) :
    completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W = 𝟙 _ := by
  apply (completedCoefficientMap_existsUnique l E E (AlgHom.id ℚ_[l] E) W).unique
    (completedCoefficientMap_existsUnique l E E (AlgHom.id ℚ_[l] E) W).exists.choose_spec
  intro n
  have hq : integralScalarQuotientMap l E E (AlgHom.id ℚ_[l] E) n = RingHom.id _ := by
    ext x
    rfl
  have hs : integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) W n = 𝟙 _ := by
    unfold integralScalarQuotientSheafMap
    rw [hq]
    convert (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) using 1 <;> rfl
  simp only [hs, Category.id_comp, Category.comp_id]

/-- Field towers give the actual composite completed inclusion, not a chosen comparison.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: after each target projection, successive quotient inclusions and direct
inclusion both send the class of x to the class of j(i(x)). The defining residue
normalization and joint monicity of projections prove equality. -/
theorem completedMap_composition (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (j : F →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :
    completedCoefficientMap l E F i W ≫ completedCoefficientMap l F L j W =
      completedCoefficientMap l E L (j.comp i) W := by
  apply (completedCoefficientMap_existsUnique l E L (j.comp i) W).unique
  · intro n
    have hj : completedCoefficientMap l F L j W ≫
        completedIntegralCommRingProjectionUnrestricted l L W n = _ :=
      (completedCoefficientMap_existsUnique l F L j W).exists.choose_spec n
    have hi : completedCoefficientMap l E F i W ≫
        completedIntegralCommRingProjectionUnrestricted l F W n = _ :=
      (completedCoefficientMap_existsUnique l E F i W).exists.choose_spec n
    rw [Category.assoc,
      hj,
      ← Category.assoc,
      hi,
      Category.assoc]
    congr 1
    have hq : (integralScalarQuotientMap l F L j n).comp
        (integralScalarQuotientMap l E F i n) =
        integralScalarQuotientMap l E L (j.comp i) n := by
      apply RingHom.ext
      intro x
      induction x using Quotient.inductionOn' with
      | h x => rfl
    unfold integralScalarQuotientSheafMap
    rw [← Functor.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact congrArg ULift.up (RingHom.congr_fun hq x.down)
  · exact (completedCoefficientMap_existsUnique l E L (j.comp i) W).exists.choose_spec

attribute [local irreducible] ordinaryIntegralModulePull ordinaryIntegralModuleAdjunction
  ordinaryIntegralDirectRingMap
  proEtaleRingModulePullback proEtaleRingModuleAdjunction
  HasProEtaleTorAmplitude

section Refinements

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))] [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- Inclusion of the actual uniform finite-Tor domain into the recorded integral category.
Source: blueprint definition 1464
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
-/
def finiteTorIntegralInclusion (W : Scheme.{u}) :
    finiteTorConstructibleIntegralCategory l E W ⥤ sfIntegralConstructibleCategory l E W where
  obj M := ⟨M.obj, M.property.1⟩
  map v := ObjectProperty.homMk v.hom

end Refinements

end WeilConjectures.PurCompactSupport
