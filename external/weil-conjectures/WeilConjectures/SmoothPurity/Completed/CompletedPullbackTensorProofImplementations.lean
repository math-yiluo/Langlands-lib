/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.StrictQuotient.StrictScalarPullbackComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleEnoughPoints
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.Sites.FinitarySliceEnoughPoints
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.FinitarySiteEnoughPoints
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import WeilConjectures.CategoryTheory.Sites.PointSystemSaturation
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.PointSystemRefineAll
import WeilConjectures.CategoryTheory.PointSystemRefinementMap
import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.AlgebraicGeometry.PointSystemRefine
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.PointSystemRefinementChainExists
import WeilConjectures.CategoryTheory.PointSystemChain
import Mathlib.Order.Directed
import WeilConjectures.CategoryTheory.PointSystemExtensions
import WeilConjectures.CategoryTheory.PointSystemDiagram
import Mathlib.Order.Category.PartOrdEmb
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Order.Hom.Set
import WeilConjectures.CategoryTheory.PointSystemPosetalRefine
import WeilConjectures.CategoryTheory.PointSystemPosetalReplacement
import Mathlib.Order.Antisymmetrization
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.PointSystemSchedule
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.CategoryTheory.Filtered.Grothendieck
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Sites.PointFamilyConservative
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import WeilConjectures.TraceFormula.InverseSystemSitePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat
import WeilConjectures.Algebra.Homology.RingedSiteKFlatStalkCriterion
import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Homology.RingedSitePointUniversalTensor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.Algebra.Homology.RingedSitePointTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.PUnit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Homology.RingedSitePointExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Homology.RingedSitePointFinitePresentationRetract
import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.Sites.InverseImageFreeModule
import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import WeilConjectures.CategoryTheory.Sites.NormalizedFreeModuleComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Finsupp.Pi
import WeilConjectures.Algebra.Homology.RingedSitePointKFlatResolution
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.RingedSitePointAcyclic
import WeilConjectures.Algebra.Homology.UniversalAcyclicModuleKFlat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.ModuleDirectedColimitFinitePresentation
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-! # Private implementations for the completed pullback tensor comparison

These proved helpers retain the exact composite-localization, ordinary quotient-unit,
and K-flat pullback arguments of `CompletedPullbackTensorComparison`. Keeping their
implementations separate reduces repeated elaboration in that large module.
Source: Stacks Tags 05RR, 06YY, 07A4 and 03D2.
(blueprint: def-pur-completed-pullback-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory

private theorem completedPullbackLocalizationIso_existsUnique
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (F G : C ⥤ E) (F' G' : D ⥤ E)
    (a : L ⋙ F' ≅ F) (b : L ⋙ G' ≅ G) (c : F ≅ G) :
    ∃! e : F' ≅ G', ∀ P : C,
      e.hom.app (L.obj P) ≫ b.hom.app P = a.hom.app P ≫ c.hom.app P := by
  let : Localization.Lifting L W F F' := ⟨a⟩
  let : Localization.Lifting L W G G' := ⟨b⟩
  let e := Localization.liftNatIso L W F G F' G' c
  have he (P : C) :
      e.hom.app (L.obj P) ≫ b.hom.app P = a.hom.app P ≫ c.hom.app P := by
    dsimp only [e, Localization.liftNatIso_hom]
    rw [Localization.liftNatTrans_app]
    change (a.hom.app P ≫ c.hom.app P ≫ b.inv.app P) ≫ b.hom.app P = _
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext L W
  intro P
  apply (cancel_mono (b.hom.app P)).1
  exact (he' P).trans (he P).symm

/-- Descend an exact cochain composite comparison, with its factorization square.
Source: Stacks Tag 05RR, exact-functor localization
(blueprint: lem-pur-completed-pullback-exact-composite).
Proof: whisker the exact-functor factorization isomorphisms to obtain the two
factorizations through the cochain localization Q. Compose the ordinary cochain
comparison with the cochain image of the final functor isomorphism. Localization
lifts this comparison to the derived composites; its component formula is the
required square after functoriality and reassociation. Any other comparison
with that square agrees after precomposing by Q, hence agrees by localization
extensionality. Cancellation of the factorization isomorphisms proves uniqueness. -/
theorem completedPullbackDerivedCompositeIso_existsUnique
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    (A : C₁ ⥤ C₂) (B : C₂ ⥤ D₂) (C : C₁ ⥤ D₁) (D D₀ : D₁ ⥤ D₂)
    [A.Additive] [B.Additive] [C.Additive] [D.Additive] [D₀.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits C] [PreservesFiniteColimits C]
    [PreservesFiniteLimits D] [PreservesFiniteColimits D]
    (c₁ : A.mapHomologicalComplex (.up ℤ) ⋙ B.mapHomologicalComplex (.up ℤ) ≅
      C.mapHomologicalComplex (.up ℤ) ⋙ D₀.mapHomologicalComplex (.up ℤ)) (c₂ : D₀ ≅ D) :
    ∃! e : A.mapDerivedCategory ⋙ B.mapDerivedCategory ≅
      C.mapDerivedCategory ⋙ D.mapDerivedCategory,
      ∀ P : CochainComplex C₁ ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            D.mapDerivedCategory.map (C.mapDerivedCategoryFactors.hom.app P) ≫
            D.mapDerivedCategoryFactors.hom.app
              ((C.mapHomologicalComplex (.up ℤ)).obj P) =
          B.mapDerivedCategory.map (A.mapDerivedCategoryFactors.hom.app P) ≫
            B.mapDerivedCategoryFactors.hom.app
              ((A.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map (c₁.hom.app P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c₂ (.up ℤ)).hom.app
              ((C.mapHomologicalComplex (.up ℤ)).obj P)) := by
  let c := c₁ ≪≫ Functor.isoWhiskerLeft (C.mapHomologicalComplex (.up ℤ))
    (NatIso.mapHomologicalComplex c₂ (.up ℤ))
  let a : DerivedCategory.Q ⋙ A.mapDerivedCategory ⋙ B.mapDerivedCategory ≅
      A.mapHomologicalComplex (.up ℤ) ⋙ B.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight A.mapDerivedCategoryFactors B.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ B.mapDerivedCategoryFactors
  let b : DerivedCategory.Q ⋙ C.mapDerivedCategory ⋙ D.mapDerivedCategory ≅
      C.mapHomologicalComplex (.up ℤ) ⋙ D.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight C.mapDerivedCategoryFactors D.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ D.mapDerivedCategoryFactors
  have h := completedPullbackLocalizationIso_existsUnique DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (.up ℤ))
    (A.mapHomologicalComplex (.up ℤ) ⋙ B.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (C.mapHomologicalComplex (.up ℤ) ⋙ D.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (A.mapDerivedCategory ⋙ B.mapDerivedCategory)
    (C.mapDerivedCategory ⋙ D.mapDerivedCategory) a b
    (Functor.isoWhiskerRight c DerivedCategory.Q)
  dsimp only [a, b, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.comp_obj, Functor.comp_map] at h
  simpa only [c, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc] using h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] sfIntrinsicPullback_additive
attribute [local instance] coefficientFiniteQuotientExtensionAdditive

private theorem completedPullbackTensorQuotientOrdinary {X Y : Scheme.{u}}
    (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :
    ∃! e : sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f ⋙
        coefficientFiniteQuotientExtension l E X h ≅
      coefficientFiniteQuotientExtension l E Y h ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f,
      ∀ (M : normalizedDVRModules l E Y m) (U : Y.ProEt)
        (x : M.val.obj (Opposite.op U)),
        (e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (coefficientFiniteQuotientUnitSection l E X h
            ((sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f).obj M)
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((sfIntrinsicConstantModuleAdjunction f
              (finiteCoefficientRing l E (m + 1))).unit.app M).val.app (Opposite.op U) x)) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app
            ((coefficientFiniteQuotientExtension l E Y h).obj M)).val.app (Opposite.op U)
          (coefficientFiniteQuotientUnitSection l E Y h M (Opposite.op U) x) := by
  let : (proEtaleBaseChange f).IsContinuous
      (AmbientPullbackTensor.topology Y (some m))
      (AmbientPullbackTensor.topology X (some m)) :=
    AmbientPullbackTensor.baseContinuous f (some m)
  let am := sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (m + 1))
  let an := sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))
  let qX := (pullbackTensorCalculus l E X).quotientCalculus
  let qY := (pullbackTensorCalculus l E Y).quotientCalculus
  let c := StrictQuotient.push_restrict_iso (proEtaleBaseChange f)
    (AmbientPullbackTensor.moduleRingUnit l E f (some m))
    (AmbientPullbackTensor.moduleRingUnit l E f (some n))
    (normalizedDVRQuotient l E Y h) (normalizedDVRQuotient l E X h)
    (StrictQuotient.ringSquare l E f h)
  let a := am.comp (qX.ordinaryAdjunction h)
  let b := ((qY.ordinaryAdjunction h).comp an).ofNatIsoRight c.symm
  let e := a.leftAdjointUniq b
  refine ⟨e, ?_, ?_⟩
  · intro M U x
    exact StrictQuotient.scalar_comparison_unit (proEtaleBaseChange f)
      (AmbientPullbackTensor.moduleRingUnit l E f (some m))
      (AmbientPullbackTensor.moduleRingUnit l E f (some n))
      (normalizedDVRQuotient l E Y h) (normalizedDVRQuotient l E X h)
      (StrictQuotient.ringSquare l E f h)
      (sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f)
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
      (coefficientFiniteQuotientExtension l E Y h)
      (coefficientFiniteQuotientExtension l E X h)
      am an (qY.ordinaryAdjunction h) (qX.ordinaryAdjunction h)
      (coefficientFiniteQuotientUnitSection l E Y h)
      (coefficientFiniteQuotientUnitSection l E X h)
      (qY.ordinary_unit h) (qX.ordinary_unit h) M (Opposite.op U) x
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (a.homEquiv M _).injective
    have hh : a.homEquiv M _ (e'.hom.app M) = b.unit.app M := by
      rw [Adjunction.homEquiv_unit]
      ext U x
      change (e'.hom.app M).val.app ((proEtaleBaseChange f).op.obj U)
        (coefficientRestrictionSection (normalizedDVRQuotient l E X h) _ _
          (((qX.ordinaryAdjunction h).unit.app _).val.app _
            ((am.unit.app M).val.app U x))) =
        (an.unit.app ((coefficientFiniteQuotientExtension l E Y h).obj M)).val.app U
          (coefficientRestrictionSection (normalizedDVRQuotient l E Y h) _ _
            (((qY.ordinaryAdjunction h).unit.app M).val.app U x))
      erw [qX.ordinary_unit h, qY.ordinary_unit h]
      exact he' M U.unop x
    exact hh.trans (Adjunction.homEquiv_leftAdjointUniq_hom_app a b M).symm

private theorem completedPullbackTensorFiniteGood {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y n) P) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      (((sfIntrinsicPullback
        (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let A := finiteCoefficientRing l E (n + 1)
  let R := integralCoefficientCommRingSheaf l E Y n
  let S := integralCoefficientCommRingSheaf l E X n
  let RI := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  let c : RI ≅ S := proEtaleConstantRingComparison f A
  let geom : GeometricMorphism
      (Sheaf (ProEt.topology X) (Type (u + 1)))
      (Sheaf (ProEt.topology Y) (Type (u + 1))) :=
    { inverse := proEtaleSheafInverseImage f (Type (u + 1))
      direct := proEtaleSheafDirectImage f (Type (u + 1))
      adj := proEtaleSheafAdjunction f (Type (u + 1))
      leftExact := (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1 }
  let I := SheafOfModules.inverseImageOfUniverses (normalizedAlgebraicLift f R)
  let : Limits.PreservesFiniteLimits (proEtaleModuleInverseImage f R) :=
    proEtaleModuleInverseImage_preservesFiniteLimits f R
  have : (proEtaleModuleInverseImage f R).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : I.modules.Additive := inferInstanceAs (proEtaleModuleInverseImage f R).Additive
  obtain ⟨ι, p, hp⟩ := proEtale_enoughPoints.{u, u} X
  let s : ∀ i, RingedSitePoint RI (p i) :=
    fun i ↦ Classical.choice (RingedSitePoint.nonempty _ (p i))
  have hcons : JointlyReflectIsomorphisms (fun i ↦ (p i).inverse) := by
    constructor
    intro M N a _
    exact hp a (fun i ↦ (isIso_iff_bijective ((p i).inverse.map a)).1 inferInstance)
  have hI := SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points
    (ProEt.topology Y) (ProEt.topology X) geom I ι p s hcons P hP
  let F := proEtaleRingExtension f R S c
  let : Limits.PreservesFiniteLimits F := proEtaleRingExtension_preservesFiniteLimits f R S c
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have hF := SheafOfModules.changeOfRings_isKFlat_independentCoefficients c.hom
    ((I.modules.mapHomologicalComplex (.up ℤ)).obj P) F
    (fun _ ↦ rfl) (fun g ↦ by
      change F.map g = 𝟙 _ ≫ SheafOfModules.changeOfRingsHom c.hom _ g ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      rfl) hI
  let e := NatIso.mapHomologicalComplex (openSquarePullbackModel A f) (.up ℤ)
  let B := S
  let := SheafOfModules.isMonoidal_W_independentCoefficients B
  let := SheafOfModules.monoidalCategory B
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients B
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients B
  intro Q hQ i
  exact (hF Q hQ i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj Q).mapIso (e.app P))

end WeilConjectures
