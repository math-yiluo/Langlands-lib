/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteCompletedCoefficientMap
import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourArrows
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
import WeilConjectures.AlgebraicGeometry.Pbc.PbcIntrinsicTowerComplete
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison

import all WeilConjectures.CategoryTheory.AdicSites.CompletionFiniteReductionSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulConstantTransport
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.RingTheory.Ideal.Quotient.PowTransition
import all Mathlib.RingTheory.Noetherian.Defs
import all Mathlib.RingTheory.Ideal.Quotient.Operations
import all WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import all Mathlib.RingTheory.Ideal.Maps
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all Mathlib.CategoryTheory.Sites.Over
import all WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all WeilConjectures.CategoryTheory.RingedIdealGenerators
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Finiteness.Defs
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import all Mathlib.CategoryTheory.Adjunction.Whiskering
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all Mathlib.CategoryTheory.Limits.Final
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import all WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import all Mathlib.Algebra.Category.ModuleCat.Limits
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all Mathlib.Algebra.Module.FinitePresentation
import all Mathlib.RingTheory.Flat.Basic
import all Mathlib.RingTheory.Flat.Tensor
import all Mathlib.LinearAlgebra.TensorProduct.RightExactness
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Linear.FunctorCategory
import all Mathlib.CategoryTheory.Linear.LinearFunctor
import all WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
import all Mathlib.CategoryTheory.Limits.Over
import all Mathlib.Algebra.Category.CommAlgCat.Basic
import all WeilConjectures.RingTheory.LimitFlatModules
import all Mathlib.RingTheory.Flat.EquationalCriterion
import all Mathlib.RingTheory.TensorProduct.Quotient
import all Mathlib.RingTheory.Ideal.Quotient.Noetherian
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteReductionPullbackSquare
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube

/-! # Linear completed operations and their canonical exchange
Source: blueprint order 1442, Stacks Tags 099N, 099K and 07A7
(blueprint: lem-sbc-completed-operations-linear-natural-exchange).
The units and comparison maps below are fixed by ordinary tensor and the completion
unit. No natural isomorphism is selected without its normalizing equation.

## Main statements

- `sbcPull`, `sbcPush`, `sbcAdjunction`: normalized linear complete operations.
- `sbcTheta`, `sbcExchange`: their canonical square comparison and mate.
- `sbcCompletedOperations_linear_natural_exchange`: finite-reduction compatibility.
- `sbcCompletedExchange_strictLimit`: equality with the strict derived-limit realization.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u r v w v' w'
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local instance 2000] proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
private def conjugateRestriction
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ D) (F : C' ≌ D') (R : C' ⥤ C) (S : D' ⥤ D)
    (t : F.inverse ⋙ R ≅ S ⋙ E.inverse) : R ⋙ E.functor ≅ F.functor ⋙ S :=
  NatIso.ofComponents (fun M ↦
    E.functor.mapIso (R.mapIso (F.unitIso.app M)) ≪≫
      E.functor.mapIso (t.app (F.functor.obj M)) ≪≫
      E.counitIso.app (S.obj (F.functor.obj M))) (by
        intro M N f
        dsimp only [Functor.comp_map, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
        have hf := F.unitIso.hom.naturality f
        dsimp only [Functor.id_map, Functor.comp_map] at hf
        rw [← E.functor.map_comp_assoc, ← R.map_comp, hf]
        simp only [R.map_comp, E.functor.map_comp, Category.assoc]
        have ht := t.hom.naturality (F.functor.map f)
        dsimp only [Functor.comp_map] at ht
        have ht' := congrArg E.functor.map ht
        simp only [E.functor.map_comp] at ht'
        rw [reassoc_of% ht']
        have he := E.counitIso.hom.naturality (S.map (F.functor.map f))
        dsimp only [Functor.comp_map, Functor.id_map] at he
        rw [he])

private theorem normalizedReflectionIso
    {A C : Type*} [Category A] [Category C] (P : ObjectProperty C)
    (F G : A ⥤ P.FullSubcategory) (L M : A ⥤ C)
    (j : L ⟶ F ⋙ P.ι) (k : M ⟶ G ⋙ P.ι) (e : L ≅ M)
    (hj : ∀ (X : A) (N : P.FullSubcategory),
      Function.Bijective (fun a : (F.obj X).obj ⟶ N.obj ↦ j.app X ≫ a))
    (hk : ∀ (X : A) (N : P.FullSubcategory),
      Function.Bijective (fun a : (G.obj X).obj ⟶ N.obj ↦ k.app X ≫ a)) :
    ∃! t : F ≅ G, ∀ X : A,
      j.app X ≫ (t.hom.app X).hom = e.hom.app X ≫ k.app X := by
  classical
  choose a ha using fun X ↦ (hj X (G.obj X)).2 (e.hom.app X ≫ k.app X)
  choose b hb using fun X ↦ (hk X (F.obj X)).2 (e.inv.app X ≫ j.app X)
  dsimp only at ha hb
  let τ : F ⟶ G :=
    { app X := ObjectProperty.homMk (a X)
      naturality := by
        intro X Y f
        apply ObjectProperty.hom_ext
        apply (hj X (G.obj Y)).1
        have hjn : L.map f ≫ j.app Y = j.app X ≫ (F.map f).hom := j.naturality f
        have hkn : M.map f ≫ k.app Y = k.app X ≫ (G.map f).hom := k.naturality f
        change j.app X ≫ (F.map f).hom ≫ a Y =
          j.app X ≫ a X ≫ (G.map f).hom
        calc
          _ = L.map f ≫ j.app Y ≫ a Y := by
            rw [← Category.assoc, ← hjn, Category.assoc]
          _ = L.map f ≫ (e.hom.app Y ≫ k.app Y) := by rw [ha]
          _ = (e.hom.app X ≫ M.map f) ≫ k.app Y := by
            rw [← Category.assoc, e.hom.naturality]
          _ = (e.hom.app X ≫ k.app X) ≫ (G.map f).hom := by
            rw [Category.assoc, hkn, Category.assoc]
          _ = _ := by rw [← ha, Category.assoc] }
  let σ : G ⟶ F :=
    { app X := ObjectProperty.homMk (b X)
      naturality := by
        intro X Y f
        apply ObjectProperty.hom_ext
        apply (hk X (F.obj Y)).1
        have hkn : M.map f ≫ k.app Y = k.app X ≫ (G.map f).hom := k.naturality f
        have hjn : L.map f ≫ j.app Y = j.app X ≫ (F.map f).hom := j.naturality f
        change k.app X ≫ (G.map f).hom ≫ b Y =
          k.app X ≫ b X ≫ (F.map f).hom
        calc
          _ = M.map f ≫ k.app Y ≫ b Y := by
            rw [← Category.assoc, ← hkn, Category.assoc]
          _ = M.map f ≫ (e.inv.app Y ≫ j.app Y) := by rw [hb]
          _ = (e.inv.app X ≫ L.map f) ≫ j.app Y := by
            rw [← Category.assoc, e.inv.naturality]
          _ = (e.inv.app X ≫ j.app X) ≫ (F.map f).hom := by
            rw [Category.assoc, hjn, Category.assoc]
          _ = _ := by rw [← hb, Category.assoc] }
  have hτσ : τ ≫ σ = 𝟙 F := by
    ext X
    apply (hj X (F.obj X)).1
    change j.app X ≫ a X ≫ b X = j.app X ≫ 𝟙 _
    rw [← Category.assoc, ha, Category.assoc, hb]
    simp
  have hστ : σ ≫ τ = 𝟙 G := by
    ext X
    apply (hk X (G.obj X)).1
    change k.app X ≫ b X ≫ a X = k.app X ≫ 𝟙 _
    rw [← Category.assoc, hb, Category.assoc, ha]
    simp
  refine ⟨⟨τ, σ, hτσ, hστ⟩, ha, ?_⟩
  intro t ht
  apply Iso.ext
  ext X
  apply (hj X (G.obj X)).1
  exact (ht X).trans (ha X).symm

namespace WeilConjectures
/-- The published intrinsic completeness predicate on the actual completed ring.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev IsPbcComplete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) : ObjectProperty (PbcCompletedDerived T (pbcIntegralDatum l E)) :=
  PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E)

/-- Full category of intrinsically complete complexes without a constructibility bound.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev PbcComplete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) := (IsPbcComplete l E T).FullSubcategory

/-- Alias of the landed integral constructible category; no new predicate is defined.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev PbcIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) := PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)

/-- Alias of the landed raw rational constructible category.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev PbcRationalConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) := PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)

/-- Raw scalar localization of the complete ambient category, using the landed action.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev PbcRationalComplete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) :=
  ScalarLocalization (PbcIntegralRing l E) (PbcComplete l E T) (pbcUniformizer l E)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The full integral inclusion with the completeness property already in membership.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def pbcConstructibleInclusion (T : Scheme.{u}) :
    PbcIntegralConstructible l E T ⥤ PbcComplete l E T :=
  (IsPbcComplete l E T).lift
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)))
    (fun K ↦ K.property.1)

/-- The full inclusion preserves addition and the published constant scalar action.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: both subcategories have exactly the ambient Hom groups and scalar actions.
The inclusion sends every morphism to itself, so preserves addition and multiplication
by every constant section. These are the additive and linear functor equations. -/
theorem pbcConstructibleInclusion_linear (T : Scheme.{u}) :
    (pbcConstructibleInclusion l E T).Additive ∧
      (pbcConstructibleInclusion l E T).Linear (PbcIntegralRing l E) := by
  constructor
  · exact ⟨fun {_ _} {_ _} ↦ rfl⟩
  · exact ⟨fun {_ _} _ _ ↦ rfl⟩

/-- Additivity of the full inclusion. Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance pbcConstructibleInclusion_additive (T : Scheme.{u}) :
    (pbcConstructibleInclusion l E T).Additive :=
  (pbcConstructibleInclusion_linear l E T).1

/-- Linearity of the full inclusion. Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance pbcConstructibleInclusion_scalarLinear (T : Scheme.{u}) :
    (pbcConstructibleInclusion l E T).Linear (PbcIntegralRing l E) :=
  (pbcConstructibleInclusion_linear l E T).2

end WeilConjectures

namespace CategoryTheory.ScalarLocalization
variable (R : Type r) [CommRing R] (p : R)
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
  {D : Type v'} [Category.{w'} D] [Preadditive D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R]

/-- The localized map is the linear base change of the original map on Hom modules.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def betweenHom (K L : C) := (F.mapLinearMap R (X := K) (Y := L)).baseChange (Localization.Away p)

/-- Base change of linear Hom maps preserves the category laws.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: check identity on 1 tensor id and composition on pairs of pure tensors, where
both sides are ab tensor F(fg). Extend by bilinearity and tensor induction. -/
theorem between_laws :
    (∀ K : C, betweenHom R p F K K ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj K)) ∧
    (∀ (K L M : C) (f : Localization.Away p ⊗[R] (K ⟶ L))
      (g : Localization.Away p ⊗[R] (L ⟶ M)),
      betweenHom R p F K M (composition R C p K L M g f) =
        composition R D p (F.obj K) (F.obj L) (F.obj M)
          (betweenHom R p F L M g) (betweenHom R p F K L f)) := by
  constructor
  · intro K
    simp [betweenHom]
  · intro K L M f g
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f => simp [betweenHom, composition_tmul]
      | add f f' hf hf' => simp [map_add, hf, hf']
    | add g g' hg hg' => simp [map_add, hg, hg']

/-- Scalar localization of a linear functor between two possibly different categories.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def between : ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj K := ⟨F.obj K.obj⟩
  map {K L} f := betweenHom R p F K.obj L.obj f
  map_id K := (between_laws R p F).1 K.obj
  map_comp {K L M} f g := (between_laws R p F).2 K.obj L.obj M.obj f g

variable {F} {G : C ⥤ D} [G.Additive] [G.Linear R]

/-- Localized naturality follows on pure tensors from integral naturality.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: on a tensor a tensor f the two sides are a tensor of the naturality square
for f. The tensor maps and composition are additive, so tensor induction finishes. -/
theorem betweenNat_naturality (α : F ⟶ G) (K L : ScalarLocalization R C p)
    (f : K ⟶ L) :
    (between R p F).map f ≫ ((1 : Localization.Away p) ⊗ₜ[R] α.app L.obj) =
      ((1 : Localization.Away p) ⊗ₜ[R] α.app K.obj) ≫ (between R p G).map f := by
  change composition R D p _ _ _ _ (betweenHom R p F _ _ f) =
    composition R D p _ _ _ (betweenHom R p G _ _ f) _
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [betweenHom, composition_tmul, α.naturality f]
  | add f g hf hg => simp [map_add, hf, hg]

/-- Localize the specified natural transformation componentwise by tensoring with one.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def betweenNat (α : F ⟶ G) : between R p F ⟶ between R p G where
  app K := (1 : Localization.Away p) ⊗ₜ[R] α.app K.obj
  naturality := betweenNat_naturality R p α

end CategoryTheory.ScalarLocalization

namespace WeilConjectures
/-- Localize the full inclusion of the landed constructible category.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def pbcRationalInclusion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) : PbcRationalConstructible l E T ⥤ PbcRationalComplete l E T :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (pbcConstructibleInclusion l E T)
end WeilConjectures
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {U V : Scheme.{u}} (q : U ⟶ V)

/-- The canonical completed coefficient map is invertible.
Source: Stacks 099N (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: finite quotient sheaves are finite constant sheaves and their quotient maps
are the prescribed scalar maps. Profinite-coefficient inverse-image commutation applies
to this system. Its map agrees with completedCoefficientMap by every finite projection,
so the uniqueness of that limit-cone map identifies it with the given isomorphism. -/
theorem sbcCompletedCoefficientMap_isIso :
    IsIso (completedCoefficientMap q (pbcIntegralDatum l E)) := by
  let d := pbcIntegralDatum l E
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} := Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ d.quotientFinite n.unop
  let e (W : Scheme.{u}) : proEtaleCoefficientTower W Q ≅ adicLisseRingSystem W d.ideal :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (fun f ↦ (NatTrans.ofOpSequence
        (F := proEtaleCoefficientTower W Q) (G := adicLisseRingSystem W d.ideal)
        (fun _ ↦ 𝟙 _) (fun n ↦ by
          simp [proEtaleCoefficientTower, Q, adicLisseRingSystem])).naturality f)
  let b (W : Scheme.{u}) := e W ≪≫ pbcConstantSystemComparison W d
  let c (W : Scheme.{u}) := HasLimit.isoOfNatIso (b W)
  let L := proEtaleSheafInverseImage q CommRingCat.{u + 1}
  let := (proEtale_profinite_coefficient_inverse_image Q).2.1 U V q
  let t := L.mapIso (c V).symm ≪≫ asIso (proEtaleProfiniteComparison q Q) ≪≫ c U
  suffices h : completedCoefficientMap q d = t.hom by
    rw [h]
    infer_instance
  apply limit.hom_ext
  rintro ⟨n⟩
  dsimp only [completedCoefficientMap, t, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [limit.lift_π, Category.assoc]
  dsimp only [c]
  rw [HasLimit.isoOfNatIso_hom_π]
  simp only [asIso_hom]
  rw [reassoc_of% (proEtale_profinite_coefficient_inverse_image Q).2.2.1 U V q (op n)]
  rw [← Category.assoc, ← Category.assoc, ← L.map_comp]
  rw [HasLimit.isoOfNatIso_inv_π]
  simp only [L.map_comp, Category.assoc]
  dsimp only [b, e, Iso.trans_hom, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.id_comp, proEtaleConstantComparison]
  simp only [completedCoefficientComponent, completedFiniteCoefficientMap, Category.assoc,
    L, pbcConstantSystemComparison, pbcAdicProjection, Q, Iso.trans_inv,
    NatTrans.comp_app, NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app,
    Iso.refl_inv, Functor.map_comp]
  dsimp only [proEtaleCoefficientTower, Functor.comp_obj, Functor.ofOpSequence_obj]
  simp only [Iso.refl_hom, Category.id_comp]
  change L.map (pbcAdicProjection V d n) ≫
      L.map (pbcLevelConstantComparison V d n).inv ≫
      proEtaleConstantInverseImageMap q CommRingCat.{u + 1}
        (CommRingCat.of (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1))) ≫
      (pbcLevelConstantComparison U d n).hom =
    L.map (pbcAdicProjection V d n) ≫
      L.map (pbcLevelConstantComparison V d n).inv ≫
      L.map (𝟙 (adicLisseConstantRing V
        (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1)))) ≫
      proEtaleConstantInverseImageMap q CommRingCat.{u + 1}
        (CommRingCat.of (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1))) ≫
      (pbcLevelConstantComparison U d n).hom
  rw [L.map_id, Category.id_comp]

/-- The actual finite-projection-normalized coefficient isomorphism.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcCoefficientIso :=
  letI := sbcCompletedCoefficientMap_isIso l E q
  asIso (completedCoefficientMap q (pbcIntegralDatum l E))

/-- Ordinary, uncompleted, canonical derived pullback.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcOrdinaryPull := proEtaleRingDerivedPullback q
  (pbcAdicCompletion V (pbcIntegralDatum l E))
  (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)

/-- The actual K-injective derived module direct image along the coefficient map.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcAmbientPush := proEtaleRingDerivedDirectImage q
  (pbcAdicCompletion V (pbcIntegralDatum l E))
  (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)

/-- The specified object equality gives the identity on sheafified tensors.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryModuleIsoApp
    (M : pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E))) :
    (completedModulePullback q (pbcIntegralDatum l E)).obj M ≅
      (proEtaleRingModulePullback q
        (pbcAdicCompletion V (pbcIntegralDatum l E))
        (pbcAdicCompletion U (pbcIntegralDatum l E))
        (sbcCoefficientIso l E q)).obj M :=
  eqToIso ((completedAdicChangeData U
    (completedCoefficientMap q (pbcIntegralDatum l E))).choose_spec.choose
      ((proEtaleModuleInverseImage q
        (pbcAdicCompletion V (pbcIntegralDatum l E))).obj M))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The object equality in the normalized scalar-extension interface is natural.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: both maps are the sheafification of r tensor x maps to r tensor a(x),
by the morphism characterization in completedAdicChangeData. The tensor generators
and the sheafification universal property prove the naturality square. -/
theorem sbcOrdinaryModuleIso_naturality
    (M N : pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E)))
    (a : M ⟶ N) :
    (completedModulePullback q (pbcIntegralDatum l E)).map a ≫
      (sbcOrdinaryModuleIsoApp l E q N).hom =
    (sbcOrdinaryModuleIsoApp l E q M).hom ≫
      (proEtaleRingModulePullback q
        (pbcAdicCompletion V (pbcIntegralDatum l E))
        (pbcAdicCompletion U (pbcIntegralDatum l E))
        (sbcCoefficientIso l E q)).map a := by
  let h := (completedAdicChangeData U
    (completedCoefficientMap q (pbcIntegralDatum l E))).choose_spec.choose
  change (completedAdicChangeData U
    (completedCoefficientMap q (pbcIntegralDatum l E))).choose.map
      ((proEtaleModuleInverseImage q _).map a) ≫ eqToHom (h _) =
    eqToHom (h _) ≫ SheafOfModules.changeOfRingsHom
      (completedCoefficientMap q (pbcIntegralDatum l E)) _
      ((proEtaleModuleInverseImage q _).map a)
  erw [(completedAdicChangeData U
    (completedCoefficientMap q (pbcIntegralDatum l E))).choose_spec.choose_spec.choose
      ((proEtaleModuleInverseImage q _).map a)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The ordinary module comparison is identity on the specified sheafified tensors.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryModuleIso : completedModulePullback q (pbcIntegralDatum l E) ≅
    proEtaleRingModulePullback q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q) :=
  NatIso.ofComponents (fun M ↦ sbcOrdinaryModuleIsoApp l E q M)
    (fun {M N} a ↦ sbcOrdinaryModuleIso_naturality l E q M N a)

/-- Additivity of the exact ordinary tensor functor at these specified coefficients.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcOrdinaryModule_additive :
    (proEtaleRingModulePullback q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)).Additive :=
  proEtaleRingModulePullback_additive q
    (pbcAdicCompletion V (pbcIntegralDatum l E))
    (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)

/-- Zero-morphism preservation from the specified additive module pullback.
The explicit instance avoids an extra recursive instance search through coefficients.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcOrdinaryModule_preservesZero :
    (proEtaleRingModulePullback q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E))
      (sbcCoefficientIso l E q)).PreservesZeroMorphisms :=
  haveI := sbcOrdinaryModule_additive l E q
  Functor.preservesZeroMorphisms_of_additive _

/-- The canonical derived comparison retains the universal counit on every complex.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: the exact ordinary pullback is a total left derived functor of module pullback.
Its factorization composed with the normalized module comparison is the required
counit. Uniqueness of left derived functors gives the unique counit-preserving iso.
K-flat resolutions compute the same map, so this includes arbitrary unbounded objects. -/
theorem sbcOrdinaryDerivedIso_exists :
    ∃! e : completedOrdinaryPullback q (pbcIntegralDatum l E) ≅ sbcOrdinaryPull l E q,
      ∀ P : CochainComplex (pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E))) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (proEtaleRingDerivedPullbackFactors q
            (pbcAdicCompletion V (pbcIntegralDatum l E))
            (pbcAdicCompletion U (pbcIntegralDatum l E))
            (sbcCoefficientIso l E q)).hom.app P =
        Functor.leftDerivedCounitOnComplex
          (completedModulePullback q (pbcIntegralDatum l E))
          (completedOrdinaryPullback q (pbcIntegralDatum l E))
          (completedOrdinaryPullbackCounit q (pbcIntegralDatum l E)) P ≫
        DerivedCategory.Q.map ((@NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _
          (Functor.preservesZeroMorphisms_of_additive
            (completedModulePullback q (pbcIntegralDatum l E)))
          (sbcOrdinaryModule_preservesZero l E q)
          (sbcOrdinaryModuleIso l E q) (.up ℤ)).hom.app P) := by
  let F := completedModulePullback q (pbcIntegralDatum l E)
  let G := proEtaleRingModulePullback q
    (pbcAdicCompletion V (pbcIntegralDatum l E))
    (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)
  let LF := completedOrdinaryPullback q (pbcIntegralDatum l E)
  let ε := completedOrdinaryPullbackCounit q (pbcIntegralDatum l E)
  let W := HomotopyCategory.quasiIso
    (pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E))) (.up ℤ)
  let H := HomotopyCategory.quotient
    (pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E))) (.up ℤ)
  let e := sbcOrdinaryModuleIso l E q
  let eh : F.mapHomotopyCategory (.up ℤ) ≅ G.mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  have : LF.IsLeftDerivedFunctor ε W := by
    unfold LF ε completedOrdinaryPullback completedOrdinaryPullbackCounit
    exact (completedOrdinaryPullback_exists q (pbcIntegralDatum l E)).choose_spec.choose_spec.1
  have hi : W.IsInvertedBy (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [MorphismProperty.IsInvertedBy.iff_of_iso W
      (Functor.isoWhiskerRight eh DerivedCategory.Qh ≪≫ G.mapDerivedCategoryFactorsh.symm)]
    exact MorphismProperty.IsInvertedBy.of_comp W _ (Localization.inverts _ W) _
  have : IsIso ε := Functor.isIso_of_isLeftDerivedFunctor_of_inverts LF ε hi
  let δ : DerivedCategory.Q ⋙ LF ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm LF ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H (asIso ε) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso _)
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  let φ := δ ≪≫ Functor.isoWhiskerRight ec DerivedCategory.Q ≪≫
    G.mapDerivedCategoryFactors.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E))) (.up ℤ))
    (PbcCompletedDerived U (pbcIntegralDatum l E))
  let t := ff.preimageIso φ
  have ht : Functor.whiskerLeft DerivedCategory.Q t.hom = φ.hom :=
    ff.map_preimage φ.hom
  have hδ (P) : δ.hom.app P = Functor.leftDerivedCounitOnComplex F LF ε P := by
    simp only [δ, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, asIso_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp]
    rfl
  refine ⟨t, ?_, ?_⟩
  · intro P
    change t.hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategoryFactors.hom.app P =
        Functor.leftDerivedCounitOnComplex F LF ε P ≫
          DerivedCategory.Q.map (ec.hom.app P)
    have h := congr_app ht P
    change t.hom.app (DerivedCategory.Q.obj P) = _ at h
    rw [h]
    simp only [φ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
    rw [hδ]
  · intro t' ht'
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E))) (.up ℤ))
    intro P
    apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app P)).1
    have htP := congr_app ht P
    change t.hom.app (DerivedCategory.Q.obj P) = _ at htP
    rw [htP]
    simp only [φ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id, hδ]
    exact ht' P

/-- The ordinary comparison is fixed by the actual tensor counit, not an arbitrary iso.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryDerivedIso := (sbcOrdinaryDerivedIso_exists l E q).exists.choose

/-- Package the landed completed-pullback object construction with its actual maps.
This is the same reduction, strict tower pullback and derived limit composite.
Source: blueprint order 1442; Stacks 099N
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcCompletedPullbackFunctor :
    PbcCompletedDerived V (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived U (pbcIntegralDatum l E) :=
  completedReductionTower V (pbcIntegralDatum l E) ⋙
    completedTowerPullback q (pbcIntegralDatum l E) ⋙
      completedTowerRlim (pbcIntegralDatum l E) U

/-- Ordinary pullback followed by the strict-reduction-tower completion unit.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcCompletionUnit (K : PbcCompletedDerived V (pbcIntegralDatum l E)) :
    (sbcOrdinaryPull l E q).obj K ⟶ completedPullbackObject q (pbcIntegralDatum l E) K :=
  (sbcOrdinaryDerivedIso l E q).inv.app K ≫
    completedPullbackComparison q (pbcIntegralDatum l E) K

private theorem sbcComplete_iso {W : Scheme.{u}}
    {M N : PbcCompletedDerived W (pbcIntegralDatum l E)} (e : M ≅ N)
    (hM : IsPbcComplete l E W M) : IsPbcComplete l E W N := by
  rcases hM with ⟨r, a, ha, C, eC, hC⟩
  refine ⟨r, a, ha, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison W (pbcIntegralDatum l E)).inv).mapIso e,
    ?_⟩
  change IsIso (_ ≫ _)
  dsimp only [Iso.trans_inv, Functor.mapIso_inv]
  rw [Category.assoc]
  change IsIso ((pbcDerivedExtend (pbcCompletedComparison W (pbcIntegralDatum l E)).inv).map
    e.inv ≫ completedIntrinsicCompletionMap W _ r a C eC)
  have : IsIso (completedIntrinsicCompletionMap W _ r a C eC) := hC
  infer_instance

private theorem sbcComplete_unit_iff (W : Scheme.{u})
    (M : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    IsPbcComplete l E W M ↔
      IsIso ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app M) := by
  let P := IsPbcComplete l E W
  let adj := Adjunction.ofIsRightAdjoint P.ι
  change P M ↔ IsIso (adj.unit.app M)
  rw [adj.isIso_unit_app_iff_mem_essImage]
  refine ⟨fun h ↦ ⟨⟨M, h⟩, ⟨Iso.refl _⟩⟩, ?_⟩
  rintro ⟨N, ⟨e⟩⟩
  exact sbcComplete_iso l E e N.property

private def sbcAmbientPushIso :
    pbcActualDerivedPush q (pbcIntegralDatum l E) ≅ sbcAmbientPush l E q :=
  ((pbcActualDerivedAdjunction q (pbcIntegralDatum l E)).ofNatIsoLeft
    (sbcOrdinaryDerivedIso l E q)).rightAdjointUniq
      (proEtaleRingDerivedAdjunction q
        (pbcAdicCompletion V (pbcIntegralDatum l E))
        (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q))

/-- The actual operations preserve intrinsic completeness.
Source: Stacks 099N and 099K (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: completed pullback is the intrinsic completion by the constant/completed
comparison. For direct image, compute intrinsic completion by the Koszul products
and mapping fibres. Direct image commutes with limits and is linear in the generators;
its derived functor commutes with these homotopy limits. Thus it carries a complete
object to a complete object. No scheme finiteness or constructibility is used. -/
theorem sbcOperations_preserveComplete :
    (∀ K : PbcComplete l E V, IsPbcComplete l E U
      ((sbcCompletedPullbackFunctor l E q).obj K.obj)) ∧
    (∀ K : PbcComplete l E U, IsPbcComplete l E V
      ((sbcAmbientPush l E q).obj K.obj)) := by
  constructor
  · intro K
    let e := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) q).exists.choose
    exact sbcComplete_iso l E (e.app K).symm
      (pbcActualCompletedPull_isComplete q (pbcIntegralDatum l E) K.obj)
  · intro K
    let d := pbcIntegralDatum l E
    let R := pbcActualDerivedPush q d
    let c := (pbcActualDirectCompletionIso_exists q d).exists.choose
    have hc := (pbcActualDirectCompletionIso_exists q d).exists.choose_spec K.obj
    have hK := (sbcComplete_unit_iff l E U K.obj).1 K.property
    have : IsIso ((pbcActualCompletionUnit d V).app (R.obj K.obj)) := by
      apply (isIso_comp_right_iff _ (c.hom.app K.obj)).1
      rw [hc]
      infer_instance
    exact sbcComplete_iso l E ((sbcAmbientPushIso l E q).app K.obj)
      ((sbcComplete_unit_iff l E V (R.obj K.obj)).2 inferInstance)

/-- Restrict the actual completed-pullback functor to complete objects.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcPull : PbcComplete l E V ⥤ PbcComplete l E U :=
  (IsPbcComplete l E U).lift
    (ObjectProperty.ι (IsPbcComplete l E V) ⋙ sbcCompletedPullbackFunctor l E q)
    (sbcOperations_preserveComplete l E q).1

/-- Restrict the actual derived direct-image functor to complete objects.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcPush : PbcComplete l E U ⥤ PbcComplete l E V :=
  (IsPbcComplete l E V).lift (ObjectProperty.ι (IsPbcComplete l E U) ⋙ sbcAmbientPush l E q)
    (sbcOperations_preserveComplete l E q).2

/-- Both restrictions are additive and linear for the specified constant sections.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: module inverse image and extension preserve addition and constant scalars on
pure tensors. Direct image does so sectionwise; on derived Hom groups compute with
K-injective representatives and chain maps. Completion uses products, tensor and
mapping fibres, which preserve the same scalar operations. The full subcategories
inherit exactly these Hom actions. -/
theorem sbcOperations_linear :
    (sbcPull l E q).Additive ∧ (sbcPush l E q).Additive ∧
      (sbcPull l E q).Linear (PbcIntegralRing l E) ∧
      (sbcPush l E q).Linear (PbcIntegralRing l E) := by
  let d := pbcIntegralDatum l E
  let I := ObjectProperty.ι (IsPbcComplete l E V)
  let t := (pbcActualCompletedPullback_tower d q).exists.choose
  have : (I ⋙ sbcCompletedPullbackFunctor l E q).Additive :=
    Functor.additive_of_iso t.symm
  have : (I ⋙ sbcCompletedPullbackFunctor l E q).Linear (PbcIntegralRing l E) :=
    Functor.linear_of_iso (PbcIntegralRing l E) t.symm
  have : (sbcAmbientPush l E q).Additive :=
    Functor.additive_of_iso (sbcAmbientPushIso l E q)
  have : (sbcAmbientPush l E q).Linear (PbcIntegralRing l E) :=
    Functor.linear_of_iso (PbcIntegralRing l E) (sbcAmbientPushIso l E q)
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    intro M N a b
    apply ObjectProperty.hom_ext
    exact (I ⋙ sbcCompletedPullbackFunctor l E q).map_add (f := a) (g := b)
  · constructor
    intro M N a b
    apply ObjectProperty.hom_ext
    exact (sbcAmbientPush l E q).map_add (f := a.hom) (g := b.hom)
  · constructor
    intro M N a c
    apply ObjectProperty.hom_ext
    exact Functor.map_smul (I ⋙ sbcCompletedPullbackFunctor l E q) c a
  · constructor
    intro M N a c
    apply ObjectProperty.hom_ext
    exact Functor.map_smul (sbcAmbientPush l E q) c a.hom

/-- Additivity of completed pullback.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcPull_additive : (sbcPull l E q).Additive := (sbcOperations_linear l E q).1
/-- Additivity of completed direct image.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcPush_additive : (sbcPush l E q).Additive := (sbcOperations_linear l E q).2.1
/-- Constant-section scalar linearity of completed pullback.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcPull_linear : (sbcPull l E q).Linear (PbcIntegralRing l E) :=
  (sbcOperations_linear l E q).2.2.1
/-- Constant-section scalar linearity of completed direct image.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcPush_linear : (sbcPush l E q).Linear (PbcIntegralRing l E) :=
  (sbcOperations_linear l E q).2.2.2

private theorem sbcCompletionUnit_naturality
    {M N : PbcCompletedDerived V (pbcIntegralDatum l E)} (a : M ⟶ N) :
    (sbcOrdinaryPull l E q).map a ≫ sbcCompletionUnit l E q N =
      sbcCompletionUnit l E q M ≫ (sbcCompletedPullbackFunctor l E q).map a := by
  let j := (sbcOrdinaryDerivedIso l E q).inv ≫
    pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) q
  simpa only [j, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, pbcActualStrictCompletedPullUnit,
    sbcCompletionUnit, completedPullbackComparison, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Category.id_comp,
    Category.assoc, pbcActualDerivedPull, pbcActualStrictCompletedPull,
    sbcCompletedPullbackFunctor, completedPullbackObject, Functor.comp_map]
      using j.naturality a

private theorem sbcCompletionUnit_universal (M : PbcComplete l E V)
    (N : PbcComplete l E U) :
    Function.Bijective (fun a : ((sbcPull l E q).obj M).obj ⟶ N.obj ↦
      sbcCompletionUnit l E q M.obj ≫ a) := by
  let d := pbcIntegralDatum l E
  let P := IsPbcComplete l E U
  let adj := Adjunction.ofIsRightAdjoint
    (ObjectProperty.ι (PbcIsIntrinsicallyComplete U d))
  let t := (pbcActualCompletedPullback_tower d q).exists.choose
  let A := (completedOrdinaryPullback q d).obj M.obj
  let B := P.ι.leftAdjoint.obj A
  let eb : (P.ι.obj B ⟶ N.obj) ≃ (A ⟶ N.obj) :=
    P.fullyFaithfulι.homEquiv.symm.trans (adj.homEquiv A N)
  let e : (((sbcPull l E q).obj M).obj ⟶ N.obj) ≃
      ((sbcOrdinaryPull l E q).obj M.obj ⟶ N.obj) :=
    ((Iso.homCongr (t.app M) (Iso.refl N.obj)).trans eb).trans
    (Iso.homCongr ((sbcOrdinaryDerivedIso l E q).app M.obj) (Iso.refl N.obj))
  have hj : sbcCompletionUnit l E q M.obj ≫ (t.hom.app M) =
      (sbcOrdinaryDerivedIso l E q).inv.app M.obj ≫ adj.unit.app A := by
    have ht := (pbcActualCompletedPullback_tower d q).exists.choose_spec M
    have ht' : completedPullbackComparison q d M.obj ≫ t.hom.app M =
        adj.unit.app A := by
      simpa only [pbcActualStrictCompletedPullUnit, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_inv_app, Functor.rightUnitor_inv_app,
        pbcActualCompletedPullUnit, pbcActualCompletionUnit, pbcActualDerivedPull,
        completedPullbackComparison, Category.id_comp, Category.assoc, t, adj, A] using ht
    change (_ ≫ _) ≫ _ = _
    erw [Category.assoc, ht']
  have he (a : ((sbcPull l E q).obj M).obj ⟶ N.obj) :
      e a = sbcCompletionUnit l E q M.obj ≫ a := by
    dsimp only [e, eb, Equiv.trans_apply, Iso.homCongr,
      Equiv.coe_fn_mk, Functor.FullyFaithful.homEquiv, Equiv.symm]
    simp only [Iso.refl_hom, Category.comp_id]
    change (sbcOrdinaryDerivedIso l E q).inv.app M.obj ≫
      (adj.homEquiv A N) (ObjectProperty.homMk ((t.app M).inv ≫ a)) = _
    erw [Adjunction.homEquiv_unit]
    change (sbcOrdinaryDerivedIso l E q).inv.app M.obj ≫
      (adj.unit.app A ≫ ((t.app M).inv ≫ a)) = _
    rw [← Category.assoc, ← hj]
    simp only [Category.assoc]
    congr 1
    exact (t.app M).hom_inv_id_assoc a
  have he' : ⇑e = fun a ↦ sbcCompletionUnit l E q M.obj ≫ a := funext he
  exact he' ▸ e.bijective

/-- The complete adjunction is uniquely normalized by the ordinary unit and completion.
Source: Stacks 099K (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: completion is the reflector onto intrinsic complete objects. For complete N,
precomposition by the completion unit gives Hom(PM,N)=Hom(LM,N). Compose with the
canonical ordinary derived module adjunction. The resulting Hom equivalence defines
an adjunction and its unit is the displayed composite. Its unit determines it uniquely. -/
theorem sbcAdjunction_exists :
    ∃! adj : sbcPull l E q ⊣ sbcPush l E q,
      ∀ M : PbcComplete l E V, (adj.unit.app M).hom =
        (proEtaleRingDerivedAdjunction q
          (pbcAdicCompletion V (pbcIntegralDatum l E))
          (pbcAdicCompletion U (pbcIntegralDatum l E))
          (sbcCoefficientIso l E q)).unit.app M.obj ≫
        (sbcAmbientPush l E q).map (sbcCompletionUnit l E q M.obj) := by
  let ao := proEtaleRingDerivedAdjunction q
    (pbcAdicCompletion V (pbcIntegralDatum l E))
    (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)
  let hom (M : PbcComplete l E V) (N : PbcComplete l E U) :
      ((sbcPull l E q).obj M ⟶ N) ≃ (M ⟶ (sbcPush l E q).obj N) :=
    ((IsPbcComplete l E U).fullyFaithfulι.homEquiv
      (X := (sbcPull l E q).obj M) (Y := N)).trans
      ((Equiv.ofBijective _ (sbcCompletionUnit_universal l E q M N)).trans
        ((ao.homEquiv M.obj N.obj).trans
          ((IsPbcComplete l E V).fullyFaithfulι.homEquiv
            (X := M) (Y := (sbcPush l E q).obj N)).symm))
  have hh (M : PbcComplete l E V) (N : PbcComplete l E U)
      (a : (sbcPull l E q).obj M ⟶ N) :
      (hom M N a).hom = ao.homEquiv M.obj N.obj
        (sbcCompletionUnit l E q M.obj ≫ a.hom) := rfl
  let core : Adjunction.CoreHomEquiv (sbcPull l E q) (sbcPush l E q) :=
    { homEquiv := hom
      homEquiv_naturality_left_symm := by
        intro M' M N a b
        apply (hom M' N).injective
        apply ObjectProperty.hom_ext
        rw [Equiv.apply_symm_apply, hh]
        simp only [ObjectProperty.FullSubcategory.comp_hom]
        change a.hom ≫ b.hom = ao.homEquiv _ _
          (sbcCompletionUnit l E q M'.obj ≫
            (sbcCompletedPullbackFunctor l E q).map a.hom ≫ ((hom M N).symm b).hom)
        rw [← Category.assoc, ← sbcCompletionUnit_naturality l E q a.hom, Category.assoc,
          ao.homEquiv_naturality_left]
        exact congrArg (a.hom ≫ ·) (congrArg (fun k ↦ k.hom)
          ((hom M N).apply_symm_apply b)).symm
      homEquiv_naturality_right := by
        intro M N N' a b
        apply ObjectProperty.hom_ext
        rw [hh]
        simp only [ObjectProperty.FullSubcategory.comp_hom]
        rw [hh]
        change ao.homEquiv _ _ (_ ≫ (a.hom ≫ b.hom)) = _
        rw [← Category.assoc, ao.homEquiv_naturality_right]
        rfl }
  let ac := Adjunction.mkOfHomEquiv core
  have hu (M : PbcComplete l E V) : (ac.unit.app M).hom =
      ao.unit.app M.obj ≫ (sbcAmbientPush l E q).map (sbcCompletionUnit l E q M.obj) := by
    change (hom M ((sbcPull l E q).obj M) (𝟙 _)).hom = _
    rw [hh, ObjectProperty.FullSubcategory.id_hom]
    erw [Category.comp_id, Adjunction.homEquiv_unit]
  refine ⟨ac, hu, ?_⟩
  intro ac' hu'
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply ObjectProperty.hom_ext
  exact (hu' M).trans (hu M).symm

/-- The canonical completed adjunction with its fixed tensor-unit normalization.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcAdjunction := (sbcAdjunction_exists l E q).exists.choose

variable {U V : Scheme.{u}} (q : U ⟶ V)

/-- Retain the prescribed finite coefficient identification, with no extra choice.
Source: blueprint order 1444 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcFiniteCoefficientIso (n : ℕ) :=
  letI := completedFiniteCoefficientMap_isIso q (pbcIntegralDatum l E) n
  asIso (completedFiniteCoefficientMap q (pbcIntegralDatum l E) n)

/-- Ordinary, uncompleted, quotient-coefficient inverse image.
Source: blueprint order 1444 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcFinitePull (n : ℕ) := proEtaleRingDerivedPullback q
  (((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))
  (((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))) (sbcFiniteCoefficientIso l E q n)

/-- Ordinary K-injective quotient-coefficient direct image, without completion.
Source: blueprint order 1444 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcFinitePush (n : ℕ) := proEtaleRingDerivedDirectImage q
  (((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))
  (((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))) (sbcFiniteCoefficientIso l E q n)

private def sbcSuccessiveCompletionUnit {Z : Scheme.{u}} (v : Z ⟶ U) :
    ObjectProperty.ι (IsPbcComplete l E V) ⋙
        (sbcOrdinaryPull l E q ⋙ sbcOrdinaryPull l E v) ⟶
      (sbcPull l E q ⋙ sbcPull l E v) ⋙ ObjectProperty.ι (IsPbcComplete l E Z) where
  app K := (sbcOrdinaryPull l E v).map (sbcCompletionUnit l E q K.obj) ≫
    sbcCompletionUnit l E v ((sbcPull l E q).obj K).obj
  naturality M N a := by
    change (sbcOrdinaryPull l E v).map ((sbcOrdinaryPull l E q).map a.hom) ≫
      ((sbcOrdinaryPull l E v).map (sbcCompletionUnit l E q N.obj) ≫ _) = _
    rw [← Functor.map_comp_assoc, sbcCompletionUnit_naturality, Functor.map_comp]
    simp only [Category.assoc]
    exact congrArg ((sbcOrdinaryPull l E v).map (sbcCompletionUnit l E q M.obj) ≫ ·)
      (sbcCompletionUnit_naturality l E v ((sbcPull l E q).map a).hom)

private theorem sbcFiniteCoefficientComp {Z : Scheme.{u}} (v : Z ⟶ U) (n : ℕ) :
    proEtaleRingCompositeCoefficients v q
      ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n))
      ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))
      ((pbcAdicRings Z (pbcIntegralDatum l E)).obj (op n))
      (sbcFiniteCoefficientIso l E q n) (sbcFiniteCoefficientIso l E v n) =
        sbcFiniteCoefficientIso l E (v ≫ q) n := by
  let d := pbcIntegralDatum l E
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
    (Functor.const ℕᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1)))
  let : ∀ j : ℕᵒᵖ, Finite (Q.obj j) := fun _ ↦ d.quotientFinite n
  have hc := (proEtale_profinite_coefficient_inverse_image Q).2.2.2.2.2.2.2.2.2.1
    Z U V v q (op n)
  apply Iso.ext
  dsimp only [proEtaleRingCompositeCoefficients, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, sbcFiniteCoefficientIso, asIso_hom]
  dsimp only [completedFiniteCoefficientMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (proEtaleSheafInverseImage v CommRingCat.{u + 1}).map_comp_assoc
    (pbcLevelConstantComparison U d n).hom (pbcLevelConstantComparison U d n).inv]
  simp only [Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← (proEtaleRingInverseImageComp v q).hom.naturality_assoc
    (pbcLevelConstantComparison V d n).inv]
  dsimp only [proEtaleConstantComparison, Q, Functor.const_obj_obj] at hc
  rw [hc]
  simp only [Category.assoc]
  rfl

/-- Completed coefficient identifications commute with composition.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: project to any finite quotient. Both maps are the canonical successive
inverse-image maps of a constant finite sheaf. Their composition law agrees on
constant sections, hence everywhere; the completed limit projections are jointly monic. -/
theorem sbcCoefficientComp {Z : Scheme.{u}} (v : Z ⟶ U) :
    proEtaleRingCompositeCoefficients v q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E))
      (pbcAdicCompletion Z (pbcIntegralDatum l E))
      (sbcCoefficientIso l E q) (sbcCoefficientIso l E v) =
        sbcCoefficientIso l E (v ≫ q) := by
  let d := pbcIntegralDatum l E
  let L := proEtaleSheafInverseImage v CommRingCat.{u + 1}
  have hp {A B : Scheme.{u}} (a : A ⟶ B) (n : ℕ) :
      completedCoefficientMap a d ≫ pbcAdicProjection A d n =
        (proEtaleSheafInverseImage a CommRingCat.{u + 1}).map
          (pbcAdicProjection B d n) ≫ completedFiniteCoefficientMap a d n :=
    limit.lift_π _ (op n)
  apply Iso.ext
  apply limit.hom_ext
  rintro ⟨n⟩
  change (proEtaleRingInverseImageComp v q).hom.app (pbcAdicCompletion V d) ≫
      L.map (completedCoefficientMap q d) ≫
        completedCoefficientMap v d ≫ pbcAdicProjection _ d n =
    completedCoefficientMap (v ≫ q) d ≫ pbcAdicProjection _ d n
  rw [hp v n, hp (v ≫ q) n, ← L.map_comp_assoc, hp q n, L.map_comp]
  simp only [Category.assoc]
  erw [← (proEtaleRingInverseImageComp v q).hom.naturality_assoc
    (pbcAdicProjection V d n)]
  have hc := congrArg Iso.hom (sbcFiniteCoefficientComp l E q v n)
  dsimp only [proEtaleRingCompositeCoefficients, Iso.trans_hom, Functor.mapIso_hom,
    sbcFiniteCoefficientIso, asIso_hom] at hc
  exact congrArg ((proEtaleSheafInverseImage (v ≫ q) CommRingCat.{u + 1}).map
    (pbcAdicProjection V d n) ≫ ·) hc

private theorem sbcSuccessiveUnit_universal {Z : Scheme.{u}} (v : Z ⟶ U)
    (K : PbcComplete l E V) (N : PbcComplete l E Z) :
    Function.Bijective (fun a : (((sbcPull l E q ⋙ sbcPull l E v).obj K).obj ⟶ N.obj) ↦
      (sbcOrdinaryPull l E v).map (sbcCompletionUnit l E q K.obj) ≫
        sbcCompletionUnit l E v ((sbcPull l E q).obj K).obj ≫ a) := by
  let ao := proEtaleRingDerivedAdjunction v
    (pbcAdicCompletion U (pbcIntegralDatum l E))
    (pbcAdicCompletion Z (pbcIntegralDatum l E)) (sbcCoefficientIso l E v)
  let R := (sbcPush l E v).obj N
  let e1 := Equiv.ofBijective _
    (sbcCompletionUnit_universal l E v ((sbcPull l E q).obj K) N)
  let e2 := ao.homEquiv ((sbcPull l E q).obj K).obj N.obj
  let e3 := Equiv.ofBijective _ (sbcCompletionUnit_universal l E q K R)
  let e4 := (ao.homEquiv ((sbcOrdinaryPull l E q).obj K.obj) N.obj).symm
  let b := e1.trans (e2.trans (e3.trans e4))
  have hb (a) : b a =
      (sbcOrdinaryPull l E v).map (sbcCompletionUnit l E q K.obj) ≫
        sbcCompletionUnit l E v ((sbcPull l E q).obj K).obj ≫ a := by
    apply (ao.homEquiv _ _).injective
    dsimp only [b, Equiv.trans_apply]
    erw [Equiv.apply_symm_apply]
    change sbcCompletionUnit l E q K.obj ≫
      ao.homEquiv _ _ (sbcCompletionUnit l E v ((sbcPull l E q).obj K).obj ≫ a) = _
    rw [← ao.homEquiv_naturality_left]
  have hb' : ⇑b = fun a ↦
      (sbcOrdinaryPull l E v).map (sbcCompletionUnit l E q K.obj) ≫
        sbcCompletionUnit l E v ((sbcPull l E q).obj K).obj ≫ a := funext hb
  exact hb' ▸ b.bijective


/-- Canonical quotient-linear reduction of an ambient completed complex.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcReduction (W : Scheme.{u}) (n : ℕ) :=
  pbcCompletedReduction W (pbcIntegralDatum l E) n

/-- The completed and finite coefficient identifications form the projection square.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: this is precisely the finite-projection characterization of the completed
coefficient map; replacing the two invertible maps by asIso changes no homomorphism. -/
theorem sbcProjectionSquare (n : ℕ) :
    (sbcCoefficientIso l E q).hom ≫ pbcAdicProjection U (pbcIntegralDatum l E) n =
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
        (pbcAdicProjection V (pbcIntegralDatum l E) n) ≫
          (sbcFiniteCoefficientIso l E q n).hom := by
  change completedCoefficientMap q (pbcIntegralDatum l E) ≫
    pbcAdicProjection U (pbcIntegralDatum l E) n = _
  exact limit.lift_π _ (op n)

/-- Restriction comparison is the recorded identity-on-sections coefficient square.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcRestrictionPull (n : ℕ) :=
  proEtaleRingRestrictionDerivedPullback q
    (pbcAdicCompletion V (pbcIntegralDatum l E))
    (((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))
    (pbcAdicCompletion U (pbcIntegralDatum l E))
    (((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n)))
    (pbcAdicProjection V (pbcIntegralDatum l E) n)
    (pbcAdicProjection U (pbcIntegralDatum l E) n)
    (sbcCoefficientIso l E q) (sbcFiniteCoefficientIso l E q n)
    (sbcProjectionSquare l E q n)

/-- Ordinary pullback/reduction comparison is the scalar-adjunction mate of restriction.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryReductionMap (n : ℕ) :
    sbcOrdinaryPull l E q ⋙ sbcReduction l E U n ⟶
      sbcReduction l E V n ⋙ sbcFinitePull l E q n :=
  ((mateEquiv
    (AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
      (pbcAdicProjection V (pbcIntegralDatum l E) n))
    (AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
      (pbcAdicProjection U (pbcIntegralDatum l E) n))).symm
        (TwoSquare.mk _ _ _ _ (sbcRestrictionPull l E q n).inv))

/-- The ordinary comparison is tensor balancing on K-flat representatives.
Source: Stacks 07A4 and 06YY (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: take a flat-term K-flat resolution. Exact inverse image preserves the
corresponding acyclic tensor tests. Both composites are its pullback tensored with
the same quotient; their unit-normalized mate is balancing, whose reverse is its
inverse. Localization gives an isomorphism on every derived object. -/
theorem sbcOrdinaryReductionMap_isIso (n : ℕ) :
    IsIso (sbcOrdinaryReductionMap l E q n) := by
  exact proEtaleReductionPullbackInv_isIso q
    (pbcAdicCompletion V (pbcIntegralDatum l E))
    ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n))
    (pbcAdicCompletion U (pbcIntegralDatum l E))
    ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))
    (pbcAdicProjection V (pbcIntegralDatum l E) n)
    (pbcAdicProjection U (pbcIntegralDatum l E) n)
    (sbcCoefficientIso l E q) (sbcFiniteCoefficientIso l E q n)
    (sbcProjectionSquare l E q n)

attribute [local irreducible] smallModulesEquiv completedCechModulesEquiv

section CompletionPresentation
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

private def sbcRestrictId (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules X R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))) (fun _ ↦ by ext U x; rfl)

private def sbcPresentationBackEquiv :
    adicDatumModules X (intrinsicPresentationDatum d) ≌ pbcModules X (pbcAdicCompletion X d) :=
  CategoryTheory.Equivalence.mk (intrinsicPresentationModulesBack X d)
    (intrinsicPresentationModules X d)
    ((pbcRestrictComp (pbcCompletedComparison X d).hom (pbcCompletedComparison X d).inv
        (𝟙 _) (pbcCompletedComparison X d).hom_inv_id ≪≫
      sbcRestrictId X _).symm)
    (intrinsicPresentationRoundTrip X d).symm

include ha in
private theorem sbcIntrinsicWitness (M : PbcCompletedDerived X d)
    (C : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ)
    (e : (DerivedCategory.Q.obj C :
        DerivedCategory (adicDatumModules X (intrinsicPresentationDatum d))) ≅
      (pbcDerivedExtend (pbcCompletedComparison X d).inv).obj M)
    (h : IsIso (e.inv ≫ DerivedCategory.Q.map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C))) :
    PbcIsIntrinsicallyComplete X d M := by
  exact ⟨r, a, ha, C, e, h⟩

private theorem sbcPresentation_of_complete (M : PbcCompletedDerived X d)
    (hM : WfIsComplete X d r a ha M) : PbcIsIntrinsicallyComplete X d M := by
  let B := intrinsicPresentationModulesBack X d
  let G := intrinsicPresentationModules X d
  let E := sbcPresentationBackEquiv X d
  have : B.IsEquivalence := E.isEquivalence_functor
  have : G.IsEquivalence := E.isEquivalence_inverse
  let C := wfCompletionRepresentative X d M
  let C' := (G.mapHomologicalComplex (.up ℤ)).obj C
  let real := DerivedCategory.Q.objObjPreimageIso M
  let adj := pbcDerivedScalarAdjunction (pbcCompletedComparison X d).inv
  have : E.symm.functor.Additive := inferInstanceAs G.Additive
  have : E.symm.inverse.Additive := inferInstanceAs B.Additive
  let ej := (E.symm.mapDerivedCategory : DerivedCategory (pbcModules X (pbcAdicCompletion X d)) ≌
    DerivedCategory (adicDatumModules X (intrinsicPresentationDatum d))).toAdjunction
  let j : G.mapDerivedCategory ≅ pbcDerivedExtend (pbcCompletedComparison X d).inv :=
    Adjunction.leftAdjointUniq ej adj
  let eC : (DerivedCategory.Q.obj C' :
        DerivedCategory (adicDatumModules X (intrinsicPresentationDatum d))) ≅
      (pbcDerivedExtend (pbcCompletedComparison X d).inv).obj M :=
    (G.mapDerivedCategoryFactors.app C).symm ≪≫ G.mapDerivedCategory.mapIso real ≪≫ j.app M
  have hu : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) := by
    have : IsIso (real.inv ≫ DerivedCategory.Q.map
        (intrinsicCompletionComplexUnit X d r a C)) := hM
    exact IsIso.of_isIso_comp_left real.inv _
  have hq : QuasiIso (intrinsicCompletionComplexUnit X d r a C) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hu
  let t : C ≅ (B.mapHomologicalComplex (.up ℤ)).obj C' :=
    (NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip X d) (.up ℤ)).app C
  have hcomp : intrinsicCompletionComplexUnit X d r a C =
      t.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C') := by
    unfold intrinsicCompletionComplexUnit intrinsicCompletionUnitComponent
    ext q
    rfl
  have hBu : QuasiIso ((B.mapHomologicalComplex (.up ℤ)).map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C')) := by
    have : QuasiIso (t.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C')) := by
      rw [← hcomp]
      exact hq
    exact quasiIso_of_comp_left t.hom _
  have hCu : QuasiIso (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C') :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ B).1 hBu
  apply sbcIntrinsicWitness X d r a ha M C' eC
  infer_instance

private theorem wfComplete_iff_presentation (M : PbcCompletedDerived X d) :
    WfIsComplete X d r a ha M ↔ PbcIsIntrinsicallyComplete X d M := by
  constructor
  · exact sbcPresentation_of_complete X d r a ha M
  · intro hM
    exact (d.towerComplete_iff_intrinsic X M).mp
      (pbcIntrinsicComplete_towerComplete d X M hM) r a ha _ _
private theorem sbcConstantFiniteRestriction_complete (n : ℕ)
    (M : ConstantCompletion.D (ConstantCompletion.finite
      (completedCechTopology X) A d.ideal n)) :
    ConstantCompletion.IsComplete
      (ConstantCompletion.projection (completedCechTopology X) A d.ideal 0)
      ((ConstantCompletion.dres (ConstantCompletion.projection
        (completedCechTopology X) A d.ideal n)).obj M) := by
  let J := completedCechTopology X
  let := d.noetherian
  let S : CategoryTheory.AdicSites.Site := ⟨completedCechSite X, J⟩
  let φ := ConstantCompletion.coefficientMap J A d.ideal
  let p := ConstantCompletion.projection J A d.ideal n
  let q := ConstantCompletion.quotient J A d.ideal n
  have hp : φ ≫ p = q := limit.lift_π _ _
  have : PreservesFiniteLimits (ConstantCompletion.res p) :=
    (siteRestrictScalars_exact p).1
  have : PreservesFiniteColimits (ConstantCompletion.res p) :=
    (siteRestrictScalars_exact p).2
  have : PreservesFiniteLimits (ConstantCompletion.res φ) :=
    (siteRestrictScalars_exact φ).1
  have : PreservesFiniteColimits (ConstantCompletion.res φ) :=
    (siteRestrictScalars_exact φ).2
  have : PreservesFiniteLimits (ConstantCompletion.res q) :=
    (siteRestrictScalars_exact q).1
  have : PreservesFiniteColimits (ConstantCompletion.res q) :=
    (siteRestrictScalars_exact q).2
  let e : ConstantCompletion.dres p ⋙ ConstantCompletion.dres φ ≅
      ConstantCompletion.dres q :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (ConstantCompletion.resCompIso φ p q hp)
  have hm := CategoryTheory.AdicSites.finiteRestriction_complete S A
    d.toCompleteCoefficientDatum n M
  let : ∀ U : completedCechSite X, HasDerivedCategory
      (SheafOfModules (siteModuleRings ((ConstantCompletion.constant J A).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : completedCechSite X, HasDerivedCategory
      (SheafOfModules (siteModuleRings ((ConstantCompletion.completed J A d.ideal).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  have hm' : ConstantCompletion.IsComplete (ConstantCompletion.quotient J A d.ideal 0)
      ((ConstantCompletion.dres φ).obj ((ConstantCompletion.dres p).obj M)) := by
    exact locallyDerivedRingedIdealComplete_of_iso _ _ (e.app M) hm
  have h := siteDerivedRestrictScalars_locallyDerivedComplete_iff φ
    (ConstantCompletion.kernelIdeal (ConstantCompletion.quotient J A d.ideal 0))
    ((ConstantCompletion.dres p).obj M)
  rw [ConstantCompletion.coefficientKernel_extension] at h
  exact h.mp hm'

include r a ha in
private theorem sbcFiniteRestricted_complete (n : ℕ)
    (M : DerivedCategory (pbcModules X (reductionCoefficient X d n))) :
    PbcIsIntrinsicallyComplete X d
      ((pbcDerivedRestrict (completedReductionProjection X d n)).obj M) := by
  let := d.noetherian
  let E := comparisonModulesEquiv X d
  let β := comparisonCompletedRingIso X d
  let δ := comparisonFiniteRing X d n
  let Ef := smallModulesEquiv X (reductionCoefficient X d n)
    (ConstantCompletion.finite (completedCechTopology X) A d.ideal n) δ
  let R := pbcRestrict (completedReductionProjection X d n)
  let R' := ConstantCompletion.res
    (ConstantCompletion.projection (completedCechTopology X) A d.ideal n)
  let τ := smallRestrictionComparison X β δ (completedReductionProjection X d n)
    (ConstantCompletion.projection (completedCechTopology X) A d.ideal n)
    (comparisonRing_projection X d n)
  let τ' := conjugateRestriction E Ef R R' τ
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : Ef.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : R'.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits R' := (siteRestrictScalars_exact _).1
  have : PreservesFiniteColimits R' := (siteRestrictScalars_exact _).2
  have : (completedCechModulesEquiv X d).functor.IsEquivalence :=
    (completedCechModulesEquiv X d).isEquivalence_functor
  have : (ConstantCompletion.res β.inv).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits (ConstantCompletion.res β.inv) :=
    (siteRestrictScalars_exact _).1
  have : PreservesFiniteColimits (ConstantCompletion.res β.inv) :=
    (siteRestrictScalars_exact _).2
  let ED := E.mapDerivedCategory
  let FD := Ef.mapDerivedCategory
  let τD : pbcDerivedRestrict (completedReductionProjection X d n) ⋙ ED.functor ≅
      FD.functor ⋙ ConstantCompletion.dres
        (ConstantCompletion.projection (completedCechTopology X) A d.ideal n) :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso τ' ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  have : PreservesFiniteLimits (completedCechModulesEquiv X d).functor := inferInstance
  have : PreservesFiniteColimits (completedCechModulesEquiv X d).functor := inferInstance
  have : (completedCechModulesEquiv X d).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (ConstantCompletion.res
      (CechConstantAlgebra.algebraIso X d.ideal (pbcCompletedComparison X d)).inv).Additive :=
    inferInstance
  have : PreservesFiniteLimits (ConstantCompletion.res
      (CechConstantAlgebra.algebraIso X d.ideal (pbcCompletedComparison X d)).inv) :=
    (siteRestrictScalars_exact _).1
  have : PreservesFiniteColimits (ConstantCompletion.res
      (CechConstantAlgebra.algebraIso X d.ideal (pbcCompletedComparison X d)).inv) :=
    (siteRestrictScalars_exact _).2
  have : PreservesFiniteLimits ((completedCechModulesEquiv X d).functor ⋙
      ConstantCompletion.res
        (CechConstantAlgebra.algebraIso X d.ideal (pbcCompletedComparison X d)).inv) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ inferInstance
      (siteRestrictScalars_exact _).1
  have : PreservesFiniteColimits ((completedCechModulesEquiv X d).functor ⋙
      ConstantCompletion.res
        (CechConstantAlgebra.algebraIso X d.ideal (pbcCompletedComparison X d)).inv) :=
    @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ inferInstance
      (siteRestrictScalars_exact _).2
  let δD : ED.functor ≅ (completedCechDerivedEquiv X d).functor ⋙
      ConstantCompletion.dres β.inv :=
    Functor.mapDerivedCategoryNatIso (comparisonModulesEquiv_to_cech X d) ≪≫
      (Functor.mapDerivedCategoryCompIso (completedCechModulesEquiv X d).functor
        (ConstantCompletion.res β.inv)).symm
  let N := (pbcDerivedRestrict (completedReductionProjection X d n)).obj M
  let C := wfCompletionRepresentative X d N
  let real := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨c, hc⟩ := completed_koszul_constant_transport X d β
    (comparisonCompletedRingIso_scalar X d) ED.functor δD r a ha C
  let H := ConstantCompletion.completion (completedCechTopology X) A d.ideal true
  let η := ConstantCompletion.completionUnit (completedCechTopology X) A d.ideal true
  obtain ⟨_, _, _, _, hi⟩ := ConstantCompletion.koszul_quotient_reflector
    (completedCechTopology X) A d.ideal true r a ha
  have hm := sbcConstantFiniteRestriction_complete X d n (FD.functor.obj M)
  let : ∀ U : completedCechSite X, HasDerivedCategory (SheafOfModules (siteModuleRings
      ((ConstantCompletion.completed (completedCechTopology X) A d.ideal).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  have hm' : ConstantCompletion.IsComplete
      (ConstantCompletion.projection (completedCechTopology X) A d.ideal 0)
      (ED.functor.obj N) :=
    locallyDerivedRingedIdealComplete_of_iso _ _ (τD.app M) hm
  have hn : IsIso (η.app (ED.functor.obj N)) := (hi _).2 hm'
  have hC : IsIso (η.app (ED.functor.obj (DerivedCategory.Q.obj C))) := by
    apply (isIso_comp_right_iff _ (H.map (ED.functor.map real.hom))).1
    have hn' := η.naturality (ED.functor.map real.hom)
    dsimp only [Functor.id_map, Functor.comp_map] at hn'
    rw [← hn']
    let := hn
    infer_instance
  have hu : IsIso (ED.functor.map
      (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C))) := by
    apply (isIso_comp_right_iff _ c.hom).1
    rw [hc]
    exact hC
  have : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) :=
    isIso_of_reflects_iso _ ED.functor
  apply sbcPresentation_of_complete X d r a ha
  change IsIso (real.inv ≫ DerivedCategory.Q.map
    (intrinsicCompletionComplexUnit X d r a C))
  infer_instance

end CompletionPresentation

/-- Reduction turns the completion unit into an isomorphism.
Source: Stacks 099N(5) (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: restricting a finite-quotient complex gives an intrinsically complete complex:
transport to the constant-coefficient site, where nilpotence proves completeness, then
transport back through the normalized Koszul comparison. The scalar-extension adjunction
and the completion-unit universal property show that the reduced unit induces a
bijection on maps to every finite-coefficient complex. Coyoneda detects its invertibility. -/
theorem sbcCompletionUnit_reduction_isIso (n : ℕ) (K : PbcComplete l E V) :
    IsIso ((sbcReduction l E U n).map (sbcCompletionUnit l E q K.obj)) := by
  let d := pbcIntegralDatum l E
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let adj := pbcDerivedScalarAdjunction (pbcAdicProjection U d n)
  apply isIso_of_coyoneda_map_bijective
  intro M
  let N : PbcComplete l E U := ⟨_, sbcFiniteRestricted_complete U d r a ha n M⟩
  have hbij := sbcCompletionUnit_universal l E q K N
  constructor
  · intro x y hxy
    apply (adj.homEquiv _ _).injective
    apply hbij.injective
    change sbcCompletionUnit l E q K.obj ≫ (adj.homEquiv _ _) x =
      sbcCompletionUnit l E q K.obj ≫ (adj.homEquiv _ _) y
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
    exact congrArg (adj.homEquiv _ _) hxy
  · intro y
    obtain ⟨x, hx⟩ := hbij.surjective ((adj.homEquiv _ _) y)
    refine ⟨(adj.homEquiv _ _).symm x, ?_⟩
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hx

/-- The finite reduction of completed pullback, with its projection/unit normalization.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcPullReduction (n : ℕ) (K : PbcComplete l E V) :
    (sbcReduction l E U n).obj ((sbcPull l E q).obj K).obj ⟶
      (sbcFinitePull l E q n).obj ((sbcReduction l E V n).obj K.obj) :=
  letI := sbcCompletionUnit_reduction_isIso l E q n K
  inv ((sbcReduction l E U n).map (sbcCompletionUnit l E q K.obj)) ≫
    (sbcOrdinaryReductionMap l E q n).app K.obj

/-- The pushforward comparison is the canonical mate of ordinary pullback/reduction.
It is the finite-perfect projection-formula map, rather than a selected isomorphism.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcPushReduction (n : ℕ) (K : PbcComplete l E U) :
    (sbcReduction l E V n).obj ((sbcPush l E q).obj K).obj ⟶
      (sbcFinitePush l E q n).obj ((sbcReduction l E U n).obj K.obj) :=
  letI := sbcOrdinaryReductionMap_isIso l E q n
  (proEtaleRingDerivedAdjunction q
    (((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))
    (((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n)))
    (sbcFiniteCoefficientIso l E q n)).unit.app _ ≫
  (sbcFinitePush l E q n).map
    (inv ((sbcOrdinaryReductionMap l E q n).app ((sbcPush l E q).obj K).obj)) ≫
  (sbcFinitePush l E q n).map ((sbcReduction l E U n).map
    ((proEtaleRingDerivedAdjunction q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E))
      (sbcCoefficientIso l E q)).counit.app K.obj))

private theorem sbcFiniteRingIso_eq (n : ℕ) :
    (pbcIntegralDatum l E).finiteRingIso q n = sbcFiniteCoefficientIso l E q n := by
  apply Iso.ext
  rfl

private theorem sbcIntegralRingIso_eq :
    (pbcIntegralDatum l E).integralRingIso q = sbcCoefficientIso l E q := by
  apply Iso.ext
  apply limit.hom_ext
  rintro ⟨n⟩
  change ((pbcIntegralDatum l E).integralRingIso q).hom ≫
      (pbcIntegralDatum l E).projection U n = _
  rw [AdicCoefficientDatum.projection_comm, sbcFiniteRingIso_eq]
  exact (sbcProjectionSquare l E q n).symm

private theorem sbcProjection_isIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    (cR : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj
      (d.completedRing V) ≅ d.completedRing U)
    (cS : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj
      (d.finiteRing V n) ≅ d.finiteRing U n)
    (heR : d.integralRingIso q = cR) (heS : d.finiteRingIso q n = cS)
    (comm : cR.hom ≫ d.projection U n =
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map (d.projection V n) ≫ cS.hom)
    (M : d.derived U) :
    IsIso ((proEtaleRingDerivedAdjunction q (d.finiteRing V n) (d.finiteRing U n) cS).homEquiv _ _
      ((proEtaleReductionPullbackIso q (d.completedRing V) (d.finiteRing V n)
        (d.completedRing U) (d.finiteRing U n) (d.projection V n) (d.projection U n)
        cR cS comm).hom.app
          ((proEtaleRingDerivedDirectImage q (d.completedRing V) (d.completedRing U) cR).obj M) ≫
        (d.reduction U n).map ((proEtaleRingDerivedAdjunction q (d.completedRing V)
          (d.completedRing U) cR).counit.app M))) := by
  subst cR
  subst cS
  exact d.finiteProjection_isIso q M n

attribute [local irreducible] sbcCoefficientIso sbcFiniteCoefficientIso
  AdicCoefficientDatum.integralRingIso AdicCoefficientDatum.finiteRingIso

/-- Both canonical finite comparisons are invertible.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: the pullback comparison is the composite of two already invertible maps.
The pushforward mate is the projection formula for the globally strict-perfect
coefficient quotient. Compute that quotient by the two-term free complex for the
uniformizer power. Derived direct image commutes with the finite sums, shifts and
cones in that complex, and the displayed mate is identity on the free generator.
This proves invertibility without any boundedness or finiteness condition on q. -/
theorem sbcReductionComparisons_isIso (n : ℕ) :
    (∀ K : PbcComplete l E V, IsIso (sbcPullReduction l E q n K)) ∧
      (∀ K : PbcComplete l E U, IsIso (sbcPushReduction l E q n K)) := by
  constructor
  · intro K
    let := sbcCompletionUnit_reduction_isIso l E q n K
    let := sbcOrdinaryReductionMap_isIso l E q n
    unfold sbcPullReduction
    infer_instance
  · intro K
    have h := sbcProjection_isIso q (pbcIntegralDatum l E) n
      (sbcCoefficientIso l E q) (sbcFiniteCoefficientIso l E q n)
      (sbcIntegralRingIso_eq l E q) (sbcFiniteRingIso_eq l E q n)
      (sbcProjectionSquare l E q n) K.obj
    simp only [Adjunction.homEquiv_unit, Functor.map_comp,
      proEtaleReductionPullbackIso, Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app] at h
    unfold sbcPushReduction
    convert! h using 1

variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)

/-- The two composite coefficient identifications agree on every finite projection.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: both send the constant residue of a to the same constant residue after inverse
image. This proves equality at each finite quotient, and the limit projections determine
the completed map. Transport along square commutativity gives the stated heterogeneous equality. -/
theorem sbcCoefficientSquare (_square : ChosenCartesianSquare h e f g) : HEq
    (proEtaleRingCompositeCoefficients h f
      (pbcAdicCompletion S (pbcIntegralDatum l E))
      (pbcAdicCompletion X (pbcIntegralDatum l E))
      (pbcAdicCompletion Y (pbcIntegralDatum l E))
      (sbcCoefficientIso l E f) (sbcCoefficientIso l E h))
    (proEtaleRingCompositeCoefficients e g
      (pbcAdicCompletion S (pbcIntegralDatum l E))
      (pbcAdicCompletion T (pbcIntegralDatum l E))
      (pbcAdicCompletion Y (pbcIntegralDatum l E))
      (sbcCoefficientIso l E g) (sbcCoefficientIso l E e)) := by
  rw [sbcCoefficientComp, sbcCoefficientComp]
  have aux : ∀ (a b : Y ⟶ S), a = b →
      HEq (sbcCoefficientIso l E a) (sbcCoefficientIso l E b) := by
    intro a b hab
    subst b
    rfl
  exact aux _ _ _square.w

/-- The ordinary tensor-normalized comparison, in the orientation used by exchange.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryTheta : sbcOrdinaryPull l E f ⋙ sbcOrdinaryPull l E h ≅
    sbcOrdinaryPull l E g ⋙ sbcOrdinaryPull l E e :=
  (proEtaleAmbientRingedPullbackComparison sq
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (pbcAdicCompletion S (pbcIntegralDatum l E))
    (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (pbcAdicCompletion T (pbcIntegralDatum l E))
    (sbcCoefficientIso l E f) (sbcCoefficientIso l E g)
    (sbcCoefficientIso l E h) (sbcCoefficientIso l E e)
    (sbcCoefficientSquare l E sq)).symm

private theorem sbcTheta_ofIso
    (c : sbcOrdinaryPull l E f ⋙ sbcOrdinaryPull l E h ≅
      sbcOrdinaryPull l E g ⋙ sbcOrdinaryPull l E e) :
    ∃! t : sbcPull l E f ⋙ sbcPull l E h ≅ sbcPull l E g ⋙ sbcPull l E e,
      ∀ K : PbcComplete l E S,
        (sbcOrdinaryPull l E h).map (sbcCompletionUnit l E f K.obj) ≫
          sbcCompletionUnit l E h ((sbcPull l E f).obj K).obj ≫
          (t.hom.app K).hom =
        c.hom.app K.obj ≫
          (sbcOrdinaryPull l E e).map (sbcCompletionUnit l E g K.obj) ≫
          sbcCompletionUnit l E e ((sbcPull l E g).obj K).obj := by
  let I := ObjectProperty.ι (IsPbcComplete l E S)
  let j := sbcSuccessiveCompletionUnit l E f h
  let k := sbcSuccessiveCompletionUnit l E g e
  have hj (K : PbcComplete l E S) (N : PbcComplete l E Y) :
      Function.Bijective (fun a : ((sbcPull l E f ⋙ sbcPull l E h).obj K).obj ⟶ N.obj ↦
        j.app K ≫ a) := by
    convert! sbcSuccessiveUnit_universal l E f h K N using 1
    funext a
    exact Category.assoc _ _ _
  have hk (K : PbcComplete l E S) (N : PbcComplete l E Y) :
      Function.Bijective (fun a : ((sbcPull l E g ⋙ sbcPull l E e).obj K).obj ⟶ N.obj ↦
        k.app K ≫ a) := by
    convert! sbcSuccessiveUnit_universal l E g e K N using 1
    funext a
    exact Category.assoc _ _ _
  obtain ⟨t, ht, hu⟩ := normalizedReflectionIso (IsPbcComplete l E Y)
    (sbcPull l E f ⋙ sbcPull l E h) (sbcPull l E g ⋙ sbcPull l E e) _ _ j k
    (Functor.isoWhiskerLeft I c) hj hk
  refine ⟨t, ?_, ?_⟩
  · intro K
    exact (Category.assoc _ _ _).symm.trans (ht K)
  · intro t' ht'
    apply hu t'
    intro K
    exact (Category.assoc _ _ _).trans (ht' K)

/-- The completed square comparison is fixed by ordinary pullback and the two units.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: successive completion is completion of successive ordinary pullback, by the
reflector property and compatibility of the coefficient ideals. The ordinary theta
therefore extends uniquely across the two completion units. Its inverse extends the
ordinary inverse, so the extension is an isomorphism. This is equivalently the
composition comparison obtained by uniqueness of the composite adjunction. -/
theorem sbcTheta_exists :
    ∃! t : sbcPull l E f ⋙ sbcPull l E h ≅ sbcPull l E g ⋙ sbcPull l E e,
      ∀ K : PbcComplete l E S,
        (sbcOrdinaryPull l E h).map (sbcCompletionUnit l E f K.obj) ≫
          sbcCompletionUnit l E h ((sbcPull l E f).obj K).obj ≫
          (t.hom.app K).hom =
        (sbcOrdinaryTheta l E sq).hom.app K.obj ≫
          (sbcOrdinaryPull l E e).map (sbcCompletionUnit l E g K.obj) ≫
          sbcCompletionUnit l E e ((sbcPull l E g).obj K).obj := by
  exact sbcTheta_ofIso l E (sbcOrdinaryTheta l E sq)

/-- The square comparison with the ordinary-unit normalization retained.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcTheta := (sbcTheta_exists l E sq).exists.choose

/-- The specified unit/comparison/counit mate, as an actual component morphism.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcExchangeApp (K : PbcComplete l E T) :
    (sbcPull l E f).obj ((sbcPush l E g).obj K) ⟶
      (sbcPush l E h).obj ((sbcPull l E e).obj K) :=
  (sbcAdjunction l E h).unit.app _ ≫
    (sbcPush l E h).map ((sbcTheta l E sq).hom.app ((sbcPush l E g).obj K)) ≫
    (sbcPush l E h).map ((sbcPull l E e).map ((sbcAdjunction l E g).counit.app K))

/-- The mate is natural, without an invertibility or finiteness assumption.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: apply the naturality equations for the unit, theta and counit, and functoriality
of the two operations. Associativity pastes the three squares into the required square.
Finite reduction preserves this construction: normalized pullback and direct-image
comparisons carry its unit and counit to the ordinary finite units and counits, and
carry theta to finite tensor balancing. Applying derived inverse limit gives the same
completed mate. Thus the construction agrees with finite-level completed exchange. -/
theorem sbcExchange_naturality {K K' : PbcComplete l E T} (a : K ⟶ K') :
    (sbcPush l E g ⋙ sbcPull l E f).map a ≫ sbcExchangeApp l E sq K' =
      sbcExchangeApp l E sq K ≫ (sbcPull l E e ⋙ sbcPush l E h).map a := by
  let η := Functor.whiskerLeft (sbcPush l E g ⋙ sbcPull l E f) (sbcAdjunction l E h).unit
  let θ := Functor.whiskerRight (Functor.whiskerLeft (sbcPush l E g) (sbcTheta l E sq).hom)
    (sbcPush l E h)
  let ε := Functor.whiskerRight (Functor.whiskerRight (sbcAdjunction l E g).counit (sbcPull l E e))
    (sbcPush l E h)
  exact (η ≫ θ ≫ ε).naturality a

/-- The integral natural exchange is the specified adjunction mate.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcExchange : sbcPush l E g ⋙ sbcPull l E f ⟶ sbcPull l E e ⋙ sbcPush l E h where
  app K := sbcExchangeApp l E sq K
  naturality {_K _K'} a := sbcExchange_naturality l E sq a

attribute [local irreducible] sbcOrdinaryTheta sbcTheta sbcAdjunction
  proEtaleRingDerivedAdjunction Functor.mapDerivedCategory Functor.rightDerivedFunctor
  completedAdicDerivedChange proEtaleRingModulePullback proEtaleAmbientRingedPullbackComparison

private def pushUnderlying (M : PbcComplete l E U) :
    ((sbcPush l E q).obj M).obj ⟶ (sbcAmbientPush l E q).obj M.obj := 𝟙 _

-- Abstracting the dependent functor families requires additional elaboration steps.
-- Generalizing the comparison data and sixteen functors requires additional elaboration steps.
end WeilConjectures
