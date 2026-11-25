/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.GroupTheory.Torsion
import WeilConjectures.AlgebraicGeometry.PrincipalConeKoszulRoosComparison
import WeilConjectures.CategoryTheory.Principal.PrincipalIdealLocalTestCriterion
import all WeilConjectures.CategoryTheory.UnitPowerCompleteness
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import WeilConjectures.Algebra.Homology.InternalHom
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
import WeilConjectures.CategoryTheory.RingedKoszulDualizable
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
import WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
import WeilConjectures.Algebra.Homology.TelescopeColimit
import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
import WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement
import WeilConjectures.Algebra.Homology.SliceTensorNatural
import WeilConjectures.Algebra.Homology.SliceModuleSheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.Native.NativePrincipalCompletenessSmallModel
import WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import Mathlib.GroupTheory.OrderOfElement
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.SixFunctors.OpenRoosRestriction.OpenRoosRestrictionDescent
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.CharAndCard
import all WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus

/-! # Actual open completion units and the complete open adjunction

Source: Stacks Project, Tags 099M, 099N (2),(5), and 09BN; Bhatt--Scholze,
Proposition 3.5.1 and Definition 3.5.2, p.24
(blueprint: lem-sf-open-roos-unit-adjunction).

The quotient completion and its unit are the published strict augmented Roos
construction. The comparison is characterized uniquely by compatibility with this
unit; the normalized exact-product construction gives precisely that comparison.
The index n denotes the positive exponent n+1. Coefficient and site universes are
independent, and all derived categories and complexes are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.OpenRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The published intrinsic Koszul-unit condition, specialized to the actual uniformizer.
Quantification over representatives avoids adding a choice to complete objects.
Source: Stacks 099B, 0A0E; the integral specialization of intrinsic completion in
RoosIntrinsicCompletenessEquivalence (blueprint: lem-sf-open-roos-unit-adjunction). -/
abbrev Intrinsic (T : Scheme.{t}) (K : IntegralOnSlice.D l E T none) : Prop :=
  ∀ (C : IntegralOnSlice.Cx l E T none) (e : DerivedCategory.Q.obj C ≅ K),
    IsIso (integralKoszulIntrinsicUnit l E T K C e)

/-- The four reflector assertions, all for the actual quotient-augmentation unit.
Source: Stacks 099M and 099B (blueprint: lem-sf-open-roos-unit-adjunction). -/
def ReflectorAssertions (T : Scheme.{t}) : Prop :=
  (∀ H : IntegralOnSlice.D l E T none,
    Intrinsic l E T ((IntegralOnSlice.completion l E T none).obj H)) ∧
  (∀ H L : IntegralOnSlice.D l E T none, Intrinsic l E T L →
    Function.Bijective (fun f : (IntegralOnSlice.completion l E T none).obj H ⟶ L ↦
      (IntegralOnSlice.completionUnit l E T none).app H ≫ f)) ∧
  (∀ H : IntegralOnSlice.D l E T none,
    IntegralOnSlice.IsComplete l E T none H ↔
      IsIso ((IntegralOnSlice.completionUnit l E T none).app H)) ∧
  (∀ H : IntegralOnSlice.D l E T none,
    IsIso ((IntegralOnSlice.completionUnit l E T none).app H) ↔ Intrinsic l E T H)

/-- The full complete category, using the recorded Roos-triangle predicate verbatim.
Source: Bhatt--Scholze Definition 3.5.2
(blueprint: lem-sf-open-roos-unit-adjunction). -/
abbrev Complete (T : Scheme.{t}) :=
  ObjectProperty.FullSubcategory (IntegralOnSlice.IsComplete l E T none)

variable {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

/-- Literal restriction of the ordinary derived extension to complete objects.
Source: Stacks 09BN (blueprint: lem-sf-open-roos-unit-adjunction). -/
def completeExtension
    (h : ∀ M, IntegralOnSlice.IsComplete l E V none M →
      IntegralOnSlice.IsComplete l E W none ((IntegralOpenReduction.shriek l E e o).obj M)) :
    Complete l E V ⥤ Complete l E W :=
  ObjectProperty.lift _
    ((ObjectProperty.ι (IntegralOnSlice.IsComplete l E V none)) ⋙
      IntegralOpenReduction.shriek l E e o)
    (fun M ↦ h M.obj M.property)

/-- Literal restriction of ordinary derived open restriction to complete objects.
Source: Stacks 099N (2),(5) (blueprint: lem-sf-open-roos-unit-adjunction). -/
def completeRestriction
    (h : ∀ H, IntegralOnSlice.IsComplete l E W none H →
      IntegralOnSlice.IsComplete l E V none ((IntegralOpenReduction.star l E e o).obj H)) :
    Complete l E W ⥤ Complete l E V :=
  ObjectProperty.lift _
    ((ObjectProperty.ι (IntegralOnSlice.IsComplete l E W none)) ⋙
      IntegralOpenReduction.star l E e o)
    (fun H ↦ h H.obj H.property)

/-- The actual pulled quotient tower's Roos derived-limit model on good representatives.
The restriction is applied to the entire strict tower, retaining its transitions.
Source: Stacks 099N (5), 0941 (blueprint: lem-sf-open-roos-unit-adjunction). -/
def pulledRoos : (IntegralOnSlice.Good l E W none).FullSubcategory ⥤
    IntegralOnSlice.D l E V none :=
  (IntegralOnSlice.Good l E W none).ι ⋙ IntegralOnSlice.tower l E W none ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)) ⋙
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q

/-- The actual pulled augmentation: apply restriction to (gamma,0), then the map
which is the canonical product comparison in BOTH Roos coordinates.
Source: Stacks 099N (5), 0941 (blueprint: lem-sf-open-roos-unit-adjunction). -/
def pulledUnit (P : IntegralOnSlice.Cx l E W none) :=
  ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)).map
      (IntegralOnSlice.roosUnit l E W none P) ≫
    scalarRoosMap (IntegralOpenReduction.restriction l E e o)
      ((IntegralOnSlice.tower l E W none).obj P)

attribute [local irreducible] CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit
  CategoryTheory.RingedKoszulLimitPresentation.completion
  CategoryTheory.RingedKoszulLimitPresentation.unit
attribute [local irreducible] principalKoszulRoosUnit roosF koszulTowerComplex koszulTensorTower
  SheafOfModules.monoidalCategory

private theorem normalizedComparison_unique
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) (L : A ⥤ A) (η : 𝟭 A ⟶ L) (R : B ⥤ B) (ε : 𝟭 B ⟶ R)
    (h : ∀ H : A, Function.Injective
      (fun f : R.obj (F.obj H) ⟶ R.obj (F.obj H) ↦ ε.app (F.obj H) ≫ f))
    (rho sigma : L ⋙ F ≅ F ⋙ R)
    (ha : ∀ H, F.map (η.app H) ≫ rho.hom.app H = ε.app (F.obj H))
    (hb : ∀ H, F.map (η.app H) ≫ sigma.hom.app H = ε.app (F.obj H)) : sigma = rho := by
  apply Iso.ext
  apply NatTrans.ext
  funext H
  apply (cancel_epi (rho.inv.app H)).mp
  have hh : rho.inv.app H ≫ sigma.hom.app H = 𝟙 _ := by
    apply h H
    change ε.app (F.obj H) ≫ (rho.inv.app H ≫ sigma.hom.app H) =
      ε.app (F.obj H) ≫ 𝟙 _
    rw [← ha H]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Category.comp_id]
    exact (hb H).trans (ha H).symm
  simpa only [Iso.inv_hom_id_app] using hh

private theorem compUnitIso {A : Type*} [Category A] {P C D E : A}
    (a : C ≅ D) (b : D ≅ E) (u : P ⟶ C) (v : P ⟶ D) (w : P ⟶ E)
    (ha : u ≫ a.hom = v) (hb : v ≫ b.hom = w) :
    u ≫ (a ≪≫ b).hom = w := by
  rw [Iso.trans_hom, ← Category.assoc, ha, hb]

private theorem homBijection_transport
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) [F.Full] [F.Faithful]
    {P C L : A} {P' C' : B} (a : F.obj C ≅ C') (b : F.obj P ≅ P')
    (u : P ⟶ C) (v : P' ⟶ C') (hu : F.map u ≫ a.hom = b.hom ≫ v)
    (hb : Function.Bijective (fun f : C' ⟶ F.obj L ↦ v ≫ f)) :
    Function.Bijective (fun f : C ⟶ L ↦ u ≫ f) := by
  have hmap (f : C ⟶ L) :
      F.map (u ≫ f) = b.hom ≫ v ≫ a.inv ≫ F.map f := by
    calc
      _ = (F.map u ≫ a.hom) ≫ a.inv ≫ F.map f := by
        simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
      _ = _ := by rw [hu]; simp only [Category.assoc]
  constructor
  · intro f g hfg
    apply F.map_injective
    apply (cancel_epi a.inv).mp
    apply hb.injective
    apply (cancel_epi b.hom).mp
    simpa only [Category.assoc, ← hmap] using congrArg F.map hfg
  · intro f
    obtain ⟨g, hg⟩ := hb.surjective (b.inv ≫ F.map f)
    let g' := F.preimage (a.hom ≫ g)
    refine ⟨g', F.map_injective ?_⟩
    rw [hmap]
    simp only [g', Functor.map_preimage, Iso.inv_hom_id_assoc]
    change v ≫ g = b.inv ≫ F.map f at hg
    rw [hg]
    simp only [Iso.hom_inv_id_assoc]

private theorem smallPrincipalHom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : C, HasSheafify (J.over U) CommRingCat.{u}]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    [HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (μ : End P)
    (hμ : ∀ (q : ℤ) (U : Cᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x =
        @SMul.smul _ _ ((P.X q).val.obj U).isModule.toSMul (a.val U) x)
    (L : DerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hL : principalLocallyComplete.{u, u, u, w} R a L) :
    Function.Bijective (fun f : DerivedCategory.Q.obj
        (CochainComplex.PrincipalCone.completion μ) ⟶ L ↦
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫ f) := by
  let : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let := principalLocalTestSliceDerived R
  let : HasBinaryBiproducts (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  have hD := ringedKoszulCompletionReflector R 1 (fun _ ↦ a)
    (image (ringedKoszulScalar R a).asHom) (image.ι (ringedKoszulScalar R a).asHom)
    (principal_generators R a)
  let D := hD.choose
  have hb := hD.choose_spec.2.1
  let b : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections := ⟨a.val, a.property⟩
  set_option backward.isDefEq.respectTransparency true in
  have hC := principalConeKoszulRoosComparison R P a μ hμ
  let c := hC.choose
  have hc := hC.choose_spec
  set_option backward.isDefEq.respectTransparency true in
  have hE := principalKoszulRoos_presentation_comparison R b P D
  let d := hE.choose
  have hd := hE.choose_spec
  let e := c ≪≫ d
  have he : DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫ e.hom =
      D.unit (DerivedCategory.Q.obj P) :=
    compUnitIso c d _ _ _ hc hd
  exact homBijection_transport (𝟭 _) e (Iso.refl _)
    (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ))
    (D.unit (DerivedCategory.Q.obj P))
    (by simpa only [Functor.id_map, Iso.refl_hom, Category.id_comp] using he)
    (hb _ L ((principalLocallyComplete_iff R a L).mp hL))

private theorem principalHom (T : Scheme.{t})
    (σ : ∀ U : T.ProEtᵒᵖ, (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    (hσ : ∀ {U V : T.ProEtᵒᵖ} (f : U ⟶ V),
      (completedIntegralCoefficientSheafUnrestricted l E T).obj.map f (σ U) = σ V)
    (P : IntegralOnSlice.Cx l E T none) (μ : End P)
    (hμ : ∀ (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x = σ U • x)
    (L : IntegralOnSlice.D l E T none)
    (hL : IntegralPrincipalCone.locallyComplete l E T σ L) :
    Function.Bijective (fun f : DerivedCategory.Q.obj
        (CochainComplex.PrincipalCone.completion μ) ⟶ L ↦
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫ f) := by
  let J := IntegralOnSlice.topology T none
  let R := IntegralOnSlice.ring l E T none
  let Rg := IntegralOnSlice.rings l E T none
  let a : (R.obj ⋙ forget CommRingCat).sections := ⟨σ, hσ⟩
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    IntegralOnSlice.abSheafify.{t, u} T none
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    IntegralOnSlice.abLocallyBijective.{t, u} T none
  let : ∀ U : IntegralOnSlice.Site T none, HasSheafify (J.over U) AddCommGrpCat.{max u (t + 1)} :=
    fun U ↦ IntegralOnSlice.abSheafify.{t, u} T (some U)
  let : ∀ U : IntegralOnSlice.Site T none, (J.over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
    fun U ↦ IntegralOnSlice.abLocallyBijective.{t, u} T (some U)
  let : ∀ U : IntegralOnSlice.Site T none, HasSheafify (J.over U) CommRingCat.{max u (t + 1)} :=
    fun U ↦
      letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
      hasSheafifyEssentiallySmallSite _ _
  let : HasDerivedCategory (SheafOfModules.{max u (t + 1)} Rg) :=
    IntegralOnSlice.hasDerived l E T none
  let : ∀ U : IntegralOnSlice.Site T none,
      HasDerivedCategory (SheafOfModules.{max u (t + 1)} (Rg.over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  have testIso (N : IntegralOnSlice.D l E T none) (U : T.ProEt)
      (s : ((R.over U).obj ⋙ forget CommRingCat).sections) :
      IntegralPrincipalCone.localTest l E T N U s ≅ principalLocalTest.{t + 1, t, u} R N U s := by
    letI := (SheafOfModules.overFunctor_exact_ofUniverses Rg U).1
    letI := (SheafOfModules.overFunctor_exact_ofUniverses Rg U).2
    exact (IntegralOnSlice.hom l E T (some U)).mapIso
      ((Iso.refl _).prod (SheafOfModules.overFunctor_derivedRestrictionIso Rg U N))
  have hpred (N : IntegralOnSlice.D l E T none) :
      IntegralPrincipalCone.locallyComplete l E T σ N ↔
        principalLocallyComplete.{t + 1, t, u} R a N := by
    constructor
    · intro h U s hs
      exact (h U s hs).of_iso (testIso N U s).symm
    · intro h U s hs
      exact (h U s hs).of_iso (testIso N U s)
  let F := AsSmall.down.{t, t + 1, max u (t + 1)}
    (C := IntegralOnSlice.Site T none)
  let Js := F.inducedTopology J
  let : F.IsEquivalence :=
    (AsSmall.equiv.{t, t + 1, max u (t + 1)}
      (C := IntegralOnSlice.Site T none)).symm.isEquivalence_functor
  let S := NativeRestriction.restrictedCommRing.{max u (t + 1), t + 1,
    max u (t + 1), t, u} (K := Js) F R
  let H := NativeRestriction.restrictModules.{max u (t + 1), t + 1,
    max u (t + 1), t, u} (K := Js) F R
  let : H.IsEquivalence := NativeRestriction.globalModulesEquivalence
    (K := Js) F R
  let : HasSheafify Js AddCommGrpCat.{max u (t + 1)} := inferInstance
  let : Js.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} := inferInstance
  let : ∀ U : AsSmall.{max u (t + 1)} (IntegralOnSlice.Site T none),
      HasSheafify (Js.over U) AddCommGrpCat.{max u (t + 1)} := fun _ ↦ inferInstance
  let : ∀ U : AsSmall.{max u (t + 1)} (IntegralOnSlice.Site T none),
      (Js.over U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    fun _ ↦ inferInstance
  let : ∀ U : AsSmall.{max u (t + 1)} (IntegralOnSlice.Site T none),
      HasSheafify (Js.over U) CommRingCat.{max u (t + 1)} := fun _ ↦ inferInstance
  let : HasDerivedCategory
      (NativeRestriction.NativeModules.{max u (t + 1), max u (t + 1),
        max u (t + 1)} S) := HasDerivedCategory.standard _
  let Rs := NativeRestriction.NativeRings.{max u (t + 1), max u (t + 1),
    max u (t + 1)} S
  let : ∀ U : AsSmall.{max u (t + 1)} (IntegralOnSlice.Site T none),
      HasDerivedCategory (SheafOfModules.{max u (t + 1)} (Rs.over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : HasDerivedCategory
      (ℕᵒᵖ ⥤ NativeRestriction.NativeModules.{max u (t + 1), max u (t + 1),
        max u (t + 1)} S) := HasDerivedCategory.standard _
  let : HasExactLimitsOfShape (Discrete ℕ) (IntegralOnSlice.Mod l E T none) :=
    AlgebraicGeometry.Scheme.ProEt.products_exact.{t, u, 0} T Rg ℕ
  let : HasExactLimitsOfShape (Discrete ℕ)
      (NativeRestriction.NativeModules.{max u (t + 1), max u (t + 1),
        max u (t + 1)} S) :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) H.asEquivalence
  let a' := NativeRestriction.restrictedSection.{max u (t + 1), t + 1,
    max u (t + 1), t, u} (K := Js) F R a
  let μ' := End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom)
  have hμ' (q : ℤ) (U : (AsSmall.{max u (t + 1)} T.ProEt)ᵒᵖ)
      (x : (((H.mapHomologicalComplex (.up ℤ)).obj P).X q).val.obj U) :
      (μ'.asHom.f q).val.app U x = a'.val U • x := hμ q (F.op.obj U) x
  have hComparison := CochainComplex.principalCompletionMap H μ
  let c := hComparison.choose
  have hc := hComparison.choose_spec
  let α := H.mapDerivedCategoryFactors.app (CochainComplex.PrincipalCone.completion μ) ≪≫
    DerivedCategory.Q.mapIso c
  let β := H.mapDerivedCategoryFactors.app P
  have hunit : H.mapDerivedCategory.map
      (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ)) ≫ α.hom =
      β.hom ≫ DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ') := by
    change _ ≫ (H.mapDerivedCategoryFactors.app _).hom ≫ DerivedCategory.Q.map c.hom = _
    simp only [Iso.app_hom]
    rw [← Category.assoc, H.mapDerivedCategoryFactors_hom_naturality,
      Category.assoc, ← Functor.map_comp, hc]
    rfl
  have hl' := (NativeRestriction.smallModelComplete.{t + 1, t, u} R a L).mp
    ((hpred L).mp hL)
  exact homBijection_transport H.mapDerivedCategory α β
    (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ))
    (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ')) hunit
    (smallPrincipalHom S a' ((H.mapHomologicalComplex (.up ℤ)).obj P) μ' hμ' _ hl')

attribute [local semireducible] CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit

private theorem intrinsic_iff_local (T : Scheme.{t}) (K : IntegralOnSlice.D l E T none) :
    Intrinsic l E T K ↔ IntegralPrincipalCone.locallyComplete l E T
      (integralCompletionScalarValue l E T) K := by
  have hrep (P : IntegralOnSlice.Cx l E T none) (e : DerivedCategory.Q.obj P ≅ K) :
      IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T) K ↔
        IsIso (integralKoszulIntrinsicUnit l E T K P e) := by
    have hlocal := (IntegralPrincipalCone.localCriterion l E T
      (integralCompletionScalarValue l E T) (integralScalar_natural l E T)
      P (integralKoszulScalar l E T P)
      (integralKoszulScalar_existsUnique l E T P).exists.choose_spec K e).2
    rw [hlocal]
    simp only [integralKoszulIntrinsicUnit, isIso_comp_left_iff]
    change IsIso (DerivedCategory.Q.map
      (integralKoszulLimitUnitComplex l E T P)) ↔ _
    exact signedFiberUnit _ _ (integralKoszulProductUnit_comp l E T P)
      (integralKoszulLimitUnit_condition l E T P)
      (integralKoszulIntrinsicUnit_condition l E T P)
  refine ⟨fun h ↦ (hrep (DerivedCategory.Q.objPreimage K)
    (DerivedCategory.Q.objObjPreimageIso K)).mpr (h _ _), fun h P e ↦ (hrep P e).mp h⟩

private theorem reflectorFacts (T : Scheme.{t})
    (D : FiniteFieldDatum.{t}) (hl : l ≠ D.p)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) :
    ReflectorAssertions l E T := by
  classical
  let : Fact D.p.Prime := ⟨D.prime⟩
  let := IntegralOnSlice.goodLocalization l E T none
  let : (IntegralOnSlice.qGood l E T none).EssSurj :=
    Localization.essSurj (IntegralOnSlice.qGood l E T none)
      ((HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E T none) (.up ℤ)).inverseImage
        (IntegralOnSlice.Good l E T none).ι)
  have model (H : IntegralOnSlice.D l E T none) :
      ∃ (P : (IntegralOnSlice.Good l E T none).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ H), True :=
    ⟨(IntegralOnSlice.qGood l E T none).objPreimage H,
      (IntegralOnSlice.qGood l E T none).objObjPreimageIso H, trivial⟩
  have crit (H : IntegralOnSlice.D l E T none) :
      IntegralOnSlice.IsComplete l E T none H ↔
        IsIso ((IntegralOnSlice.completionUnit l E T none).app H) := by
    let P := (model H).choose
    let e := (model H).choose_spec.choose
    exact (roosIntrinsicCompletenessEquivalence D.p l (Ne.symm hl) E T d hd H P e).out 1 5
  have localcrit (H : IntegralOnSlice.D l E T none) :
      IsIso ((IntegralOnSlice.completionUnit l E T none).app H) ↔
        IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T) H := by
    let P := (model H).choose
    let e := (model H).choose_spec.choose
    exact (roosIntrinsicCompletenessEquivalence D.p l (Ne.symm hl) E T d hd H P e).out 5 2
  have complete (H : IntegralOnSlice.D l E T none) :
      IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T)
        ((IntegralOnSlice.completion l E T none).obj H) := by
    let P := (model H).choose
    let e := (model H).choose_spec.choose
    let c := (IntegralOnSlice.completion l E T none).mapIso e.symm ≪≫
      (IntegralOnSlice.completionComparison l E T none).app P
    exact integralLocallyComplete_iso l E T _ c.symm
      (integralQuotientLocallyComplete l E T P.obj P.property.1)
  refine ⟨fun H ↦ (intrinsic_iff_local l E T _).mpr (complete H), ?_, crit,
    fun H ↦ (localcrit H).trans (intrinsic_iff_local l E T H).symm⟩
  intro H L hL
  let P := (model H).choose
  let e := (model H).choose_spec.choose
  have hComparison := integralPrincipalConeQuotientComparison l E T P.obj P.property.1
    (integralKoszulScalar l E T P.obj)
    (integralKoszulScalar_existsUnique l E T P.obj).exists.choose_spec
  let c := hComparison.choose
  have hc := hComparison.choose_spec
  let a := c ≪≫ ((IntegralOnSlice.completionComparison l E T none).app P).symm ≪≫
    (IntegralOnSlice.completion l E T none).mapIso e
  have hn : e.hom ≫ (IntegralOnSlice.completionUnit l E T none).app H =
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
        (integralKoszulScalar l E T P.obj)) ≫ a.hom := by
    have he := (IntegralOnSlice.completionUnit l E T none).naturality e.hom
    have hp : (IntegralOnSlice.completionUnit l E T none).app
        (DerivedCategory.Q.obj P.obj) ≫
          (IntegralOnSlice.completionComparison l E T none).hom.app P =
        DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none P.obj) :=
      (IntegralOnSlice.completionUnit_existsUnique l E T none).exists.choose_spec P
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← Category.assoc, hc, ← hp]
    simpa only [Category.assoc, Iso.app_hom, Iso.app_inv,
      Iso.hom_inv_id_app_assoc, Functor.id_map] using he
  have hb := principalHom l E T (integralCompletionScalarValue l E T)
    (integralScalar_natural l E T) P.obj (integralKoszulScalar l E T P.obj)
    (integralKoszulScalar_existsUnique l E T P.obj).exists.choose_spec L
    ((intrinsic_iff_local l E T L).mp hL)
  constructor
  · intro f g hfg
    apply (cancel_epi a.hom).mp
    apply hb.injective
    change _ ≫ (a.hom ≫ f) = _ ≫ (a.hom ≫ g)
    change (IntegralOnSlice.completionUnit l E T none).app H ≫ f =
      (IntegralOnSlice.completionUnit l E T none).app H ≫ g at hfg
    rw [← Category.assoc, ← hn, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) hfg
  · intro f
    obtain ⟨g, hg⟩ := hb.surjective (e.hom ≫ f)
    refine ⟨a.inv ≫ g, ?_⟩
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, hn]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hg

private theorem ordinaryUnit (M : IntegralOnSlice.Mod l E V none) :
    IsIso ((IntegralOpenReduction.ordinaryAdjunction l E e o).unit.app M) := by
  let U := IntegralOpenReduction.openObject e
  have : Mono U.hom := by change Mono e; infer_instance
  have hU (Z : W.ProEt) : Subsingleton (Z ⟶ U) := by
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.hom).mp
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  have : Mono (terminal.from U) := ⟨fun {Z} f g _ ↦ (hU Z).elim f g⟩
  have := SheafOfModules.SubterminalLocal.adj_unit_isIso.{t + 1, t, max u (t + 1)}
    (completedIntegralCommRingSheafUnrestricted l E W) U
  have hu : IsIso ((SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E W) U).unit.app
        (o.integral.functor.obj M)) := inferInstance
  rw [IntegralOpenReduction.ordinaryAdjunction, Adjunction.comp_unit_app]
  have : IsIso (o.integral.toAdjunction.unit.app M) :=
    inferInstanceAs (IsIso (o.integral.unitIso.hom.app M))
  let := hu
  infer_instance

private theorem derivedUnit_formula (P : IntegralOnSlice.Cx l E V none) :
    (IntegralOpenReduction.openAdjunction l E e o).unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
        (((IntegralOpenReduction.ordinaryAdjunction l E e o).mapHomologicalComplex
          (.up ℤ)).unit.app P) ≫
      (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.inv.app _ ≫
      (IntegralOpenReduction.star l E e o).map
        ((IntegralOpenReduction.extension l E e o).mapDerivedCategoryFactors.inv.app P) := by
  simp only [IntegralOpenReduction.openAdjunction,
    SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction,
    Adjunction.localization_unit_app]
  rfl

private theorem derivedUnit (M : IntegralOnSlice.D l E V none) :
    IsIso ((IntegralOpenReduction.openAdjunction l E e o).unit.app M) := by
  have hQ (P : IntegralOnSlice.Cx l E V none) :
      IsIso ((IntegralOpenReduction.openAdjunction l E e o).unit.app
        (DerivedCategory.Q.obj P)) := by
    have : IsIso (((IntegralOpenReduction.ordinaryAdjunction l E e o).mapHomologicalComplex
        (.up ℤ)).unit.app P) := by
      have hn : ∀ n : ℤ, IsIso
          ((((IntegralOpenReduction.ordinaryAdjunction l E e o).mapHomologicalComplex
            (.up ℤ)).unit.app P).f n) := fun n ↦ ordinaryUnit l E e o (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    rw [derivedUnit_formula l E e o P]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso
    (IntegralOpenReduction.openAdjunction l E e o).unit
    (DerivedCategory.Q.objObjPreimageIso M)).mp (hQ (DerivedCategory.Q.objPreimage M))

attribute [local irreducible] IntegralOpenReduction.openAdjunction
  IntegralOpenReduction.ordinaryAdjunction

private theorem restrictedAdjunction
    (hExtension : ∀ M, IntegralOnSlice.IsComplete l E V none M →
      IntegralOnSlice.IsComplete l E W none ((IntegralOpenReduction.shriek l E e o).obj M))
    (hRestriction : ∀ H, IntegralOnSlice.IsComplete l E W none H →
      IntegralOnSlice.IsComplete l E V none ((IntegralOpenReduction.star l E e o).obj H))
    (hUnit : ∀ M : IntegralOnSlice.D l E V none,
      IntegralOnSlice.IsComplete l E V none M →
        IsIso ((IntegralOpenReduction.openAdjunction l E e o).unit.app M)) :
    Nonempty ((completeExtension l E e o hExtension).FullyFaithful) ∧
    ∃ a : completeExtension l E e o hExtension ⊣ completeRestriction l E e o hRestriction,
      (∀ M : Complete l E V,
        (a.unit.app M).hom = (IntegralOpenReduction.openAdjunction l E e o).unit.app M.obj) ∧
      (∀ H : Complete l E W,
        (a.counit.app H).hom =
          (IntegralOpenReduction.openAdjunction l E e o).counit.app H.obj) := by
  let a := (IntegralOpenReduction.openAdjunction l E e o).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι (IntegralOnSlice.IsComplete l E V none))
    (ObjectProperty.fullyFaithfulι (IntegralOnSlice.IsComplete l E W none))
    (L := completeExtension l E e o hExtension)
    (R := completeRestriction l E e o hRestriction) (Iso.refl _) (Iso.refl _)
  have hu (M : Complete l E V) :
      (a.unit.app M).hom =
        (IntegralOpenReduction.openAdjunction l E e o).unit.app M.obj := by
    simpa using (IntegralOpenReduction.openAdjunction l E e o).map_restrictFullyFaithful_unit_app
        (ObjectProperty.fullyFaithfulι (IntegralOnSlice.IsComplete l E V none))
        (ObjectProperty.fullyFaithfulι (IntegralOnSlice.IsComplete l E W none))
        (L := completeExtension l E e o hExtension)
        (R := completeRestriction l E e o hRestriction) (Iso.refl _) (Iso.refl _) M
  have hc (H : Complete l E W) :
      (a.counit.app H).hom =
        (IntegralOpenReduction.openAdjunction l E e o).counit.app H.obj := by
    have h := (IntegralOpenReduction.openAdjunction l E e o).map_restrictFullyFaithful_counit_app
        (ObjectProperty.fullyFaithfulι (IntegralOnSlice.IsComplete l E V none))
        (ObjectProperty.fullyFaithfulι (IntegralOnSlice.IsComplete l E W none))
        (L := completeExtension l E e o hExtension)
        (R := completeRestriction l E e o hRestriction) (Iso.refl _) (Iso.refl _) H
    change (a.counit.app H).hom = 𝟙 _ ≫
      (IntegralOpenReduction.shriek l E e o).map (𝟙 _) ≫
        (IntegralOpenReduction.openAdjunction l E e o).counit.app H.obj at h
    rw [(IntegralOpenReduction.shriek l E e o).map_id] at h
    simpa only [Category.id_comp] using h
  have (M : Complete l E V) : IsIso (a.unit.app M) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    rw [hu]
    exact hUnit M.obj M.property
  have : IsIso a.unit := NatIso.isIso_of_isIso_app _
  exact ⟨⟨a.fullyFaithfulLOfIsIsoUnit⟩, a, hu, hc⟩

private theorem coefficientFacts :
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
    IsAddTorsion (Padic.coefficientExtensionRing l E 1) ∧
    (∃ d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E),
      d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) ∧
    (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l E (n + 1)) ∧
      Function.Injective (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x) ∧
      Function.Exact (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x)
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ∧
      Function.Surjective
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.2.1
  have hf (n : ℕ) := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have : Finite (Padic.coefficientExtensionRing l E 1) := hf 0
  have ht : IsAddTorsion (Padic.coefficientExtensionRing l E 1) := isAddTorsion_of_finite
  let d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E) :=
    { ideal := Ideal.span {Padic.coefficientExtensionUniformizer l E}
      noetherian := inferInstance
      finitelyGenerated := Submodule.fg_span_singleton _
      quotientTorsion := fun x ↦ by
        have : Finite (Padic.coefficientExtensionIntegers l E ⧸
            Ideal.span {Padic.coefficientExtensionUniformizer l E}) := by
          simpa only [Padic.coefficientExtensionRing, Padic.coefficientExtensionIdeal,
            Nat.zero_add, pow_one] using hf 0
        exact (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
      quotientPerfect := fun n hn ↦ by
        obtain ⟨P, hge, hle, hfree, _, hrest⟩ :=
          (AlgebraicGeometry.standard_quotients_perfect l n hn).2 E
        obtain ⟨_, _, _, φ, ε, hε, _, _, _⟩ := hrest
        have hqi : QuasiIso ε := by
          have hiso : IsIso (DerivedCategory.Q.map ε) := by rw [hε]; infer_instance
          exact (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := ε)).1 hiso
        let := HasDerivedCategory.standard
          (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E))
        unfold adicQuotientPerfect
        refine ⟨P, -1, 0, hge, hle, ?_, ⟨(asIso (DerivedCategory.Q.map ε)).symm⟩⟩
        intro i
        have := (hfree i).1
        exact ⟨inferInstance, (hfree i).2⟩
      quotientFinite := hf }
  refine ⟨inferInstance, ht, ⟨d, rfl⟩, ?_⟩
  intro n
  refine ⟨hf n, ?_, ?_, Ideal.Quotient.mk_surjective⟩
  · exact mul_right_injective₀
      (pow_ne_zero (n + 1) (AlgebraicGeometry.uniformizer_ne_zero l E))
  · intro x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩

attribute [local irreducible] IntegralOnSlice.completion IntegralOnSlice.completionUnit
  IntegralOnSlice.completionComparison

/-- Roos completeness, reflection by the actual unit, and the complete open adjunction.

Source: Stacks 099M, 099N (2),(5), 09BN; Bhatt--Scholze 3.5.1--3.5.2, p.24
(blueprint: lem-sf-open-roos-unit-adjunction).

Proof:
1. The extension-integers DVR theorem gives a Noetherian PID R and a nonzero
uniformizer. Finite DVR quotients are finite, hence A_1 is additive torsion.
Multiplication by t^(n+1) is injective with cokernel A_(n+1), giving the displayed
rank-one finite free resolution and every adic-datum hypothesis.
2. Finite type over the field gives Noetherian V,W, hence qcqs. Every open in a
Noetherian scheme is quasi-compact; therefore e is quasi-compact, including the empty open.
3. Weakly-etale localization identifies the open site with the slice. Constant
sections identify each finite coefficient. Quotient maps commute on constants;
immersion inverse image preserves the completed limit and every projection.
4. The ringed Koszul reflector and the unit-compatible completed Koszul/quotient
comparison identify the Koszul unit (u,0) with the actual strict quotient unit.
Strict Roos comparison preserves this augmentation. The Roos/intrinsic equivalence
then gives complete output, the stated Hom bijection and both predicate equivalences.
5. Take a flat-term K-flat representative. Exact ringed restriction preserves it.
The tensor restriction map sends each tensor to the same restricted tensor, commuting
with every quotient and with x mapped to x tensor 1. This yields one strict tower
comparison before localization, natural and independent of representatives.
6. Apply the normalized exact-product strict-limit comparison to that tower map.
Its augmentation clause proves rho composed with e*eta equals eta on e*H.
The reflector Hom bijection makes this unit-compatible natural isomorphism unique.
The pulledRoos model is the strict pulled quotient tower, and pulledUnit retains
both product coordinates. Descent supplies C,c,chi; b identifies it with completion
of restriction, and chi followed by b is exactly the actual completion unit.
Thus restriction preserves completeness and this comparison is invertible on
complete inputs.
7. Exact open extension preserves countable products since e is quasi-compact.
The simultaneous open semilinear tensor model commutes with reductions and their
augmentations. Exact-product strict limits therefore show it preserves completeness.
8. Restrict the actual exact open adjunction to the full complete subcategories.
Its unit and counit are those of the ambient adjunction, as the two formulas assert.
The slice unit is summand insertion, and collapse on the open is its inverse; hence
it is the identity under that section identification. Termwise localization gives
the representative formula below, and invertibility of the unit gives full faithfulness. -/
theorem openRoosUnitAdjunction
    (D : FiniteFieldDatum.{t}) (_hl : l ≠ D.p)
    [V.Over (Spec (CommRingCat.of D.k))] [W.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (W ↘ Spec (CommRingCat.of D.k))]
    [e.IsOver (Spec (CommRingCat.of D.k))] :
    IsNoetherian V ∧ IsNoetherian W ∧ CompactSpace V ∧ CompactSpace W ∧
    QuasiSeparatedSpace V ∧ QuasiSeparatedSpace W ∧ QuasiCompact e ∧
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
    IsAddTorsion (Padic.coefficientExtensionRing l E 1) ∧
    (∃ d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E),
      d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) ∧
    (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l E (n + 1)) ∧
      Function.Injective (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x) ∧
      Function.Exact (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x)
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ∧
      Function.Surjective
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))) ∧
    ReflectorAssertions l E W ∧ ReflectorAssertions l E V ∧
    ∃ o : IntegralOpenReduction.Operations l E e,
      (∀ n : ℕ, IsIso (o.finiteMap n)) ∧ IsIso o.completedMap ∧
      (∀ n : ℕ,
        o.finiteMap (n + 1) ≫
          ((IntegralOpenReduction.sliceSite e).sheafPushforwardContinuous
            CommRingCat.{max u (t + 1)} ((ProEt.topology W).over
              (IntegralOpenReduction.openObject e)) (ProEt.topology V)).map
                (coefficientSequenceCommRingTransition l E V n) =
        ((ProEt.topology W).overPullback CommRingCat.{max u (t + 1)}
          (IntegralOpenReduction.openObject e)).map
            (coefficientSequenceCommRingTransition l E W n) ≫ o.finiteMap n) ∧
      (∃! rho : IntegralOnSlice.completion l E W none ⋙ IntegralOpenReduction.star l E e o ≅
          IntegralOpenReduction.star l E e o ⋙ IntegralOnSlice.completion l E V none,
        ∀ H : IntegralOnSlice.D l E W none,
          (IntegralOpenReduction.star l E e o).map
              ((IntegralOnSlice.completionUnit l E W none).app H) ≫ rho.hom.app H =
            (IntegralOnSlice.completionUnit l E V none).app
              ((IntegralOpenReduction.star l E e o).obj H)) ∧
      (∃ (C : IntegralOnSlice.D l E W none ⥤ IntegralOnSlice.D l E V none)
        (c : IntegralOnSlice.qGood l E W none ⋙ C ≅ pulledRoos l E e o)
        (chi : IntegralOpenReduction.star l E e o ⟶ C)
        (b : C ≅ IntegralOpenReduction.star l E e o ⋙ IntegralOnSlice.completion l E V none),
        (∀ P : (IntegralOnSlice.Good l E W none).FullSubcategory,
          chi.app (DerivedCategory.Q.obj P.obj) ≫ c.hom.app P =
            (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.hom.app P.obj ≫
              DerivedCategory.Q.map (pulledUnit l E e o P.obj)) ∧
        (∀ H : IntegralOnSlice.D l E W none,
          chi.app H ≫ b.hom.app H = (IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H))) ∧
      ∃ (hExtension : ∀ M, IntegralOnSlice.IsComplete l E V none M →
          IntegralOnSlice.IsComplete l E W none
            ((IntegralOpenReduction.shriek l E e o).obj M))
        (hRestriction : ∀ H, IntegralOnSlice.IsComplete l E W none H →
          IntegralOnSlice.IsComplete l E V none
            ((IntegralOpenReduction.star l E e o).obj H)),
        (∀ H : IntegralOnSlice.D l E W none, IntegralOnSlice.IsComplete l E W none H →
          IsIso ((IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H))) ∧
        (∀ M : IntegralOnSlice.D l E V none, IntegralOnSlice.IsComplete l E V none M →
          IsIso ((IntegralOpenReduction.openAdjunction l E e o).unit.app M)) ∧
        (∀ P : IntegralOnSlice.Cx l E V none,
          (IntegralOpenReduction.openAdjunction l E e o).unit.app (DerivedCategory.Q.obj P) =
            DerivedCategory.Q.map
              (((IntegralOpenReduction.ordinaryAdjunction l E e o).mapHomologicalComplex
                (.up ℤ)).unit.app P) ≫
            (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.inv.app _ ≫
            (IntegralOpenReduction.star l E e o).map
              ((IntegralOpenReduction.extension l E e o).mapDerivedCategoryFactors.inv.app P)) ∧
        Nonempty ((completeExtension l E e o hExtension).FullyFaithful) ∧
        ∃ a : completeExtension l E e o hExtension ⊣ completeRestriction l E e o hRestriction,
          (∀ M : Complete l E V,
            (a.unit.app M).hom = (IntegralOpenReduction.openAdjunction l E e o).unit.app M.obj) ∧
          (∀ H : Complete l E W,
            (a.counit.app H).hom =
              (IntegralOpenReduction.openAdjunction l E e o).counit.app H.obj) := by
  classical
  let : IsLocallyNoetherian V :=
    LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (CommRingCat.of D.k))
  let : IsLocallyNoetherian W :=
    LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (CommRingCat.of D.k))
  let : CompactSpace V :=
    QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (CommRingCat.of D.k))
  let : CompactSpace W :=
    QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (CommRingCat.of D.k))
  let : IsNoetherian V := {}
  let : IsNoetherian W := {}
  have harith := coefficientFacts l E
  let d := harith.2.2.1.choose
  have hd := harith.2.2.1.choose_spec
  have rW := reflectorFacts l E W D _hl d hd
  have rV := reflectorFacts l E V D _hl d hd
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, harith.1, harith.2.1,
    ⟨d, hd⟩, harith.2.2.2, rW, rV, ?_⟩
  have hk : IsUnit (l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    have : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  have hu (T : Scheme.{t}) [T.Over (Spec (.of D.k))] : IsUnit (l : Γ(T, ⊤)) := by
    simpa only [map_natCast] using hk.map
      ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (T ↘ Spec (.of D.k)).appTop).hom
  have hOpen := IntegralOpenReduction.integralOpenReductionComparison l E e (hu W) (hu V)
  let SX := hOpen.choose
  have hOpen1 := hOpen.choose_spec
  let SU := hOpen1.choose
  have hOpen2 := hOpen1.choose_spec.choose_spec.choose_spec
  let o := hOpen2.choose
  have hOpen3 := hOpen2.choose_spec
  let tensor := hOpen3.choose
  let cmp := hOpen3.choose_spec.some
  have hDescent := OpenRoosRestriction.restrictionDescent l E e o d hd
  have hf := hDescent.1
  have hc := hDescent.2.1
  have ht := hDescent.2.2.1
  let rho := hDescent.2.2.2.choose
  let c := hDescent.2.2.2.choose_spec.choose
  have hrho := hDescent.2.2.2.choose_spec.choose_spec.1
  have hrep := hDescent.2.2.2.choose_spec.choose_spec.2
  refine ⟨o, hf, hc, ht, ⟨rho, hrho, ?_⟩, ?_, ?_⟩
  · intro sigma hsigma
    exact normalizedComparison_unique (IntegralOpenReduction.star l E e o)
      (IntegralOnSlice.completion l E W none) (IntegralOnSlice.completionUnit l E W none)
      (IntegralOnSlice.completion l E V none) (IntegralOnSlice.completionUnit l E V none)
      (fun H ↦ (rV.2.1 _ _ (rV.1 _)).injective) rho sigma hrho hsigma
  · refine ⟨IntegralOnSlice.completion l E W none ⋙ IntegralOpenReduction.star l E e o,
      c, Functor.whiskerRight (IntegralOnSlice.completionUnit l E W none)
        (IntegralOpenReduction.star l E e o), rho, ?_, hrho⟩
    exact hrep
  · let hExtension : ∀ M, IntegralOnSlice.IsComplete l E V none M →
        IntegralOnSlice.IsComplete l E W none
          ((IntegralOpenReduction.shriek l E e o).obj M) :=
      fun M hM ↦ cmp.extensionComplete ⟨M, hM⟩
    let hRestriction : ∀ H, IntegralOnSlice.IsComplete l E W none H →
        IntegralOnSlice.IsComplete l E V none ((IntegralOpenReduction.star l E e o).obj H) :=
      fun H hH ↦ cmp.restrictionComplete ⟨H, hH⟩
    have ha := restrictedAdjunction l E e o hExtension hRestriction
      (fun M _ ↦ derivedUnit l E e o M)
    exact ⟨hExtension, hRestriction,
      fun H hH ↦ (rV.2.2.1 _).mp (hRestriction H hH),
      fun M _ ↦ derivedUnit l E e o M, derivedUnit_formula l E e o, ha.1, ha.2⟩

end WeilConjectures.OpenRoos
