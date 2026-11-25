/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
public import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionCoefficientData
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientCompletedHorizontal
import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientLevelwiseFlatModels
import WeilConjectures.SmoothPurity.StrictQuotient.StrictTensorAdjointConstructor
import WeilConjectures.SmoothPurity.StrictQuotient.StrictPullbackAdjointConstructor
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
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
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData

/-! # Prescribed strict quotient-expression towers

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E (lemma-pullback-K-flat)
and 07A2 (lemma-tensor-product-K-flat), and the extracted finite-expression argument
of lem-pur-quotient-expression-kflat-normalization
(blueprint: lem-pur-quotient-expression-strict-kflat-towers).

The syntax retains distinct trees. Its interpretation uses the recorded ordinary
sequence-site operations. Natural-number level n denotes positive exponent n+1.
The completed-coefficient tower is localized before evaluation. No normalization
of transition adjoints is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall

universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] MorphismProperty.Over.pullback constantSheaf
  HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint coefficientFiniteReductionModel completedTowerLevelIso

private theorem system_good_iff {W : Scheme.{t}} (K : Complex l E W) :
    SystemGood l E K ↔ ∀ n : ℕ, Good l E K n :=
  (levelwiseFlatModels l E W K).symm

private theorem reduction_flat (W : Scheme.{t})
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hf : ∀ k : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X k)) (n : ℕ) :
    ∀ k : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W)
      (R := integralCoefficientCommRingSheaf l E W n)
      ((((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P).X k) := by
  let R := completedIntegralCommRingSheafUnrestricted l E W
  let := scalarReductionExtensionAdditive l E W n
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (completedIntegralCommRingProjectionUnrestricted l E W n) P
    (scalarReductionExtension l E W n)
    (scalarReductionExistence l E W n).choose_spec.choose
    (scalarReductionExistence l E W n).choose_spec.choose_spec.choose hP
    (fun k ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X k)) (hf k))
  intro k
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso
      (integralCoefficientCommRingSheaf l E W n) _).symm (h.2 k)

private theorem unit_system_good (W : Scheme.{t}) :
    SystemGood l E (𝟙_ (Complex l E W)) := by
  let R := coefficientSequenceCommRingSheaf l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.tensorPreadditive R
  constructor
  · intro T hT k
    exact (hT k).of_iso (ρ_ T).symm
  · intro k
    have hf : ObjectProperty.flat ((𝟙_ (Complex l E W)).X k) := by
      by_cases hk : k = 0
      · subst k
        exact (ObjectProperty.flat).prop_of_iso
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ _)).symm
          (ObjectProperty.prop_unit _)
      · exact (ObjectProperty.flat).prop_of_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (𝟙_ _) k hk)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hf.2

private theorem tensor_system_good {W : Scheme.{t}} (P Q : Complex l E W)
    (hP : SystemGood l E P) (hQ : SystemGood l E Q) :
    SystemGood l E (total l E P Q) := by
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (coefficientSequenceCommRingSheaf l E W) P Q hP.1 hQ.1 hP.2 hQ.2
  exact ⟨h.1, h.2.1⟩

private theorem pull_system_good {V W : Scheme.{t}} (g : V ⟶ W)
    (P : Complex l E W) (hP : SystemGood l E P) :
    SystemGood l E (pull l E g P) := by
  obtain ⟨A, TA, _⟩ := ringedDerived_closed_symmetric_monoidal.{t + 1, t, u,
    (max u (t + 1)) + 1} (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
  obtain ⟨B, TB, _⟩ := ringedDerived_closed_symmetric_monoidal.{t + 1, t, u,
    (max u (t + 1)) + 1} (coefficientSequenceTopology (Scheme.ProEt.topology V))
      (coefficientSequenceCommRingSheaf l E V)
  obtain ⟨K, hK, _⟩ := AmbientPullbackTensor.tensorData_existsUnique l E g none A B TA TB
  exact hK.2.2.2 P hP

private theorem generator_models (W : Scheme.{t})
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hf : ∀ k : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X k)) :
    ∃ (N : Complex l E W)
      (κ : ∀ n : ℕ, level l E N n ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P),
      ∀ {m n : ℕ} (hmn : n ≤ m),
        transition l E N hmn ≫
            ((normalizedDVRModuleRes l E W hmn).mapHomologicalComplex (.up ℤ)).map
              (κ n).hom =
          (κ m).hom ≫ (NatTrans.mapHomologicalComplex
            (coefficientOrdinaryQuotient l E W hmn) (.up ℤ)).app P := by
  obtain ⟨S, _⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  obtain ⟨N, _, κ, _, hκ⟩ := S.reductionModel P hP hf
  exact ⟨N, κ, fun h ↦ hκ _ _ h⟩

private theorem horizontal_identity {W : Scheme.{t}}
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEt)
    (x : M.val.obj (op (n, U))) :
    horizontal l E M (Nat.le_refl n) U x = x := by
  change M.val.presheaf.map (𝟙 (op (n, U))) x = x
  rw [M.val.presheaf.map_id]
  rfl

private theorem horizontal_compose {W : Scheme.{t}}
    (M : coefficientSequenceModules l E W) {a m n : ℕ}
    (ham : m ≤ a) (hmn : n ≤ m) (U : W.ProEt)
    (x : M.val.obj (op (a, U))) :
    horizontal l E M (le_trans hmn ham) U x =
      horizontal l E M hmn U (horizontal l E M ham U x) := by
  unfold horizontal
  have he : (Prod.mkHom (homOfLE (le_trans hmn ham)) (𝟙 U)).op =
      (Prod.mkHom (homOfLE ham) (𝟙 U)).op ≫
        (Prod.mkHom (homOfLE hmn) (𝟙 U)).op := by
    apply Quiver.Hom.unop_inj
    apply Prod.hom_ext
    · exact Subsingleton.elim _ _
    · simp
  rw [he, M.val.presheaf.map_comp]
  rfl

private theorem lifted_transformation_fac
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (L : C ⥤ D) (S : MorphismProperty C) [L.IsLocalization S]
    (F G : C ⥤ T) (FD GD : D ⥤ T)
    [Localization.Lifting L S F FD] [Localization.Lifting L S G GD]
    (τ : F ⟶ G) (M : C) :
    (Localization.liftNatTrans L S F G FD GD τ).app (L.obj M) ≫
        (Localization.Lifting.iso L S G GD).hom.app M =
      (Localization.Lifting.iso L S F FD).hom.app M ≫ τ.app M := by
  rw [Localization.liftNatTrans_app]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem derived_evaluation_model {W : Scheme.{t}} (K : Complex l E W) :
    ∀ n : ℕ, ∃ e : (coefficientSequenceDerivedEvaluation l E W n).obj
              (DerivedCategory.Q.obj K) ≅
            DerivedCategory.Q.obj (level l E K n),
          e.hom = (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
            K := by
  intro n
  exact ⟨(coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app
    K, rfl⟩

private theorem derived_restriction_model {W : Scheme.{t}} (K : Complex l E W) :
    ∃ e : (coefficientSequenceDerivedRestriction l E W).obj
              (DerivedCategory.Q.obj K) ≅
            DerivedCategory.Q.obj (completedTower l E K),
          e.hom = (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app
            K := by
  exact ⟨(coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app
    K, rfl⟩

private theorem completed_evaluation_model {W : Scheme.{t}} (K : Complex l E W) :
    ∀ n : ℕ, ∃ e : (coefficientConstantTowerEvaluation l E W n).obj
              (DerivedCategory.Q.obj (completedTower l E K)) ≅
            (coefficientFiniteDerivedRestriction l E W n).obj
              (DerivedCategory.Q.obj (level l E K n)),
          e.hom = (completedTowerLevelIso l E K n).hom := by
  intro n
  exact ⟨completedTowerLevelIso l E K n, rfl⟩

private theorem completed_horizontal_model {W : Scheme.{t}} (K : Complex l E W) :
    ∀ (k : ℤ) {m n : ℕ} (hmn : n ≤ m) (U : W.ProEtᵒᵖ),
          HEq (fun x ↦
            (((((completedTower l E K).X k).map
              (homOfLE hmn).op).val.app U) x))
            (fun x : (K.X k).val.obj (op (m, U.unop)) ↦
              horizontal l E (K.X k) hmn U.unop x) := by
  intro k m n hmn U
  exact completedHorizontal l E (K.X k) m n hmn U

private theorem completed_localization_model {W : Scheme.{t}} (K : Complex l E W) :
    ∀ {m n : ℕ} (hmn : n ≤ m),
          (completedTowerDerivedTransition l E W hmn).app
                (DerivedCategory.Q.obj (completedTower l E K)) ≫
              (coefficientConstantTowerEvaluationFactors l E W n).hom.app
                (completedTower l E K) =
            (coefficientConstantTowerEvaluationFactors l E W m).hom.app
                (completedTower l E K) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex
                  ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE hmn).op)
                    (.up ℤ)).app (completedTower l E K)) := by
  intro m n hmn
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ))
      (((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op m)).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q) (coefficientConstantTowerEvaluation l E W m) :=
    ⟨coefficientConstantTowerEvaluationFactors l E W m⟩
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ))
      (((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q) (coefficientConstantTowerEvaluation l E W n) :=
    ⟨coefficientConstantTowerEvaluationFactors l E W n⟩
  exact lifted_transformation_fac DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ)) _ _
    (coefficientConstantTowerEvaluation l E W m) (coefficientConstantTowerEvaluation l E W n)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE hmn).op) (.up ℤ))
        DerivedCategory.Q) (completedTower l E K)

private theorem system_comparisons {W : Scheme.{t}} (K : Complex l E W)
    (hK : SystemGood l E K) :
        SystemGood l E K ∧
        (∀ n : ℕ, Good l E K n) ∧
        (∀ (k : ℤ) (U : W.ProEt) (n : ℕ)
          (x : (K.X k).val.obj (op (n, U))),
          horizontal l E (K.X k) (Nat.le_refl n) U x = x) ∧
        (∀ (k : ℤ) (U : W.ProEt) {a m n : ℕ} (ham : m ≤ a) (hmn : n ≤ m)
          (x : (K.X k).val.obj (op (a, U))),
          horizontal l E (K.X k) (le_trans hmn ham) U x =
            horizontal l E (K.X k) hmn U
              (horizontal l E (K.X k) ham U x)) ∧
        (∀ n : ℕ, ∃ e : (coefficientSequenceDerivedEvaluation l E W n).obj
              (DerivedCategory.Q.obj K) ≅
            DerivedCategory.Q.obj (level l E K n),
          e.hom = (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
            K) ∧
        (∃ e : (coefficientSequenceDerivedRestriction l E W).obj
              (DerivedCategory.Q.obj K) ≅
            DerivedCategory.Q.obj (completedTower l E K),
          e.hom = (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app
            K) ∧
        (∀ n : ℕ, ∃ e : (coefficientConstantTowerEvaluation l E W n).obj
              (DerivedCategory.Q.obj (completedTower l E K)) ≅
            (coefficientFiniteDerivedRestriction l E W n).obj
              (DerivedCategory.Q.obj (level l E K n)),
          e.hom = (completedTowerLevelIso l E K n).hom) ∧
        (∀ (k : ℤ) {m n : ℕ} (hmn : n ≤ m) (U : W.ProEtᵒᵖ),
          HEq (fun x ↦
            (((((completedTower l E K).X k).map
              (homOfLE hmn).op).val.app U) x))
            (fun x : (K.X k).val.obj (op (m, U.unop)) ↦
              horizontal l E (K.X k) hmn U.unop x)) ∧
        (∀ {m n : ℕ} (hmn : n ≤ m),
          (completedTowerDerivedTransition l E W hmn).app
                (DerivedCategory.Q.obj (completedTower l E K)) ≫
              (coefficientConstantTowerEvaluationFactors l E W n).hom.app
                (completedTower l E K) =
            (coefficientConstantTowerEvaluationFactors l E W m).hom.app
                (completedTower l E K) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex
                  ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE hmn).op)
                    (.up ℤ)).app (completedTower l E K))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hK
  · exact (system_good_iff l E _).1 (hK)
  · intro k U n x
    exact horizontal_identity l E _ n U x
  · intro k U a m n ham hmn x
    exact horizontal_compose l E _ ham hmn U x
  · exact derived_evaluation_model l E K
  · exact derived_restriction_model l E K
  · exact completed_evaluation_model l E K
  · exact completed_horizontal_model l E K
  · exact completed_localization_model l E K

/-- The strict-system construction and all expression-level comparison data.
Source: Stacks 0G7E, 07A2 and 0941; structural induction on strict expressions.
(blueprint: lem-pur-quotient-expression-strict-kflat-towers).

Proof:
1. Form the ordinary scalar reductions of each input at all positive levels. The
   quotient natural transformations give their semilinear chain maps, commuting
   with differentials and satisfying identity and composition. Realize these strict
   systems on the vertical sequence site. Evaluation yields the isomorphisms κ,
   and the K-flat reduction counit followed by Q(κ.inv) is the generator comparison.
2. Induct on the finite expression tree. Scalar extension preserves K-flatness and
   flat terms at input leaves; a coefficient unit is free in degree zero. Direct-sum
   total tensor preserves both properties by the K-flat total tensor theorem.
   Geometric inverse image uses the coefficient-ring comparison and the ringed
   pullback K-flat theorem. The tensor and pullback transition formulas hold on the
   defining generators and extend by balancing, sums and sheafification.
3. Horizontal identity and composition are the presheaf functor laws. Evaluating
   tensor with an exact system sequence is exact by finite-level flatness, and
   evaluation detects exactness, proving termwise system flatness. For an acyclic
   test complex, evaluation commutes with the total tensor and is acyclic by
   finite-level K-flatness. Detection of acyclicity proves system K-flatness.
4. Evaluation and restriction are exact, so their derived-factor isomorphisms
   compute the displayed complexes. The completed tower retains the same sections
   and horizontal maps after scalar restriction. Its level comparison is exactly
   completedTowerLevelIso, and its derived transition equation is the defining
   localization-lift naturality equation, with no normalization of adjoints.
5. Apply the system K-flat tensor model and its finite-level evaluation comparison
   to the two interpreted expressions. For each allowed geometric arrow, evaluate
   the actual sequence pullback to identify it with the level module pullback on
   generators. Exact inverse image computes its universal left derived functor on
   every complex, giving PullbackComputes and the specified derived-factor map.
-/
theorem quotientExpressionStrictKFlatTowers_towerData
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (_hlZ : ∀ x : Z, IsUnit (l : Z.residueField x))
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ x : Y, IsUnit (l : Y.residueField x))
    (r : ℕ) (P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : ∀ i : Fin r, CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (P i))
    (_hflat : ∀ (i : Fin r) (k : ℤ), SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) ((P i).X k)) :
    ∃ (N : Fin r → Complex l E Y)
      (κ : ∀ (i : Fin r) (n : ℕ), level l E (N i) n ≅
        ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj (P i)),
      (∀ (i : Fin r) {m n : ℕ} (hmn : n ≤ m),
        transition l E (N i) hmn ≫
            ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
              (κ i n).hom =
          (κ i m).hom ≫
            (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
              (.up ℤ)).app (P i)) ∧
      (∀ (i : Fin r) (n : ℕ),
        ∃ e : (coefficientFiniteDerivedExtension l E Y n).obj
            (DerivedCategory.Q.obj (P i)) ≅ DerivedCategory.Q.obj (level l E (N i) n),
          e.hom = (coefficientFiniteReductionModel l E Y (P i) (hP i) n).hom ≫
            DerivedCategory.Q.map (κ i n).inv) ∧
      (∀ (W : Scheme.{t}) (A : Expression h f r W),
        SystemGood l E (A.interpret l E N) ∧
        (∀ n : ℕ, Good l E (A.interpret l E N) n) ∧
        (∀ (k : ℤ) (U : W.ProEt) (n : ℕ)
          (x : ((A.interpret l E N).X k).val.obj (op (n, U))),
          horizontal l E ((A.interpret l E N).X k) (Nat.le_refl n) U x = x) ∧
        (∀ (k : ℤ) (U : W.ProEt) {a m n : ℕ} (ham : m ≤ a) (hmn : n ≤ m)
          (x : ((A.interpret l E N).X k).val.obj (op (a, U))),
          horizontal l E ((A.interpret l E N).X k) (le_trans hmn ham) U x =
            horizontal l E ((A.interpret l E N).X k) hmn U
              (horizontal l E ((A.interpret l E N).X k) ham U x)) ∧
        (∀ n : ℕ, ∃ e : (coefficientSequenceDerivedEvaluation l E W n).obj
              (DerivedCategory.Q.obj (A.interpret l E N)) ≅
            DerivedCategory.Q.obj (level l E (A.interpret l E N) n),
          e.hom = (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
            (A.interpret l E N)) ∧
        (∃ e : (coefficientSequenceDerivedRestriction l E W).obj
              (DerivedCategory.Q.obj (A.interpret l E N)) ≅
            DerivedCategory.Q.obj (completedTower l E (A.interpret l E N)),
          e.hom = (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app
            (A.interpret l E N)) ∧
        (∀ n : ℕ, ∃ e : (coefficientConstantTowerEvaluation l E W n).obj
              (DerivedCategory.Q.obj (completedTower l E (A.interpret l E N))) ≅
            (coefficientFiniteDerivedRestriction l E W n).obj
              (DerivedCategory.Q.obj (level l E (A.interpret l E N) n)),
          e.hom = (completedTowerLevelIso l E (A.interpret l E N) n).hom) ∧
        (∀ (k : ℤ) {m n : ℕ} (hmn : n ≤ m) (U : W.ProEtᵒᵖ),
          HEq (fun x ↦
            (((((completedTower l E (A.interpret l E N)).X k).map
              (homOfLE hmn).op).val.app U) x))
            (fun x : ((A.interpret l E N).X k).val.obj (op (m, U.unop)) ↦
              horizontal l E ((A.interpret l E N).X k) hmn U.unop x)) ∧
        (∀ {m n : ℕ} (hmn : n ≤ m),
          (completedTowerDerivedTransition l E W hmn).app
                (DerivedCategory.Q.obj (completedTower l E (A.interpret l E N))) ≫
              (coefficientConstantTowerEvaluationFactors l E W n).hom.app
                (completedTower l E (A.interpret l E N)) =
            (coefficientConstantTowerEvaluationFactors l E W m).hom.app
                (completedTower l E (A.interpret l E N)) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex
                  ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE hmn).op)
                    (.up ℤ)).app (completedTower l E (A.interpret l E N))))) ∧
      (∀ (W : Scheme.{t}) (A B : Expression h f r W),
        TensorTransitions l E (A.interpret l E N) (B.interpret l E N) ∧
        (∀ S : CoefficientDerivedSystemTensors l E W,
          ∃ (hA : SystemGood l E (A.interpret l E N))
            (hB : SystemGood l E (B.interpret l E N))
            (e : DerivedCategory.Q.obj
                (total (W := W) l E (A.interpret l E N) (B.interpret l E N)) ≅
              S.systemClosed.tensor.obj
                (DerivedCategory.Q.obj (A.interpret l E N),
                  DerivedCategory.Q.obj (B.interpret l E N))),
            e.hom = (CoefficientTensorModels.iso.{u, t+1, t}
              (coefficientSequenceTopology (Scheme.ProEt.topology W))
              (coefficientSequenceCommRingSheaf l E W) S.systemClosed S.systemTensorModel
              (A.interpret l E N) (B.interpret l E N) hA.1 hB.1).hom) ∧
        (∀ (n : ℕ) (S : CoefficientDerivedSystemTensors l E W),
          ∃ (hA : Good l E (A.interpret l E N) n)
            (hB : Good l E (B.interpret l E N) n)
            (e : DerivedCategory.Q.obj
                (level l E (total l E (A.interpret l E N) (B.interpret l E N)) n) ≅
              (S.finiteClosed n).tensor.obj
                (DerivedCategory.Q.obj (level l E (A.interpret l E N) n),
                  DerivedCategory.Q.obj (level l E (B.interpret l E N) n))),
            e.hom = (tensorComparison l E (A.interpret l E N) (B.interpret l E N)
              n S hA hB).hom)) ∧
      (∀ {V W : Scheme.{t}} (g : V ⟶ W), AllowedArrow h f g →
        ∀ A : Expression h f r W,
          PullbackTransitions l E g (A.interpret l E N) ∧
          (∀ n : ℕ, PullbackModel l E g (A.interpret l E N) n ∧
            PullbackComputes l E g (A.interpret l E N) n) ∧
          ∃ e : (integralComparisonDerivedSequencePullback l E g).obj
                (DerivedCategory.Q.obj (A.interpret l E N)) ≅
              DerivedCategory.Q.obj (pull l E g (A.interpret l E N)),
            e.hom = (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app
              (A.interpret l E N)) := by
  classical
  have hex (i : Fin r) := generator_models l E Y (P i) (hP i) (_hflat i)
  choose N κ hτ using hex
  have hN (i : Fin r) : SystemGood l E (N i) := by
    apply (system_good_iff l E _).2
    intro n
    constructor
    · exact SheafOfModules.kFlat_iso_independent
        (integralCoefficientCommRingSheaf l E Y n) (κ i n).symm
        ((coefficientTensorModelPreservation l E Y).1 (P i) (hP i) n)
    · intro k
      exact SheafOfModules.flatOnSite_of_iso
        (integralCoefficientCommRingSheaf l E Y n)
        ((HomologicalComplex.eval _ _ k).mapIso (κ i n).symm)
        (reduction_flat l E Y (P i) (hP i) (_hflat i) n k)
  have hA (W : Scheme.{t}) (A : Expression h f r W) :
      SystemGood l E (A.interpret l E N) := by
    induction A with
    | input i => exact hN i
    | unitY => exact unit_system_good l E Y
    | unitX => exact unit_system_good l E X
    | unitZ => exact unit_system_good l E Z
    | tensor A B hA hB => exact tensor_system_good l E _ _ hA hB
    | pullF A hA => exact pull_system_good l E f _ hA
    | pullH A hA => exact pull_system_good l E h _ hA
    | pullHF A hA => exact pull_system_good l E (h ≫ f) _ hA
  refine ⟨N, κ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i m n hmn
    exact hτ i hmn
  · intro i n
    exact ⟨coefficientFiniteReductionModel l E Y (P i) (hP i) n ≪≫
      DerivedCategory.Q.mapIso (κ i n).symm, rfl⟩
  · intro W A
    exact system_comparisons l E _ (hA W A)
  · intro W A B
    refine ⟨(strictTensorAdjointConstructor l E _ _).1, ?_, ?_⟩
    · intro S
      exact ⟨hA W A, hA W B, CoefficientTensorModels.iso.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) S.systemClosed S.systemTensorModel
        (A.interpret l E N) (B.interpret l E N) (hA W A).1 (hA W B).1, rfl⟩
    · intro n S
      exact ⟨(system_good_iff l E _).1 (hA W A) n,
        (system_good_iff l E _).1 (hA W B) n, tensorComparison l E
          (A.interpret l E N) (B.interpret l E N) n S
          ((system_good_iff l E _).1 (hA W A) n)
          ((system_good_iff l E _).1 (hA W B) n), rfl⟩
  · intro V W g _hg A
    refine ⟨(strictPullbackAdjointConstructor l E g _).1,
      (strictPullbackAdjointConstructor l E g _).2.1, ?_⟩
    exact ⟨(integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.app
        (A.interpret l E N), rfl⟩

/-- Every prescribed expression has its actual strict quotient maps, flat terms and
K-flatness both at each finite level and as a system. All comparisons use these
representatives, and the completed tower retains the actual arrows.

Source: Stacks Project, Tags 0G7E (lemma-pullback-K-flat), 07A2
(lemma-tensor-product-K-flat), and the extracted strict-expression argument
(blueprint: lem-pur-quotient-expression-strict-kflat-towers).

Proof:
1. The constant-coefficient comparison is invertible. Identify the coefficient map
   with the constant-section adjunct, as in prop-weil-pbc-proetale-constant-ring-map.
   Exactness is prop-weil-pbc-proetale-constant-exact. On constants the two quotient
   composites agree; sheafification and adjunction give the coefficient square.
2. Construct all generator reductions simultaneously. On x tensor b the transition
   is x tensor q(b), balanced by q pi_m = pi_n. The unit transition is q.
   Both commute with restrictions and differentials, even for an empty generator list.
3. Tensor sends each total summand u tensor v to t(u) tensor t(v). Balancing moves
   the same scalar q(a) on either side. The degree-zero maps commute with the total
   differential du tensor v + (-1)^p u tensor dv; extend by sums and sheafification.
4. Pullback sends s tensor gamma_m(u) to q(s) tensor gamma_n(t(u)). The coefficient
   square of step 1 gives balancing. Naturality and d(s tensor u)=s tensor du give
   the restriction and chain equations on the prescribed module pullback.
5. Structural induction gives identity and cocycle. They are the quotient equations
   on leaves, the two induction hypotheses on tensors, and q_mn q_km=q_kn together
   with the input induction hypothesis on pullback generators. Equality extends by
   tensor balancing, Kan extension, sheafification and direct sums. Scalar restriction
   composes by the identity on sections, so these are the strict required equations.
6. Induct for flat terms and K-flatness. Generators use ringed pullback along pi_n
   and lem-pur-derived-change-of-rings. Units have one free term. Tensor uses
   lem-pur-kflat-total-tensor-model; geometry uses
   lem-weil-pbc-ringed-pullback-preserves-kflat and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback. No quotient is assumed flat.
7. The strict-system/sequence-site equivalence realizes the constructed complexes.
   Tensor and sums evaluate componentwise because covers are vertical, so the
   actual total tensor evaluates to its displayed level total tensor, with step 3's maps.
8. Tensor any exact system sequence with a term of the prescribed complex: every
   evaluation is exact by level flatness. Componentwise detection gives system
   flatness. For an acyclic test system complex, evaluations of its total tensor are
   acyclic by level K-flatness; componentwise detection gives system K-flatness.
9. Exact derived evaluation is termwise (lem-coef-semilinear-derived-sections).
   The total-tensor theorem on the sequence site computes derived system tensor on
   these K-flat representatives. Exact geometric inverse image computes its derived
   functor on every complex (lem-weil-pbc-exact-functor-derived-functor). Their
   evaluations are exactly step 6's comparisons, with no new resolutions.
10. Restriction along pi_n makes t completed-linear, since q pi_m=pi_n. Localize
    this actual complex of towers. Exact restriction and evaluation carry its
    objects to Res_n QK_n and its arrows to the localized actual transitions, as in
    situation-conventions. This is the coherent tower datum only;
    invertibility of transition adjoints is a separate theorem.
-/
theorem quotientExpressionStrictKFlatTowers
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (_hlZ : ∀ x : Z, IsUnit (l : Z.residueField x))
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ x : Y, IsUnit (l : Y.residueField x))
    (r : ℕ) (P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : ∀ i : Fin r, CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (P i))
    (_hflat : ∀ (i : Fin r) (k : ℤ), SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) ((P i).X k)) :
    (∀ {V W : Scheme.{t}} (g : V ⟶ W), AllowedArrow h f g →
      (∀ n : ℕ, IsIso (constantCoefficientMap l E g n) ∧
        PreservesFiniteLimits (integralOperationsLevelPullback l E g n) ∧
        PreservesFiniteColimits (integralOperationsLevelPullback l E g n)) ∧
      (∀ {m n : ℕ} (hmn : n ≤ m),
        (coefficientInverseImage.{t, u} g).map
            ((coefficientToModel.{t, u} W).map (coefficientFiniteQuotient l E W hmn)) ≫
            constantCoefficientMap l E g n =
          constantCoefficientMap l E g m ≫
            (coefficientToModel.{t, u} V).map (coefficientFiniteQuotient l E V hmn))) ∧
    (∀ (W : Scheme.{t}) {m n : ℕ} (hmn : n ≤ m) (U : W.ProEt)
      (b : (integralCoefficientCommRingSheaf l E W m).obj.obj (op U)),
      horizontal l E ((𝟙_ (Complex l E W)).X 0) hmn U (unitSection l E W m U b) =
        unitSection l E W n U ((coefficientFiniteQuotient l E W hmn).hom.app (op U) b)) ∧
    ∃ (N : Fin r → Complex l E Y)
      (κ : ∀ (i : Fin r) (n : ℕ), level l E (N i) n ≅
        ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj (P i)),
      (∀ (i : Fin r) {m n : ℕ} (hmn : n ≤ m),
        transition l E (N i) hmn ≫
            ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
              (κ i n).hom =
          (κ i m).hom ≫
            (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
              (.up ℤ)).app (P i)) ∧
      (∀ (i : Fin r) (n : ℕ),
        ∃ e : (coefficientFiniteDerivedExtension l E Y n).obj
            (DerivedCategory.Q.obj (P i)) ≅ DerivedCategory.Q.obj (level l E (N i) n),
          e.hom = (coefficientFiniteReductionModel l E Y (P i) (hP i) n).hom ≫
            DerivedCategory.Q.map (κ i n).inv) ∧
      (∀ (W : Scheme.{t}) (A : Expression h f r W),
        SystemGood l E (A.interpret l E N) ∧
        (∀ n : ℕ, Good l E (A.interpret l E N) n) ∧
        (∀ (k : ℤ) (U : W.ProEt) (n : ℕ)
          (x : ((A.interpret l E N).X k).val.obj (op (n, U))),
          horizontal l E ((A.interpret l E N).X k) (Nat.le_refl n) U x = x) ∧
        (∀ (k : ℤ) (U : W.ProEt) {a m n : ℕ} (ham : m ≤ a) (hmn : n ≤ m)
          (x : ((A.interpret l E N).X k).val.obj (op (a, U))),
          horizontal l E ((A.interpret l E N).X k) (le_trans hmn ham) U x =
            horizontal l E ((A.interpret l E N).X k) hmn U
              (horizontal l E ((A.interpret l E N).X k) ham U x)) ∧
        (∀ n : ℕ, ∃ e : (coefficientSequenceDerivedEvaluation l E W n).obj
              (DerivedCategory.Q.obj (A.interpret l E N)) ≅
            DerivedCategory.Q.obj (level l E (A.interpret l E N) n),
          e.hom = (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
            (A.interpret l E N)) ∧
        (∃ e : (coefficientSequenceDerivedRestriction l E W).obj
              (DerivedCategory.Q.obj (A.interpret l E N)) ≅
            DerivedCategory.Q.obj (completedTower l E (A.interpret l E N)),
          e.hom = (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app
            (A.interpret l E N)) ∧
        (∀ n : ℕ, ∃ e : (coefficientConstantTowerEvaluation l E W n).obj
              (DerivedCategory.Q.obj (completedTower l E (A.interpret l E N))) ≅
            (coefficientFiniteDerivedRestriction l E W n).obj
              (DerivedCategory.Q.obj (level l E (A.interpret l E N) n)),
          e.hom = (completedTowerLevelIso l E (A.interpret l E N) n).hom) ∧
        (∀ (k : ℤ) {m n : ℕ} (hmn : n ≤ m) (U : W.ProEtᵒᵖ),
          HEq (fun x ↦
            (((((completedTower l E (A.interpret l E N)).X k).map
              (homOfLE hmn).op).val.app U) x))
            (fun x : ((A.interpret l E N).X k).val.obj (op (m, U.unop)) ↦
              horizontal l E ((A.interpret l E N).X k) hmn U.unop x)) ∧
        (∀ {m n : ℕ} (hmn : n ≤ m),
          (completedTowerDerivedTransition l E W hmn).app
                (DerivedCategory.Q.obj (completedTower l E (A.interpret l E N))) ≫
              (coefficientConstantTowerEvaluationFactors l E W n).hom.app
                (completedTower l E (A.interpret l E N)) =
            (coefficientConstantTowerEvaluationFactors l E W m).hom.app
                (completedTower l E (A.interpret l E N)) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex
                  ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE hmn).op)
                    (.up ℤ)).app (completedTower l E (A.interpret l E N))))) ∧
      (∀ (W : Scheme.{t}) (A B : Expression h f r W),
        TensorTransitions l E (A.interpret l E N) (B.interpret l E N) ∧
        (∀ S : CoefficientDerivedSystemTensors l E W,
          ∃ (hA : SystemGood l E (A.interpret l E N))
            (hB : SystemGood l E (B.interpret l E N))
            (e : DerivedCategory.Q.obj
                (total (W := W) l E (A.interpret l E N) (B.interpret l E N)) ≅
              S.systemClosed.tensor.obj
                (DerivedCategory.Q.obj (A.interpret l E N),
                  DerivedCategory.Q.obj (B.interpret l E N))),
            e.hom = (CoefficientTensorModels.iso.{u, t+1, t}
              (coefficientSequenceTopology (Scheme.ProEt.topology W))
              (coefficientSequenceCommRingSheaf l E W) S.systemClosed S.systemTensorModel
              (A.interpret l E N) (B.interpret l E N) hA.1 hB.1).hom) ∧
        (∀ (n : ℕ) (S : CoefficientDerivedSystemTensors l E W),
          ∃ (hA : Good l E (A.interpret l E N) n)
            (hB : Good l E (B.interpret l E N) n)
            (e : DerivedCategory.Q.obj
                (level l E (total l E (A.interpret l E N) (B.interpret l E N)) n) ≅
              (S.finiteClosed n).tensor.obj
                (DerivedCategory.Q.obj (level l E (A.interpret l E N) n),
                  DerivedCategory.Q.obj (level l E (B.interpret l E N) n))),
            e.hom = (tensorComparison l E (A.interpret l E N) (B.interpret l E N)
              n S hA hB).hom)) ∧
      (∀ {V W : Scheme.{t}} (g : V ⟶ W), AllowedArrow h f g →
        ∀ A : Expression h f r W,
          PullbackTransitions l E g (A.interpret l E N) ∧
          (∀ n : ℕ, PullbackModel l E g (A.interpret l E N) n ∧
            PullbackComputes l E g (A.interpret l E N) n) ∧
          ∃ e : (integralComparisonDerivedSequencePullback l E g).obj
                (DerivedCategory.Q.obj (A.interpret l E N)) ≅
              DerivedCategory.Q.obj (pull l E g (A.interpret l E N)),
            e.hom = (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app
              (A.interpret l E N)) := by
  exact ⟨quotientExpressionStrictKFlatTowers_constantMaps l E h f _hlZ _hlX _hlY r P hP _hflat,
    quotientExpressionStrictKFlatTowers_unitTransitions l E h f _hlZ _hlX _hlY r P hP _hflat,
    quotientExpressionStrictKFlatTowers_towerData l E h f _hlZ _hlX _hlY r P hP _hflat⟩

end WeilConjectures.StrictQuotient
