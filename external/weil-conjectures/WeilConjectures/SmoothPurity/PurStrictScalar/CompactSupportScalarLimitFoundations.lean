/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportStrictScalarMate
public import WeilConjectures.SixFunctors.Compact.CompactSupportNormalizedRealization
public import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
public import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportRoosCofinality
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.Strict.StrictRoosAdditiveComparison
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientModels
import WeilConjectures.SmoothPurity.PurStrictScalar.CompletedScalarLocalizationBalancing
import all WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarLimitTensorKInjective
import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarLimitRestrictionKInjective
import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarLimitRestrictionLimits

/-! # Foundations of normalized compact-support scalar limits

The canonical scalar limits, arithmetic restriction, completed coefficient
balancing, and native compact-support limit comparisons.
Source: Stacks Tags 0941, 06YY and 099L
(blueprint: def-pur-compact-support-scalar-limit-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme hiding Modules
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

attribute [local irreducible] constantMap completedCoefficientMap

private theorem scalarTensor_preservesLimits (W : Scheme.{u})
    (J₀ : Type*) [Category J₀]
    [HasLimitsOfShape J₀
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W)]
    [HasLimitsOfShape J₀
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W)] :
    PreservesLimitsOfShape J₀ (pbcExtend (constantMap l E F i W)) := by
  classical
  let := i.toAlgebra
  let := (integralScalarIntegerInclusion l E F i).toAlgebra
  obtain ⟨b⟩ := WeilConjectures.integral_basis l E F i
  let : Algebra (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (Padic.coefficientExtensionIntegers l F) :=
    ULift.algebra' (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l F)
  let A : CommRingCat.{u + 1} :=
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  let B : CommRingCat.{u + 1} :=
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F))
  let J := ProEt.topology W
  let e := @CategoryTheory.basisSheafIso.{u + 1, u, u + 1} W.ProEt inferInstance J
    (integralCoefficientRingSheafify.{u, u} W)
    (inferInstance : J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (integralCoefficientAbSheafify.{u, u} W)
    (integralCoefficientAbLocallyBijective.{u, u} W)
    A B inferInstance (Module.finrank E F) (WeilConjectures.liftedBasis.{u, u} b)
  have : (pbcRestrict (constantMap l E F i W)).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties (constantMap l E F i W)).2.2
  have : PreservesLimitsOfShape J₀
      (pbcExtend (constantMap l E F i W) ⋙ pbcRestrict (constantMap l E F i W)) :=
    preservesLimitsOfShape_of_natIso
      (ordinaryCoordinates W (constantMap l E F i W) (Module.finrank E F)
        (by unfold constantMap; exact e.symm)).symm
  have : (pbcRestrict (constantMap l E F i W)).IsRightAdjoint :=
    (pbcScalarAdjunction (constantMap l E F i W)).isRightAdjoint
  have : ReflectsLimitsOfShape J₀ (pbcRestrict (constantMap l E F i W)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (pbcRestrict (constantMap l E F i W))

/-- Additivity of the actual inverse-limit functor follows from its finite products.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarLimit_additive (W : Scheme.{u}) :
    (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
      Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The specified total derived inverse limit on discrete integral strict towers.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
abbrev scalarLimit (W : Scheme.{u}) :=
  (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
    Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W).rightDerivedFunctor

/-- Ordinary restriction of the limit cone to the arithmetic subsequence.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitRestrictionOrdinary (W : Scheme.{u}) (e : ℕ) :
    (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤ _) ⟶
      ordinarySubsequence l E W e ⋙ lim where
  app K := limit.pre K (CategoryTheory.StrictTowerArithmetic.index e)
  naturality _K _L a := limit.map_pre a (CategoryTheory.StrictTowerArithmetic.index e)

/-- Canonical derived arithmetic restriction, with the ordinary cone normalization.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitRestriction (W : Scheme.{u}) (e : ℕ) :
    scalarLimit l E W ⟶ subsequence l E W e ⋙ scalarLimit l E W :=
  Functor.rightDerivedPullback (ordinarySubsequence l E W e)
    (scalarLimitRestrictionOrdinary l E W e)

/-- Finite-free integral scalar extension is exact and preserves strict K-injectives.
Source: Stacks 03CY, 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: one integral basis identifies restricted tensor with a finite biproduct,
including all tower transitions. The dual basis makes tensor a right adjoint of
an exact functor. The exact-left-adjoint criterion gives preservation of K-injectives. -/
theorem scalarLimitTensor_exact (W : Scheme.{u}) :
    PreservesFiniteLimits (pbcExtend (constantMap l E F i W)) ∧
      PreservesFiniteColimits (pbcExtend (constantMap l E F i W)) ∧
      PreservesLimitsOfShape ℕᵒᵖ (pbcExtend (constantMap l E F i W)) ∧
      (tensor l E F i W).PreservesKInjectiveComplexes := by
  have h := baseTensor_exact l E F i W
  have hlim := scalarTensor_preservesLimits l E F i W (ℕᵒᵖ)
  exact ⟨h.1, h.2, hlim, scalarTensor_preservesKInjective l E F i W⟩

/-- The canonical tensor/product comparison on total derived limits. Its factors
are the unit-normalized derived-composite comparisons and ordinary limit comparison.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitTensor (W : Scheme.{u}) :
    scalarLimit l E W ⋙ baseTensor l E F i W ≅
      T l E F i W ⋙ scalarLimit l F W :=
  haveI := (scalarLimitTensor_exact l E F i W).1
  haveI := (scalarLimitTensor_exact l E F i W).2.1
  haveI := (scalarLimitTensor_exact l E F i W).2.2.1
  haveI := (scalarLimitTensor_exact l E F i W).2.2.2
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤ _)
      (pbcExtend (constantMap l E F i W))).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (preservesLimitNatIso (J := ℕᵒᵖ) (pbcExtend (constantMap l E F i W))) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso (tensor l E F i W)
      (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W ⥤ _)

private theorem scalarIndex_initial (e : ℕ) (he : 1 ≤ e) :
    (CategoryTheory.StrictTowerArithmetic.index e).Initial := by
  let ceil : ℕᵒᵖ ⥤ ℕᵒᵖ :=
    (show ℕ →o ℕ from
      { toFun := fun n ↦ n / e
        monotone' := fun _ _ h ↦ Nat.div_le_div_right h }).monotone.functor.op
  have hgc (a n : ℕ) : a / e ≤ n ↔ a ≤ e * (n + 1) - 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (show 0 < e from he)]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  let adj : CategoryTheory.StrictTowerArithmetic.index e ⊣ ceil :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun n a ↦
          { toFun := fun f ↦ (homOfLE ((hgc a.unop n.unop).2 f.unop.le)).op
            invFun := fun f ↦ (homOfLE ((hgc a.unop n.unop).1 f.unop.le)).op
            left_inv := fun _ ↦ Subsingleton.elim _ _
            right_inv := fun _ ↦ Subsingleton.elim _ _ } }
  exact Functor.initial_of_adjunction adj

/-- Arithmetic restriction is invertible for every full tower and positive e.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: use compactSupportRoosCofinality on a simultaneous strict K-injective
resolution. Its selection/block map is a quasi-isomorphism and is the restriction
of the ordinary limit cone under strictRoosComparison. Cancel the derived units. -/
theorem scalarLimitRestriction_isIso (W : Scheme.{u}) (e : ℕ) (he : 1 ≤ e) :
    IsIso (scalarLimitRestriction l E W e) := by
  let A := Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W
  let P := ordinarySubsequence l E W e
  let H : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤ A := lim
  let α := scalarLimitRestrictionOrdinary l E W e
  have := scalarIndex_initial e he
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    change IsIso (limit.pre K (CategoryTheory.StrictTowerArithmetic.index e))
    infer_instance
  have : P.PreservesKInjectiveComplexes := subsequence_preservesKInjective l E W e he
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  obtain ⟨I, hI, ⟨uI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have hi : IsIso ((Functor.rightDerivedPullback P α).app (DerivedCategory.Q.obj I)) := by
    have h := Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app' P α I
    have : IsIso (H.rightDerivedFunctorUnitQ I) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have : IsIso (H.rightDerivedFunctorUnitQ ((P.mapHomologicalComplex (.up ℤ)).obj I)) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have : IsIso ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I) := by
      have (n : ℤ) : IsIso (((NatTrans.mapHomologicalComplex α (.up ℤ)).app I).f n) :=
        inferInstanceAs (IsIso (α.app (I.X n)))
      exact HomologicalComplex.Hom.isIso_of_components _
    have : IsIso (H.rightDerivedFunctorUnitQ I ≫
        (Functor.rightDerivedPullback P α).app (DerivedCategory.Q.obj I)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (H.rightDerivedFunctorUnitQ I) _
  have hn := (Functor.rightDerivedPullback P α).naturality uI.hom
  have : IsIso ((Functor.rightDerivedPullback P α).app M ≫
      (P.mapDerivedCategory ⋙ H.rightDerivedFunctor).map uI.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right ((Functor.rightDerivedPullback P α).app M)
    ((P.mapDerivedCategory ⋙ H.rightDerivedFunctor).map uI.hom)

/-- The inverse of the specific arithmetic restriction, using its cofinality theorem.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitCofinalInverse (W : Scheme.{u}) (e : ℕ) (he : 1 ≤ e)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
    (scalarLimit l E W).obj ((subsequence l E W e).obj K) ⟶
      (scalarLimit l E W).obj K :=
  haveI := scalarLimitRestriction_isIso l E W e he
  inv ((scalarLimitRestriction l E W e).app K)

private theorem restriction_preservesLimits
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} α) := by
  let U := SheafOfModules.toSheaf.{u + 1} R
  let e : SheafOfModules.restrictScalars α ⋙ U ≅ SheafOfModules.toSheaf.{u + 1} S :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars α ⋙ U) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

private theorem restriction_preservesColimits
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} α) := by
  let U := SheafOfModules.toSheaf.{u + 1} R
  let e : SheafOfModules.restrictScalars α ⋙ U ≅ SheafOfModules.toSheaf.{u + 1} S :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars α ⋙ U) :=
    preservesFiniteColimits_of_natIso e.symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ U

/-- Restriction to constant scalars preserves finite limits, detected on abelian
sheaves. Source: Stacks 03DA
(blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarConstantRestriction_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (constantRestriction l E W) :=
  restriction_preservesLimits (integralConstantToCompletionOfUniverses l E W)

/-- Restriction to constant scalars preserves finite colimits, detected on abelian
sheaves. Source: Stacks 03DA
(blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarConstantRestriction_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (constantRestriction l E W) :=
  restriction_preservesColimits (integralConstantToCompletionOfUniverses l E W)

/-- Additivity of the specified constant restriction.
Source: Stacks 03DA (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarConstantRestriction_additive (W : Scheme.{u}) :
    (constantRestriction l E W).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The exact constant restriction on the fixed derived module categories.
Source: Stacks 03DA (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarConstantRestriction (W : Scheme.{u}) :=
  (constantRestriction l E W).mapDerivedCategory

/-- The ordinary scalar/completion composite is additive.
Source: Stacks 03DA (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarCompletionTarget_additive (W : Scheme.{u}) :
    (pbcExtend (completedCoefficientMap l E F i W) ⋙ constantRestriction l F W).Additive := by
  infer_instance

/-- Ordinary scalar/completion balancing, determined on every local pure tensor.
Source: Stacks 03EK, 099L (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: an integral basis makes completed scalar extension a finite biproduct.
The displayed pure-tensor map and its inverse descend through tensor relations
and sheafification. Local pure tensors generate, proving uniqueness and naturality. -/
theorem scalarCompletionOrdinary_existsUnique (W : Scheme.{u}) :
    ∃! β : constantRestriction l E W ⋙ pbcExtend (constantMap l E F i W) ≅
        pbcExtend (completedCoefficientMap l E F i W) ⋙ constantRestriction l F W,
      ∀ (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
        (b : ((constants l F).ring W).obj.obj U) (x : M.val.obj U),
        (β.hom.app M).val.app U
            (pbcTensorSection (constantMap l E F i W)
              ((constantRestriction l E W).obj M) U b x) =
          pbcTensorSection (completedCoefficientMap l E F i W) M U
            (((integralConstantToCompletionOfUniverses l F W).hom.app U) b) x := by
  exact compactSupportCoefficientModels_ordinary l E F i W

/-- The ordinary balancing map with its prescribed pure-tensor normalization.
Source: Stacks 03EK (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarCompletionOrdinary (W : Scheme.{u}) :=
  (scalarCompletionOrdinary_existsUnique l E F i W).choose

/-- Termwise localization of the already fixed ordinary balancing.
Source: Stacks 06YY (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarCompletionOrdinaryComplex (W : Scheme.{u}) :
    (constantRestriction l E W ⋙ pbcExtend (constantMap l E F i W)).mapHomologicalComplex
        (.up ℤ) ≅
      (pbcExtend (completedCoefficientMap l E F i W) ⋙
        constantRestriction l F W).mapHomologicalComplex (.up ℤ) :=
  haveI := scalarConstantRestriction_additive l F W
  haveI := scalarCompletionTarget_additive l E F i W
  NatIso.mapHomologicalComplex (scalarCompletionOrdinary l E F i W) (.up ℤ)

/-- The scalar/completion comparison is fixed on all complex counits, before
passing to finite levels. It therefore cannot be an independently chosen iso.
Source: Stacks 06YY, 099L (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: finite freeness makes both ordinary tensors exact. Localize the prescribed
ordinary balancing; the universal derived counits give the equation and uniqueness. -/
theorem scalarCompletion_existsUnique (W : Scheme.{u}) :
    ∃! χ : scalarConstantRestriction l E W ⋙ baseTensor l E F i W ≅
        pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
          scalarConstantRestriction l F W,
      ∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
        χ.hom.app (DerivedCategory.Q.obj P) ≫
            (constantRestriction l F W).mapDerivedCategory.map
              (pbcComplexCounit (completedCoefficientMap l E F i W) P) ≫
            (constantRestriction l F W).mapDerivedCategoryFactors.hom.app
              (((pbcExtend (completedCoefficientMap l E F i W)).mapHomologicalComplex
                (.up ℤ)).obj P) =
          (baseTensor l E F i W).map
              ((constantRestriction l E W).mapDerivedCategoryFactors.hom.app P) ≫
            baseTensorCounit l E F i W
              (((constantRestriction l E W).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((scalarCompletionOrdinaryComplex l E F i W).hom.app P) := by
  simpa only [scalarConstantRestriction, scalarCompletionOrdinaryComplex] using
    completedScalarBalancing_existsUnique l E F i W (scalarCompletionOrdinary l E F i W)

/-- The quotient-compatible ordinary/strict scalar comparison χ.
Source: Stacks 06YY (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarCompletion (W : Scheme.{u}) :=
  (scalarCompletion_existsUnique l E F i W).choose

attribute [local irreducible] scalarCompletion

attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived

/-- Exact countable products on this specific constant coefficient category.
Source: blueprint proposition-exact-products--1
(blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarRoos_exactProducts (W : Scheme.{u}) :
    HasExactLimitsOfShape (Discrete ℕ)
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :=
  ProEt.products_exact.{u, u, 0} W _ ℕ

end WeilConjectures.PurStrictScalar
