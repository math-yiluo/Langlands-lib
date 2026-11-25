/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitFoundations
public import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarRoosComparisonUnique

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
import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarRoosTensorNormalization
import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarRoosNormalization
import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeRealization
import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportNativeEffectivity
import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitCompletedComparison
import all WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.CategoryTheory.RoosTensor.RoosTensorNormalization
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientModels
import all WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree

/-! # Normalized compact-support scalar limits and their finite reductions

Source: Stacks Tags 0941, 07A6 and 0GL6; auxiliary comparison Steps 5--6
(blueprint: lem-pur-compact-support-scalar-limit-reduction).

The helpers specify the total limit and its projections, the tensor and cofinal
maps, completed/constant coefficient transports, and projection-adjoint reductions.
The main theorem is `compactSupportScalarLimitReduction`; strict augmentation
preservation is `scalarLimitArrow_augmentation`.

All limits below are total right derived limits of strict towers. Natural-number
index `n` denotes positive exponent `n+1`, including in arithmetic subsequences.
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

attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] scalarCompletion

/-- The unit-normalized Roos presentation of the actual total right-derived limit.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarRoosComparison (W : Scheme.{u}) :=
  (scalarRoosComparison_existsUnique l E W).choose

attribute [local irreducible] scalarRoosComparison roosAdditiveComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
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

section Augmentation

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] scalarLimitTensor scalarLimitCofinalInverse baseTensorCounit
  support arrow

end Augmentation

section Geometry

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

end Geometry
end WeilConjectures.PurStrictScalar
