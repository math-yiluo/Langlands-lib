/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
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
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
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
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import all WeilConjectures.SixFunctors.Supporting.CompleteResidueCohomologyBounds
import all WeilConjectures.SixFunctors.CompleteLiftedTopCell.CompleteLiftedTopCellTriangle
import all WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
import WeilConjectures.SixFunctors.Completed.CompletedFreeCoproductReduction
import all WeilConjectures.SixFunctors.Supporting.ProjectiveCohomologySplitModel
import all WeilConjectures.SixFunctors.Supporting.PrescribedResidueCellConeModel
import all WeilConjectures.SixFunctors.Supporting.FieldTorAmplitude
import all WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueCoefficientIso
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

/-! # A lifted top residue cell and its complete cone

Source: Stacks Project, proetale.tex, Tags 09C2 and 09C3, final induction paragraph;
derived.tex, Tag 014E (blueprint: lem-sf-complete-top-residue-cell-cone).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionExtension

attribute [-instance] integralCoefficientAbLocallyBijective integralCoefficientAbSheafify
  GrothendieckTopology.hasSheafify_of_essentiallySmall
  sfResidueAbSheafify sfResidueAbLocallyBijective sfResidueSiteSmall
  sfResidueDerived sfResidueSliceDerived sfResidueAnySliceDerived
  sfResidueSliceAbSheafify sfResidueSliceAbLocallyBijective sfResidueSliceSmall

/-- The published locally bijective equivalences at the site's module universe.
Source: Stacks 00W1 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance topCellAbLocallyBijective (Y : Scheme.{u}) :
    (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Y

/-- The literal finite zero-differential sum of the indicated single-term complexes.
Source: Stacks 09C3, split residue model
(blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellSplitComplex (C : Type v) [Category.{w} C] [Abelian C]
    (F : ℕ → C) (a b : ℤ) (r : ℤ → ℕ) : CochainComplex C ℤ :=
  ∐ fun q : Set.Icc a b ↦ (HomologicalComplex.single C (.up ℤ) q.val).obj (F (r q.val))

/-- Inclusion in the literal finite split complex, using its finite coproduct.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellSplitInclusion (C : Type v) [Category.{w} C] [Abelian C]
    (F : ℕ → C) (a b : ℤ) (r : ℤ → ℕ) (q : Set.Icc a b) :
    (HomologicalComplex.single C (.up ℤ) q.val).obj (F (r q.val)) ⟶
      topCellSplitComplex C F a b r :=
  Sigma.ι (fun j : Set.Icc a b ↦
    (HomologicalComplex.single C (.up ℤ) j.val).obj (F (r j.val))) q

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Mathlib's abelian category at the explicit completed-coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 3000) topCellSourceAbelian :
    Abelian (scalarReductionSource.{u, u} l E X) :=
  @SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
    (integralCoefficientAbSheafify.{u, u} X)
    (integralCoefficientAbLocallyBijective.{u, u} X)

/-- Mathlib's abelian category at the explicit residue-coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 3000) topCellTargetAbelian :
    Abelian (scalarReductionTarget.{u, u} l E X 0) :=
  @SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
    (integralCoefficientSheaf.{u, u} l E X 0)
    (integralCoefficientAbSheafify.{u, u} X)
    (integralCoefficientAbLocallyBijective.{u, u} X)

/-- Standard localization at the explicit completed-coefficient sizes.
Source: Stacks 05RU (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 2000) topCellSourceDerived :
    HasDerivedCategory (scalarReductionSource.{u, u} l E X) :=
  scalarReductionSourceDerived.{u, u} l E X

/-- Standard localization at the explicit residue-coefficient sizes.
Source: Stacks 05RU (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 2000) topCellTargetDerived :
    HasDerivedCategory (scalarReductionTarget.{u, u} l E X 0) :=
  scalarReductionTargetDerived.{u, u} l E X 0

/-- Exact restriction, at the specified coefficient sizes.
Source: Stacks 03CZ (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 3000) topCellRestrictionLimits :
    PreservesFiniteLimits (scalarReductionRestriction.{u, u} l E X 0) :=
  scalarReductionRestrictionLimits.{u, u} l E X 0

/-- Exact restriction, at the specified coefficient sizes.
Source: Stacks 03CZ (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 3000) topCellRestrictionColimits :
    PreservesFiniteColimits (scalarReductionRestriction.{u, u} l E X 0) :=
  scalarReductionRestrictionColimits.{u, u} l E X 0

/-- The actual finite free module over the completed coefficient sheaf.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
abbrev topCellIntegralFree (r : ℕ) : scalarReductionSource.{u, u} l E X :=
  @SheafOfModules.free X.ProEt inferInstance (ProEt.topology X)
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
    (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
    (integralCoefficientAbLocallyBijective.{u, u} X)
    (ULift.{u + 1} (Fin r))

/-- The actual finite free module over the constant residue ring sheaf.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
abbrev topCellResidueFree (r : ℕ) : scalarReductionTarget.{u, u} l E X 0 :=
  @SheafOfModules.free X.ProEt inferInstance (ProEt.topology X)
    (integralCoefficientSheaf.{u, u} l E X 0)
    (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
    (integralCoefficientAbLocallyBijective.{u, u} X)
    (ULift.{u + 1} (Fin r))

/-- Coefficient reduction on finite free modules, fixed on every standard generator.
The restricted residue module has the same underlying global sections.
Source: Stacks 09C3, quotient of the completed coefficient sheaf
(blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellFreeQuotient (r : ℕ) : topCellIntegralFree.{u} l E X r ⟶
    (scalarReductionRestriction.{u, u} l E X 0).obj (topCellResidueFree.{u} l E X r) :=
  (@SheafOfModules.freeHomEquiv X.ProEt inferInstance (ProEt.topology X)
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
    (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
    (integralCoefficientAbLocallyBijective.{u, u} X)
    ((scalarReductionRestriction.{u, u} l E X 0).obj (topCellResidueFree.{u} l E X r))
    (ULift.{u + 1} (Fin r))).symm
      (fun i ↦ PresheafOfModules.sectionsMk
        (fun U ↦ (@SheafOfModules.freeSection X.ProEt inferInstance (ProEt.topology X)
          (integralCoefficientSheaf.{u, u} l E X 0)
          (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
          (integralCoefficientAbLocallyBijective.{u, u} X) (ULift.{u + 1} (Fin r)) i).val U)
        (fun _ _ f ↦ PresheafOfModules.sections_property
          (@SheafOfModules.freeSection X.ProEt inferInstance (ProEt.topology X)
            (integralCoefficientSheaf.{u, u} l E X 0)
            (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
            (integralCoefficientAbLocallyBijective.{u, u} X) (ULift.{u + 1} (Fin r)) i) f))

/-- The canonical comparison from the derived reduction of a shifted finite free
module to its residue free module. It is the adjoint of coefficient reduction,
using the normalized scalar-extension adjunction and the exact-restriction comparison.
Source: Stacks 06YY, 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellReductionComparison (r : ℕ) (b : ℤ) :
    (scalarReductionDerivedExtension.{u, u} l E X 0).obj
      ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree.{u} l E X r)) ⟶
    (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X 0) b).obj
      (topCellResidueFree.{u} l E X r) :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E X 0).choose.homEquiv _ _).symm
    ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).map
        (topCellFreeQuotient.{u} l E X r) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (scalarReductionRestriction.{u, u} l E X 0) (.up ℤ) b).inv.app
            (topCellResidueFree.{u} l E X r)) ≫
      (scalarReductionRestriction.{u, u} l E X 0).mapDerivedCategoryFactors.inv.app
        ((HomologicalComplex.single (scalarReductionTarget.{u, u} l E X 0) (.up ℤ) b).obj
          (topCellResidueFree.{u} l E X r)))

/-- The split residue model over an integer interval, using the existing single-term
and coproduct constructions. Source: Stacks 09C3
(blueprint: lem-sf-complete-top-residue-cell-cone). -/
abbrev topCellResidueSplit (a b : ℤ) (r : ℤ → ℕ) :=
  @topCellSplitComplex (scalarReductionTarget.{u, u} l E X 0) inferInstance
    (topCellTargetAbelian.{u} l E X)
    (topCellResidueFree.{u} l E X) a b r

/-- Inclusion of one summand of the literal split residue complex.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellResidueInclusion (a b : ℤ) (r : ℤ → ℕ) (q : Set.Icc a b) :
    (HomologicalComplex.single (scalarReductionTarget.{u, u} l E X 0)
      (.up ℤ) q.val).obj (topCellResidueFree.{u} l E X (r q.val)) ⟶
    topCellResidueSplit.{u} l E X a b r :=
  @topCellSplitInclusion (scalarReductionTarget.{u, u} l E X 0) inferInstance
    (topCellTargetAbelian.{u} l E X) (topCellResidueFree.{u} l E X) a b r q

/-- The reduced cell map after the specified free-generator comparison.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellReducedMap (r : ℕ) (b : ℤ)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (e : (scalarReductionDerivedExtension.{u, u} l E X 0).obj
      ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree.{u} l E X r)) ≅
      (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X 0) b).obj
        (topCellResidueFree.{u} l E X r))
    (f : (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
      (topCellIntegralFree.{u} l E X r) ⟶ M) :=
  e.inv ≫ (scalarReductionDerivedExtension.{u, u} l E X 0).map f

attribute [local instance 6000] topCellAbLocallyBijective
attribute [local instance] scalarReductionExtensionAdditive

private def topCellFreeProductIso (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (n : ℕ) : SheafOfModules.free (R := R) (ULift.{u + 1} (Fin n)) ≅
      ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit R := by
  let : HasFiniteBiproducts (SheafOfModules.{u + 1} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact Sigma.reindex Equiv.ulift (fun _ : Fin n ↦ SheafOfModules.unit R) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin n ↦ SheafOfModules.unit R)).symm ≪≫
    biproduct.isoProduct (fun _ : Fin n ↦ SheafOfModules.unit R)

private theorem topCell_complete_zero
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hc : IsDerivedCompleteUnrestricted.{u, u} l E X K)
    (hzero : IsZero ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) :
    IsZero K := by
  classical
  obtain ⟨D, hl, P₀, G, q, hq, e₀, hprod, δ₀, hlim⟩ := hc
  obtain ⟨P, e, hP, hflat, c, hc, i, hi, htri⟩ := strictDvrReductionTriangles.{u, u} l E X K
  have hres : IsZero (strictDvrDerivedReduction.{u, u} l E X K 0) :=
    (scalarReductionRestriction.{u, u} l E X 0).mapDerivedCategory.map_isZero hzero
  have hz : ∀ n, IsZero (strictDvrDerivedReduction.{u, u} l E X K n) := by
    intro n
    induction n with
    | zero => exact hres
    | succ n hn =>
      obtain ⟨hw, hex, δ, hT⟩ := htri n
      exact Triangle.isZero₂_of_isZero₁₃ _ hT hres hn
  let C := scalarReductionSource.{u, u} l E X
  let Q := DerivedCategory.Q (C := C)
  obtain ⟨T, s, hs, t, hst⟩ := DerivedCategory.right_fac (e.hom ≫ e₀.inv)
  let : IsIso (Q.map s) := hs
  have ht : Q.map t = Q.map s ≫ e.hom ≫ e₀.inv := by
    rw [hst, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have : IsIso (Q.map t) := by rw [ht]; infer_instance
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hs
  have : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp inferInstance
  obtain ⟨S, z, hS, _, hzq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) T
  have : QuasiIso z := hzq
  have hsz : CochainComplex.IsKFlatResolutionIndependentCoefficients.{u + 1, u, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (z ≫ s) :=
    ⟨inferInstance, hS⟩
  have htz : CochainComplex.IsKFlatResolutionIndependentCoefficients.{u + 1, u, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (z ≫ t) :=
    ⟨inferInstance, hS⟩
  have hz₀ (n : ℕ) : IsZero (Q.obj (integralTowerComplex.{0, u, u} l E X D hl n P₀)) := by
    let c := (unrestrictedTowerComparison.{u, u} l E X n (z ≫ s) (𝟙 P)
      hsz ⟨inferInstance, hP⟩).symm ≪≫
      unrestrictedTowerComparison.{u, u} l E X n (z ≫ t) q htz hq
    exact ((hz n).of_iso (strictDvrReductionComparison.{u, u} l E X P hP e n)).of_iso c.symm
  let : HasProduct (fun n : ℕ ↦ Q.obj (integralTowerComplex.{0, u, u} l E X D hl n P₀)) := hprod
  have hprodZero : IsZero (∏ᶜ fun n : ℕ ↦
      Q.obj (integralTowerComplex.{0, u, u} l E X D hl n P₀)) := by
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro n
    exact (hz₀ n).eq_of_tgt _ _
  exact Triangle.isZero₁_of_isZero₂₃ _ hlim hprodZero hprodZero

private def topCellSplitPresentationIso (k : Type u) [Field k]
    (a b : ℤ) (r : ℤ → ℕ) :
    topCellSplitComplex (sfResidueModules X k) (sfResidueFree X k) a b r ≅
      sfResidueSplit X k a b r := by
  classical
  let P := sfResidueSplit X k a b r
  let e (q : Set.Icc a b) : sfResidueFree X k (r q.val) ≅ P.X q.val :=
    eqToIso (by
      dsimp [P, sfResidueSplit, sfSplitComplex]
      rw [ite_eq_left (show a ≤ q.val ∧ q.val ≤ b from q.property)])
  have hd (p q : ℤ) : P.d p q = 0 := rfl
  have hs (q : ℤ) (hq : ¬ (a ≤ q ∧ q ≤ b)) : IsZero (P.X q) := by
    dsimp [P, sfResidueSplit, sfSplitComplex]
    rw [ite_eq_right hq]
    exact isZero_zero _
  -- Direct inference gets stuck on a universe constraint (via `AddCommGrpCat` colimits).
  haveI : HasColimitsOfShape (Discrete (Set.Icc a b)) (CochainComplex (sfResidueModules X k) ℤ) :=
    (fun (C : Type _) [Category C] [Abelian C] ↦
      (inferInstance : HasColimitsOfShape (Discrete (Set.Icc a b)) (CochainComplex C ℤ))) _
  exact Sigma.mapIso (fun q : Set.Icc a b ↦
    (CochainComplex.singleFunctor _ q.val).mapIso (e q)) ≪≫
      (zeroDifferentialIntervalIso P a b hd hs).symm

private theorem topCell_interval_ι
    {B : Type*} [Category B] [Abelian B] (P : CochainComplex B ℤ)
    (a b : ℤ) (q : Set.Icc a b)
    (hd : ∀ p q, P.d p q = 0)
    (hs : ∀ q, ¬ (a ≤ q ∧ q ≤ b) → IsZero (P.X q)) :
      Sigma.ι (fun j : Set.Icc a b ↦
        (CochainComplex.singleFunctor _ j.val).obj (P.X j.val)) q ≫
          (zeroDifferentialIntervalIso P a b hd hs).inv =
        HomologicalComplex.mkHomFromSingle (K := P) (𝟙 (P.X q.val))
          (fun t _ ↦ by simp [hd]) := by
  exact IsColimit.comp_coconePointUniqueUpToIso_inv _ _ (Discrete.mk q)

private theorem topCellSplitPresentationIso_inclusion (k : Type u) [Field k]
    (a b : ℤ) (r : ℤ → ℕ) (q : Set.Icc a b) :
    topCellSplitInclusion (sfResidueModules X k) (sfResidueFree X k) a b r q ≫
      (topCellSplitPresentationIso X k a b r).hom =
        sfSplitCell.{u, u} (sfResidueCoefficients X k) a b r q.val q.property := by
  classical
  dsimp only [topCellSplitInclusion, topCellSplitPresentationIso, Iso.trans_hom,
    Iso.symm_hom]
  -- Direct inference gets stuck on a universe constraint (via `AddCommGrpCat` colimits).
  have : HasColimitsOfShape (Discrete (Set.Icc a b)) (CochainComplex (sfResidueModules X k) ℤ) :=
    (fun (C : Type _) [Category C] [Abelian C] ↦
      (inferInstance : HasColimitsOfShape (Discrete (Set.Icc a b)) (CochainComplex C ℤ))) _
  rw [Sigma.ι_mapIso_hom_assoc]
  rw [topCell_interval_ι]
  apply HomologicalComplex.from_single_hom_ext
  simp [sfSplitCell, HomologicalComplex.mkHomFromSingle_f,
    CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self]

private def topCellConeIso {C : Type v} [Category.{w} C] [Abelian C]
    {A B D : CochainComplex C ℤ} (f : A ⟶ B) (g : A ⟶ D) (e : B ≅ D)
    (h : f ≫ e.hom = g) : CochainComplex.mappingCone f ≅ CochainComplex.mappingCone g := by
  have h' : g ≫ e.inv = (𝟙 A) ≫ f := by rw [← h]; simp
  refine ⟨CochainComplex.mappingCone.map f g (𝟙 A) e.hom (by simpa using h),
    CochainComplex.mappingCone.map g f (𝟙 A) e.inv h', ?_, ?_⟩
  · rw [← CochainComplex.mappingCone.map_comp]
    simpa using CochainComplex.mappingCone.map_id f
  · rw [← CochainComplex.mappingCone.map_comp]
    simpa using CochainComplex.mappingCone.map_id g

private theorem topCell_quotient_basis (r : ℕ) (i : ULift.{u + 1} (Fin r)) :
    SheafOfModules.ιFree i ≫ topCellFreeQuotient l E X r =
      CompletedCoefficientFree.quotientProjection.{u, u} l E X 0 ≫
        (scalarReductionRestriction.{u, u} l E X 0).map (SheafOfModules.ιFree i) := by
  apply ((scalarReductionRestriction.{u, u} l E X 0).obj
    (topCellResidueFree l E X r)).unitHomEquiv.injective
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
    Equiv.apply_symm_apply, topCellFreeQuotient, Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  have hp := congrArg (fun s ↦ s.val U)
    (((scalarReductionRestriction.{u, u} l E X 0).obj
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E X 0))).unitHomEquiv.apply_symm_apply
        ((SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E X 0)).unitHomEquiv
          (𝟙 _)))
  let oneB : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj U := 1
  change _ = (SheafOfModules.ιFree i).val.app U
    ((CompletedCoefficientFree.quotientProjection.{u, u} l E X 0).val.app U oneB)
  change (CompletedCoefficientFree.quotientProjection.{u, u} l E X 0).val.app U oneB =
    (1 : (integralCoefficientSheaf.{u, u} l E X 0).obj.obj U) at hp
  rw [hp]
  rfl

private theorem topCell_restriction_single_inverse
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (R : D ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (b : ℤ) (S : D) :
    (R.mapDerivedCategorySingleFunctor b).inv.app S =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) b).inv.app S) ≫
          R.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor D b).obj S) := by
  simp only [Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Iso.refl_inv, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.comp_id, Category.id_comp,
    Category.assoc]
  all_goals erw [Category.id_comp]

private theorem topCell_comparison_normalized (r : ℕ) (b : ℤ) :
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X 0).choose.unit.app _ ≫
      (scalarReductionRestriction.{u, u} l E X 0).mapDerivedCategory.map
        (topCellReductionComparison l E X r b) =
      (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).map
        (topCellFreeQuotient l E X r) ≫
          ((scalarReductionRestriction.{u, u} l E X 0).mapDerivedCategorySingleFunctor b).inv.app
            (topCellResidueFree l E X r) := by
  let adj := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X 0).choose
  let R := scalarReductionRestriction.{u, u} l E X 0
  let S := topCellResidueFree l E X r
  let q := topCellFreeQuotient l E X r
  let raw := (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).map q ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) b).inv.app S) ≫
        R.mapDerivedCategoryFactors.inv.app
          ((CochainComplex.singleFunctor (scalarReductionTarget.{u, u} l E X 0) b).obj S)
  have hraw : adj.unit.app _ ≫ R.mapDerivedCategory.map
      (topCellReductionComparison l E X r b) = raw :=
    (adj.homEquiv _ _).apply_symm_apply raw
  exact hraw.trans (congrArg
    (fun z ↦ (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).map q ≫ z)
    (topCell_restriction_single_inverse R b S)).symm

private theorem topCell_free_reduction (r : ℕ) (b : ℤ) :
    IsIso (topCellReductionComparison l E X r b) ∧ Epi (topCellFreeQuotient l E X r) := by
  exact completed_free_coproduct_reduction l E X r (topCellFreeQuotient l E X r)
    (topCell_quotient_basis l E X r) b (topCellReductionComparison l E X r b)
    (topCell_comparison_normalized l E X r b)

private theorem topCell_single_homology_inverse
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B] (b : ℤ) (S : B) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B b).inv.app S =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b S).inv ≫
        (DerivedCategory.homologyFunctorFactors B b).inv.app
          ((CochainComplex.singleFunctor B b).obj S) := by
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    SingleFunctors.evaluation, DerivedCategory.singleFunctorsPostcompQIso_inv_hom,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors]

private theorem topCell_free_complete (r : ℕ) (b : ℤ) :
    IsDerivedCompleteUnrestricted l E X
      ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree l E X r)) := by
  let e := (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).mapIso
    (topCellFreeProductIso X (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) r)
  have hc := (CompletedCoefficientFree.completed_coefficient_free_resolution l E X).2.1 r b
  apply (CompleteLiftedTopCell.complete_local_iff l E X _).mpr
  apply (IntegralPrincipalCone.locallyComplete_iso l E X
    (integralCompletionScalarValue.{u, u} l E X) e).mpr
  exact (CompleteLiftedTopCell.complete_local_iff l E X _).mp hc

attribute [local irreducible] topCellFreeProductIso topCellSplitPresentationIso topCellConeIso
  HasProEtaleTorAmplitude IsDerivedCompleteUnrestricted topCellFreeQuotient
  topCellReductionComparison

private theorem topCell_lift_cone
    [CompactSpace X]
    (_hweak : ∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 X)))))
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X M)
    (a b : ℤ) (hab : a ≤ b) (r : ℤ → ℕ)
    (theta : ∀ q : Set.Icc a b, topCellResidueFree.{u} l E X (r q.val) ≅
      (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) q.val).obj
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj M))
    (_hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback.{u} V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj M)) a b) :
    ∃ (e : (scalarReductionDerivedExtension.{u, u} l E X 0).obj
          ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
            (topCellIntegralFree.{u} l E X (r b))) ≅
        (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X 0) b).obj
          (topCellResidueFree.{u} l E X (r b)))
      (f : (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree.{u} l E X (r b)) ⟶ M)
      (L : DerivedCategory (scalarReductionSource.{u, u} l E X))
      (g : M ⟶ L)
      (delta : L ⟶ ((DerivedCategory.singleFunctor
        (scalarReductionSource.{u, u} l E X) b).obj
          (topCellIntegralFree.{u} l E X (r b)))⟦(1 : ℤ)⟧),
      e.hom = topCellReductionComparison.{u} l E X (r b) b ∧
      Triangle.mk f g delta ∈ distTriang _ ∧
      IsDerivedCompleteUnrestricted.{u, u} l E X L ∧
      (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) b).map
          (topCellReducedMap.{u} l E X (r b) b M e f) =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (scalarReductionTarget.{u, u} l E X 0) b).hom.app
            (topCellResidueFree.{u} l E X (r b)) ≫ (theta ⟨b, hab, le_rfl⟩).hom := by
  classical
  let A := scalarReductionSource.{u, u} l E X
  let B := scalarReductionTarget.{u, u} l E X 0
  let D := scalarReductionDerivedExtension.{u, u} l E X 0
  let R := scalarReductionRestriction.{u, u} l E X 0
  let P := topCellIntegralFree l E X (r b)
  let S := topCellResidueFree l E X (r b)
  let Pcell := (DerivedCategory.singleFunctor A b).obj P
  let : Projective P := Projective.of_iso
    (topCellFreeProductIso X (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
      (r b)).symm
    ((sf_weakly_contractible_projective.{u, u} X _hweak
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)).2 (r b))
  let : R.Faithful := CompleteLiftedTopCell.restriction_faithful _
  obtain ⟨heiso, hq⟩ := topCell_free_reduction l E X (r b) b
  let := heiso
  let := hq
  let e := asIso (topCellReductionComparison l E X (r b) b)
  let adj := (derivedScalarExtensionRestrictionAdjunction l E X 0).choose
  have he : adj.unit.app Pcell ≫ R.mapDerivedCategory.map e.hom =
      (DerivedCategory.singleFunctor A b).map (topCellFreeQuotient l E X (r b)) ≫
        (R.mapDerivedCategorySingleFunctor b).inv.app S :=
    topCell_comparison_normalized l E X (r b) b
  obtain ⟨δ₀, hδ₀⟩ :=
    (CompletedCoefficientFree.completed_coefficient_free_resolution l E X).2.2 0 M
  have hz := complete_residue_cohomology_bounds l E X M _hcomplete a b hab _hTor
    (b + 1) (Or.inr (by omega))
  have hEpi : Epi ((DerivedCategory.homologyFunctor A b).map
      (CompletedCoefficientFree.reductionMap l E X 0 M)) :=
    (DerivedCategory.HomologySequence.exact₃ _ hδ₀ b (b + 1) rfl).epi_f
      (hz.eq_zero_of_tgt _)
  let := hEpi
  have htop : Epi (CompleteLiftedTopCell.topReduction l E X M b) := by
    unfold CompleteLiftedTopCell.topReduction
    infer_instance
  obtain ⟨f, hf⟩ := @CompleteLiftedTopCell.projective_normalized_lift A B _ _ _ _
    (topCellSourceDerived l E X) (topCellTargetDerived l E X) R
    inferInstance inferInstance inferInstance inferInstance D adj.unit P inferInstance
    S b (topCellFreeQuotient l E X (r b)) inferInstance e he M
    (theta ⟨b, hab, le_rfl⟩) htop
  have hf' : (DerivedCategory.homologyFunctor B b).map
      (topCellReducedMap l E X (r b) b M e f) =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso B b).hom.app S ≫
          (theta ⟨b, hab, le_rfl⟩).hom := by
    apply (cancel_epi
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso B b).inv.app S)).mp
    simpa only [topCellReducedMap, Iso.inv_hom_id_app_assoc] using hf
  obtain ⟨L, g, delta, htriangle⟩ := distinguished_cocone_triangle f
  have hcL : IsDerivedCompleteUnrestricted l E X L :=
    CompleteLiftedTopCell.complete_cone l E X _ htriangle
      (topCell_free_complete l E X (r b) b) _hcomplete
  exact ⟨e, f, L, g, delta, rfl, htriangle, hcL, hf'⟩

/-- Lift the prescribed top residue basis, with its complete cone, split residue
cone model, shortened Tor interval and the singleton-interval and rank-zero cases.
A single-term complex in degree b is the conventional P[-b]. The identity mapping
cone on that complex is the identity pair in degrees b-1 and b.

Source: Stacks Project, proetale.tex, Tags 09C2 and 09C3, final induction paragraph;
derived.tex, Tags 014E, 014A and 05QR
(blueprint: lem-sf-complete-top-residue-cell-cone).

Proof:
1. Normalize the ordinary quotient on each free generator. Extension preserves the
free coproduct, and the shifted free complex is K-flat, so the normalized derived
adjunction makes the precise comparison in the statement an isomorphism.
2. Complete residue cohomology bounds and the uniformizer triangle make the top
reduction epic. Exact terminal evaluation makes the free module projective. The
projective cohomology lifting argument gives f with its prescribed top reduction.
3. Complete f to a distinguished triangle. The source is complete, and cone closure
through the existing intrinsic local completeness criterion makes its cone complete.
4. Reduce the triangle and apply the prescribed residue cone theorem. Its piecewise
split complex is canonically the coproduct of singles used here, respecting the
summand inclusions. Transport the cone decomposition and lower interval model.
Projectivity makes the top homology map injective, giving the equality for every model.
5. Exact pro-etale pullback preserves the shortened cohomology interval. Over the
constant residue field the existing tensor cohomology calculation gives the Tor bound.
6. For a singleton interval the residue cone vanishes. DVR quotient triangles make
all higher reductions vanish. Common K-flat roofs compare them with the completion
tower, whose product and hence limit vanish. Thus L=0 and f is invertible. The empty
free coproduct gives the rank-zero case; the constructions also allow an empty scheme. -/
theorem complete_top_residue_cell_cone
    [CompactSpace X]
    (_hweak : ∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 X)))))
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X M)
    (a b : ℤ) (hab : a ≤ b) (r : ℤ → ℕ)
    (theta : ∀ q : Set.Icc a b, topCellResidueFree.{u} l E X (r q.val) ≅
      (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) q.val).obj
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj M))
    (_hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback.{u} V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj M)) a b) :
    ∃ (e : (scalarReductionDerivedExtension.{u, u} l E X 0).obj
          ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
            (topCellIntegralFree.{u} l E X (r b))) ≅
        (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X 0) b).obj
          (topCellResidueFree.{u} l E X (r b)))
      (f : (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree.{u} l E X (r b)) ⟶ M)
      (L : DerivedCategory (scalarReductionSource.{u, u} l E X))
      (g : M ⟶ L)
      (delta : L ⟶ ((DerivedCategory.singleFunctor
        (scalarReductionSource.{u, u} l E X) b).obj
          (topCellIntegralFree.{u} l E X (r b)))⟦(1 : ℤ)⟧),
      e.hom = topCellReductionComparison.{u} l E X (r b) b ∧
      Triangle.mk f g delta ∈ distTriang _ ∧
      IsDerivedCompleteUnrestricted.{u, u} l E X L ∧
      (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) b).map
          (topCellReducedMap.{u} l E X (r b) b M e f) =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (scalarReductionTarget.{u, u} l E X 0) b).hom.app
            (topCellResidueFree.{u} l E X (r b)) ≫ (theta ⟨b, hab, le_rfl⟩).hom ∧
      (∀ phi : DerivedCategory.Q.obj (topCellResidueSplit.{u} l E X a b r) ≅
          (scalarReductionDerivedExtension.{u, u} l E X 0).obj M,
        (∀ q : Set.Icc a b,
          (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) q.val).map
              (DerivedCategory.Q.map (topCellResidueInclusion.{u} l E X a b r q) ≫ phi.hom) =
            (DerivedCategory.singleFunctorCompHomologyFunctorIso
              (scalarReductionTarget.{u, u} l E X 0) q.val).hom.app
                (topCellResidueFree.{u} l E X (r q.val)) ≫ (theta q).hom) →
        topCellReducedMap.{u} l E X (r b) b M e f =
          DerivedCategory.Q.map
            (topCellResidueInclusion.{u} l E X a b r ⟨b, hab, le_rfl⟩) ≫ phi.hom) ∧
      Nonempty ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone
          (topCellResidueInclusion.{u} l E X a b r ⟨b, hab, le_rfl⟩))) ∧
      Nonempty (CochainComplex.mappingCone
          (topCellResidueInclusion.{u} l E X a b r ⟨b, hab, le_rfl⟩) ≅
        topCellResidueSplit.{u} l E X a (b - 1) r ⨿
          CochainComplex.mappingCone (𝟙 ((HomologicalComplex.single
            (scalarReductionTarget.{u, u} l E X 0) (.up ℤ) b).obj
              (topCellResidueFree.{u} l E X (r b))))) ∧
      Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone
        (𝟙 ((HomologicalComplex.single (scalarReductionTarget.{u, u} l E X 0)
          (.up ℤ) b).obj (topCellResidueFree.{u} l E X (r b)))))) 0) ∧
      Nonempty ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L ≅
        DerivedCategory.Q.obj (topCellResidueSplit.{u} l E X a (b - 1) r)) ∧
      (∀ q : Set.Icc a (b - 1), Nonempty (topCellResidueFree.{u} l E X (r q.val) ≅
        (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) q.val).obj
          ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L))) ∧
      (a < b → ∀ V : X.ProEt,
        HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
          ((proEtaleRingDerivedPullback.{u} V.hom
            (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
            (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
            (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
                ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L)) a (b - 1)) ∧
      (a = b → IsZero ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L) ∧
        IsZero L ∧ IsIso f) ∧
      (r b = 0 → IsZero (topCellIntegralFree.{u} l E X (r b))) := by
  classical
  obtain ⟨e, f, L, g, delta, he, htriangle, hcL, hf'⟩ :=
    topCell_lift_cone l E X _hweak M _hcomplete a b hab r theta _hTor
  let A := scalarReductionSource.{u, u} l E X
  let B := scalarReductionTarget.{u, u} l E X 0
  let D := scalarReductionDerivedExtension.{u, u} l E X 0
  let S := topCellResidueFree l E X (r b)
  let Pcell := (DerivedCategory.singleFunctor A b).obj (topCellIntegralFree l E X (r b))
  let k := Padic.coefficientExtensionRing l E 1
  let : Field k := integralScalarResidueField l E
  let N := D.obj M
  let C := D.obj L
  have hN : ∀ q : ℤ, ¬ (a ≤ q ∧ q ≤ b) →
      IsZero ((DerivedCategory.homologyFunctor B q).obj N) := by
    let : Finite k := Padic.finite_coefficientExtensionRing l E 1 (by omega)
    obtain ⟨eR, _, _, eM, _, α, _, _, β, _, γ, _⟩ :=
      proEtaleDerivedPullback_identity X k
    let γ' : proEtaleRingDerivedPullback (𝟙 X)
        (proEtaleConstantRing X k) (proEtaleConstantRing X k)
        (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso
          (ULift.{u + 1, u} k) (𝟙 X)) ≅ 𝟭 _ := γ
    intro q hq
    have hz := tor_cohomology_bounds X k _ a b (_hTor (ProEt.mk (𝟙 X))) q (by omega)
    exact ((DerivedCategory.homologyFunctor B q).mapIso (γ'.app N)).isZero_iff.mp hz
  obtain ⟨sD, hD⟩ :=
    (scalarReductionDerivedExistence.{u, u} l E X 0).choose_spec.choose_spec.2.1
  let : D.CommShift ℤ := sD
  let : D.IsTriangulated := hD
  let uTop := topCellReducedMap l E X (r b) b M e f
  let dTop := D.map delta ≫ (D.commShiftIso (1 : ℤ)).hom.app Pcell ≫
    (shiftFunctor _ (1 : ℤ)).map e.hom
  have hresTriangle : Triangle.mk uTop (D.map g) dTop ∈ distTriang _ := by
    apply isomorphic_distinguished _ (D.map_distinguished _ htriangle) _
    exact (Triangle.isoMk (D.mapTriangle.obj (Triangle.mk f g delta))
      (Triangle.mk uTop (D.map g) dTop) e (Iso.refl _) (Iso.refl _)
      (by
        change D.map f ≫ 𝟙 _ = e.hom ≫ (e.inv ≫ D.map f)
        simp)
      (by change D.map g ≫ 𝟙 _ = 𝟙 _ ≫ D.map g; simp)
      (by
        change (D.map delta ≫ (D.commShiftIso (1 : ℤ)).hom.app Pcell) ≫
          (shiftFunctor _ (1 : ℤ)).map e.hom = 𝟙 _ ≫ dTop
        simp only [dTop, Category.id_comp, Category.assoc])).symm
  have htheta : sfFreeCohomologyMap.{u, u} (sfResidueCoefficients X k) b (r b) uTop =
      (theta ⟨b, hab, le_rfl⟩).hom := by
    change (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b S).inv ≫
      (DerivedCategory.homologyFunctorFactors B b).inv.app
        ((CochainComplex.singleFunctor B b).obj S) ≫
          (DerivedCategory.homologyFunctor B b).map uTop = _
    rw [← Category.assoc, ← topCell_single_homology_inverse]
    change (DerivedCategory.singleFunctorCompHomologyFunctorIso B b).inv.app S ≫
      (DerivedCategory.homologyFunctor B b).map uTop = _
    have ht := hf'
    change (DerivedCategory.homologyFunctor B b).map uTop =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B b).hom.app S ≫
        (theta ⟨b, hab, le_rfl⟩).hom at ht
    rw [ht, Iso.inv_hom_id_app_assoc]
  obtain ⟨hphi, htopModel, hcone, hterms, hsupp, hdiff, hcontract, hCcone,
      hconeLower, hTorLower, hranks, hbounds, hempty⟩ :=
    sf_prescribed_residue_cell_cone_model X k _hweak a b hab r N hN
      (fun q hq ↦ theta ⟨q, hq⟩) uTop htheta C (D.map g) dTop hresTriangle
  let s := topCellSplitPresentationIso X k a b r
  let t := topCellSplitPresentationIso X k a (b - 1) r
  let iTop := topCellResidueInclusion l E X a b r ⟨b, hab, le_rfl⟩
  let iModel := sfResidueInclusion X k a b hab r
  have hi : iTop ≫ s.hom = iModel :=
    topCellSplitPresentationIso_inclusion X k a b r ⟨b, hab, le_rfl⟩
  let c := topCellConeIso iTop iModel s hi
  let eC := hCcone.some ≪≫ hconeLower.some ≪≫ DerivedCategory.Q.mapIso t.symm
  refine ⟨e, f, L, g, delta, he, htriangle, hcL, hf', ?_,
    ⟨hCcone.some ≪≫ DerivedCategory.Q.mapIso c.symm⟩, ?_,
    ⟨CochainComplex.mappingCone.homotopyToZeroOfId _⟩, ⟨eC⟩, ?_, ?_, ?_, ?_⟩
  · intro phi hphi
    let : Projective S := Projective.of_iso
      (topCellFreeProductIso X (integralCoefficientSheaf.{u, u} l E X 0) (r b)).symm
      ((sf_weakly_contractible_projective.{u, u} X _hweak
        (integralCoefficientCommRingSheaf.{u, u} l E X 0)).2 (r b))
    apply (sfProjectiveHomologyBijective S N b).1
    exact hf'.trans (hphi ⟨b, hab, le_rfl⟩).symm
  · exact ⟨c ≪≫ hcone.some ≪≫
      coprod.mapIso t.symm (Iso.refl _)⟩
  · intro q
    have hq : a ≤ q.val ∧ q.val ≤ b - 1 := q.property
    exact hranks q.val ⟨hq.1, by omega⟩
  · intro hab' V
    let F := proEtaleRingModulePullback V.hom
      (proEtaleConstantRing X k) (proEtaleConstantRing V.left k)
      (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso (ULift.{u + 1, u} k) V.hom)
    apply bounded_field_tor V.left k _ a (b - 1) (by omega)
    intro q hq
    exact (F.map_isZero (hbounds q (by omega))).of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso q).symm.app C)
  · intro hab'
    have hzC : IsZero C := (hempty hab').2
    have hzL := topCell_complete_zero l E X L hcL hzC
    exact ⟨hzC, hzL, (Triangle.isZero₃_iff_isIso₁ _ htriangle).mp hzL⟩
  · intro hr
    rw [hr]
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro i
    exact Fin.elim0 i.down

end WeilConjectures
