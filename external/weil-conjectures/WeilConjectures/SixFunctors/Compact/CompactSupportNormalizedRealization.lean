/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
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
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.SixFunctors.Compact.CompactSupportInputTowerCompatibility
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycle
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportCoefficientChange
import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower

/-! # Normalized realization of the specified compact-support quotient tower

Source: blueprint main-20261015, lemma-change-coefficients-compact-support, proof paragraph 2;
Stacks Tags 06YS, 0D6D, 07A6 and 05RT
(blueprint: lem-coef-compact-support-normalized-realization).

Natural index n always denotes the positive coefficient exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The sequence-system quotient is the direct quotient homomorphism on constant sheaves.
Source: Stacks Tag 03EK; blueprint input quotient maps
(blueprint: lem-coef-compact-support-normalized-realization).
Proof: induct on m-n. At equal levels both maps are identities; at consecutive levels
they are the coefficient transition. Quotient factors compose on every residue class,
and constant sheafification and forgetting commutativity preserve their compositions. -/
theorem coefCompactSupportQuotient_eq (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRQuotient l E W h =
      (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (compactSupportLevelSheafQuotient l E W m n h) := by
  exact compactSupportQuotient_eq l E W h

/-- Canonical identity transport from the sequence quotient to the direct quotient.
Source: blueprint quotient maps; Stacks Tag 03DA
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportRestrictionIso (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E W h ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory :=
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E m n h)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E m n h)
  Functor.mapDerivedCategoryNatIso
    (F := normalizedDVRModuleRes l E W h)
    (G := proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h))
    (eqToIso (congrArg (fun q ↦ SheafOfModules.restrictScalars.{u + 1} q)
      (coefCompactSupportQuotient_eq l E W h)))

/-- The actual input quotient transition in the sequence quotient coordinates.
Source: blueprint input reductions; Stacks Tag 03EK
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportInputTau (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) {m n : ℕ} (h : n ≤ m) :
    (scalarReductionDerivedExtension l E W m).obj K ⟶
      (normalizedDVRRes l E W h).obj ((scalarReductionDerivedExtension l E W n).obj K) :=
  compactSupportReductionMap l E W m n h K ≫
    (coefCompactSupportRestrictionIso l E W h).inv.app
      ((scalarReductionDerivedExtension l E W n).obj K)

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard constantSheaf Padic.coefficientExtensionIdeal
  coefficientSequenceEvaluation coefficientSequenceTransition
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence Functor.objPreimage Functor.objObjPreimageIso

/-- The finite-level output transition, before restriction to completed coefficients.
Source: blueprint proof paragraph 2, specified coefficient maps
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportTau {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) {m n : ℕ} (h : n ≤ m) :=
  (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
      (compactSupportReductionMap l E X m n h K) ≫
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
      ((scalarReductionDerivedExtension l E X n).obj K)

/-- The output object at a positive coefficient level, in the recorded tower category.
Source: blueprint proof paragraph 2
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportLevel {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    normalizedDVRDerived l E Y n :=
  (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
    ((scalarReductionDerivedExtension l E X n).obj K)

/-- The specified output transition in the sequence quotient coordinates.
Source: blueprint proof paragraph 2
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportNormalizedTau {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource l E X))
    {m n : ℕ} (h : n ≤ m) :
    coefCompactSupportLevel l E c K m ⟶
      (normalizedDVRRes l E Y h).obj (coefCompactSupportLevel l E c K n) :=
  coefCompactSupportTau l E c K h ≫
    (coefCompactSupportRestrictionIso l E Y h).inv.app (coefCompactSupportLevel l E c K n)

attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

end WeilConjectures
