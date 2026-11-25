/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportCoefficientPresentation
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
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
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-! # Unit and cocycle for compact-support coefficient quotients

Source: the current blueprint, lem-coef-integral-compact-support.proof.md,
finite-level coefficient comparison; Stacks Tags 03EK, 06YS, 06YY and 07A6
(blueprint: lem-coef-compact-support-quotient-coordinates).

Index n denotes exponent n+1, so every positive coefficient exponent is included.
All reduction maps are the published normalized adjuncts of the actual quotient maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Keep distinct quotient levels from unfolding their valuation-theoretic ideal data.
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Equal-level quotients are identity maps.
Source: Stacks Tag 03EK; blueprint coefficient maps
(blueprint: lem-coef-compact-support-quotient-coordinates).
Proof: the quotient factor induced by the identity sends each residue class to itself. -/
theorem compactSupportQuotient_self (n : ℕ) :
    compactSupportLevelQuotient l E n n le_rfl = RingHom.id _ := by
  exact Ideal.Quotient.factor_eq

/-- Direct and successive quotient factors coincide.
Source: Stacks Tag 03EK; blueprint coefficient maps
(blueprint: lem-coef-compact-support-quotient-coordinates).
Proof: both homomorphisms send the class of a to the class of a in the final quotient. -/
theorem compactSupportQuotient_comp (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m) :
    (compactSupportLevelQuotient l E m n hmn).comp
        (compactSupportLevelQuotient l E r m hrm) =
      compactSupportLevelQuotient l E r n (hmn.trans hrm) := by
  unfold compactSupportLevelQuotient
  exact Ideal.Quotient.factor_comp
    (by unfold Padic.coefficientExtensionIdeal
        exact Ideal.pow_le_pow_right (Nat.add_le_add_right hrm 1))
    (by unfold Padic.coefficientExtensionIdeal
        exact Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1))

/-- The identity restriction identification, including the equal-level quotient cast.
Source: Stacks Tag 03DA; blueprint identity convention
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
def compactSupportQuotientResId (W : Scheme.{u}) (n : ℕ) :
    (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E n n le_rfl)).mapDerivedCategory ≅ 𝟭 _ :=
  compactSupportCoefficientResId W (Padic.coefficientExtensionRing l E (n + 1))
    (compactSupportLevelQuotient l E n n le_rfl) (compactSupportQuotient_self l E n)

/-- The canonical composition identification for all three quotient levels.
Source: Stacks Tag 03DA; blueprint restriction composition convention
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
def compactSupportQuotientResComp (W : Scheme.{u})
    (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m) :
    (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n hmn)).mapDerivedCategory ⋙
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E r n (hmn.trans hrm))).mapDerivedCategory :=
  compactSupportCoefficientResComp W
    (compactSupportLevelQuotient l E r m hrm)
    (compactSupportLevelQuotient l E m n hmn)
    (compactSupportLevelQuotient l E r n (hmn.trans hrm))
    (compactSupportQuotient_comp l E r m n hrm hmn)

end WeilConjectures
