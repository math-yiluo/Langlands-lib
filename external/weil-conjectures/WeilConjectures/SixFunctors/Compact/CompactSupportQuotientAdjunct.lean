/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleData
import WeilConjectures.CategoryTheory.CompactSupportQuotient.CompactSupportQuotientTransport

/-! # Invertibility of the normalized quotient adjunct

Source: the current blueprint, lem-coef-integral-compact-support.proof.md,
finite-level coefficient comparison; Stacks Tag 03DA
(blueprint: lem-coef-compact-support-quotient-adjunct).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
-- Keep distinct quotient levels from unfolding their valuation-theoretic ideal data.
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.scalarReductionDerivedExtension

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The quotient adjunct is invertible and transposes back to the prescribed arrow.
Source: quotient unit characterization, Stacks Tag 07A6
(blueprint: lem-coef-compact-support-quotient-adjunct).
Proof: the twice-transposed integral unit is the left-adjoint composition isomorphism.
The inverse Hom equivalence gives the unit equation. No geometric hypothesis is used. -/
theorem compactSupportQuotient_adjunct
    (X : Scheme.{u}) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (∀ (m n : ℕ) (h : n ≤ m),
      IsIso ((((pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E X m n h)).homEquiv
        _ _).symm (compactSupportReductionMap l E X m n h K))) ∧
      compactSupportReductionMap l E X m n h K =
        (pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E X m n h)).unit.app
            ((scalarReductionDerivedExtension.{u, u} l E X m).obj K) ≫
          (proEtaleCoefficientRestrictScalars X
            (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
              ((((pbcDerivedScalarAdjunction
        (compactSupportLevelSheafQuotient l E X m n h)).homEquiv
        _ _).symm (compactSupportReductionMap l E X m n h K)))) := by
  intro m n h
  constructor
  · exact CategoryTheory.CompactSupportQuotient.adjunct_isIso
      (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X m).choose
      (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
      (pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E X m n h))
      (compactSupportRestrictionComp l E X m n h) K
  · symm
    exact ((pbcDerivedScalarAdjunction
      (compactSupportLevelSheafQuotient l E X m n h)).homEquiv _ _).apply_symm_apply
        (compactSupportReductionMap l E X m n h K)

end WeilConjectures
