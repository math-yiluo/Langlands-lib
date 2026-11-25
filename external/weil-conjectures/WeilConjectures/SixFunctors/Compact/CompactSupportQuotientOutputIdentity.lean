/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleData
public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientNative
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientComparisonLaws

/-! # Transport of the input quotient identity through compact support

Source: the current blueprint, lem-coef-integral-compact-support.proof.md,
finite-level coefficient comparison; Stacks Tag 03DA
(blueprint: lem-coef-compact-support-quotient-output-identity).
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

/-- Compact-support quotient identity from the input law.
Source: blueprint finite-level comparison, Steps 5--6
(blueprint: lem-coef-compact-support-quotient-output-identity).
Proof: apply the abstract naturality calculation to the given input law and the
normalized compact-support coefficient-restriction square. For composition map
the unit ell in the base field into each stalk and use the quotient-factor equality. -/
theorem compactSupportQuotient_output_identity
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hid : (∀ n : ℕ, compactSupportQuotientNativeMap l E X n n le_rfl K ≫
      (compactSupportQuotientNativeResId l E X n).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K) = 𝟙 _)) :
    (∀ n : ℕ, ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
        (compactSupportQuotientNativeMap l E X n n le_rfl K) ≫
      (compactSupportQuotientNativeComparison l E c n n le_rfl).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K)) ≫
      (compactSupportQuotientNativeResId l E Y n).hom.app
        ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
          ((compactSupportQuotientNativeLevel l E X n).obj K)) = 𝟙 _) := by
  intro n
  have hσ := compactSupportQuotientNativeComparison_id l E c n
    ((compactSupportQuotientNativeLevel l E X n).obj K)
  rw [Category.assoc, hσ, ← CategoryTheory.Functor.map_comp, hid n]
  exact (sfAmbientCompactSupportCandidate
    (Padic.coefficientExtensionRing l E (n + 1)) c).map_id _

end WeilConjectures
