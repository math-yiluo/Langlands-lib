/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleData
public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientNative
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientComparisonLaws

/-! # Transport of the input quotient cocycle through compact support

Source: the current blueprint, lem-coef-integral-compact-support.proof.md,
finite-level coefficient comparison; Stacks Tag 03DA
(blueprint: lem-coef-compact-support-quotient-output-composition).
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

/-- Compact-support quotient composition from the input law.
Source: blueprint finite-level comparison, Steps 5--6
(blueprint: lem-coef-compact-support-quotient-output-composition).
Proof: apply the abstract naturality calculation to the given input law and the
normalized compact-support coefficient-restriction square. For composition map
the unit ell in the base field into each stalk and use the quotient-factor equality. -/
theorem compactSupportQuotient_output_composition
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hcomp : (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportQuotientNativeMap l E X r m hrm K ≫
          (compactSupportQuotientNativeRestriction l E X r m hrm).map
              (compactSupportQuotientNativeMap l E X m n hmn K) ≫
          (compactSupportQuotientNativeResComp l E X r m n hrm hmn).hom.app
            ((compactSupportQuotientNativeLevel l E X n).obj K) =
        compactSupportQuotientNativeMap l E X r n (hmn.trans hrm) K)) :
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (r + 1)) c).map
        (compactSupportQuotientNativeMap l E X r m hrm K) ≫
      (compactSupportQuotientNativeComparison l E c r m hrm).hom.app
        ((compactSupportQuotientNativeLevel l E X m).obj K)) ≫
          (compactSupportQuotientNativeRestriction l E Y r m hrm).map
              (((sfAmbientCompactSupportCandidate
                (Padic.coefficientExtensionRing l E (m + 1)) c).map
        (compactSupportQuotientNativeMap l E X m n hmn K) ≫
      (compactSupportQuotientNativeComparison l E c m n hmn).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K))) ≫
          (compactSupportQuotientNativeResComp l E Y r m n hrm hmn).hom.app
            ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
              ((compactSupportQuotientNativeLevel l E X n).obj K)) =
        ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (r + 1)) c).map
        (compactSupportQuotientNativeMap l E X r n (hmn.trans hrm) K) ≫
      (compactSupportQuotientNativeComparison l E c r n (hmn.trans hrm)).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K))) := by
  intro r m n hrm hmn
  have hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y) := by
    intro y
    simpa only [map_natCast] using _hl.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) ≫
        Y.presheaf.germ (⊤ : Y.Opens) y (by trivial)).hom
  have hn := (compactSupportQuotientNativeComparison l E c r m hrm).hom.naturality
      (compactSupportQuotientNativeMap l E X m n hmn K)
  have hσ := compactSupportQuotientNativeComparison_comp l E f hl c r m n hrm hmn
    ((compactSupportQuotientNativeLevel l E X n).obj K)
  simp only [CategoryTheory.Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  rw [← hσ]
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Category.assoc, hcomp r m n hrm hmn]

end WeilConjectures
