/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleData
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleRepresentativesData
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientComputationSquares
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientInputLaws
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientAdjunct
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientRawInput
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientRawOutputIdentity
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientRawOutputComposition

/-! # Unit and cocycle for compact-support coefficient quotients

Source: the current blueprint, lem-coef-integral-compact-support.proof.md,
finite-level coefficient comparison; Stacks Tags 03EK, 06YS, 06YY and 07A6
(blueprint: lem-coef-compact-support-quotient-cocycle).

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

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified quotient arrows and their compact-support images satisfy unit and
composition on arbitrary unbounded objects. No constructibility or Tor bound is assumed.
Source: blueprint proof paragraph 2; Stacks Tags 03EK, 06YY and 07A6
(blueprint: lem-coef-compact-support-quotient-cocycle).
Proof: the twice-transposed final unit is the component of the canonical
left-adjoint composition isomorphism, so the quotient adjunct is invertible. The
inverse Hom-equivalence identity gives its displayed unit equation. Apply the input
quotient identity and composition laws. The normalized identity coefficient square
transports the input identity to compact support. For composition, map the invertible
prime in the base field to each stalk, specialize the coefficient composition square
to the two quotient maps with their direct-quotient equality cast, and use naturality
to move the middle quotient arrow across the comparison. Combine the compact-support
maps by functoriality and use the input cocycle. The canonical coefficient presentation
aliases have exactly the existing maps as values, so these are the stated arrows. -/
theorem compactSupport_quotient_cocycle
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
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
        _ _).symm (compactSupportReductionMap l E X m n h K)))) ∧
    (∀ n : ℕ, compactSupportReductionMap l E X n n le_rfl K ≫
      (compactSupportQuotientResId l E X n).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportReductionMap l E X r m hrm K ≫
          (proEtaleCoefficientRestrictScalars X
            (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory.map
              (compactSupportReductionMap l E X m n hmn K) ≫
          (compactSupportQuotientResComp l E X r m n hrm hmn).hom.app
            ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) =
        compactSupportReductionMap l E X r n (hmn.trans hrm) K) ∧
    (∀ n : ℕ, ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
        (compactSupportReductionMap l E X n n le_rfl K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E n n le_rfl)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) ≫
      (compactSupportQuotientResId l E Y n).hom.app
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (r + 1))).map
        (compactSupportReductionMap l E X r m hrm K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E r m hrm)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X m).obj K)) ≫
          (proEtaleCoefficientRestrictScalars Y
            (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory.map
              (((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
        (compactSupportReductionMap l E X m n hmn K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n hmn)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))) ≫
          (compactSupportQuotientResComp l E Y r m n hrm hmn).hom.app
            ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
              ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) =
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (r + 1))).map
        (compactSupportReductionMap l E X r n (hmn.trans hrm) K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E r n (hmn.trans hrm))).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))) := by
  let hi := compactSupportQuotient_input_laws l E X K
  have hraw := compactSupportQuotient_raw_input l E X K hi
  exact ⟨compactSupportQuotient_adjunct l E X K, hraw.1, hraw.2,
    compactSupportQuotient_raw_output_identity l E c K hi.1,
    compactSupportQuotient_raw_output_composition l E k _hl c K hi⟩

end WeilConjectures
