/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingShiftChainPart
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingShiftDerivedPart

/-! # Signed shifts of normalized reindexing comparisons

Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 0GMX, 0A8X, 08J9.
(blueprint: lem-pod-reindexing-signed-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Signed shifts commute with every product-normalized reindexing comparison.
Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-signed-shifts).

Proof: in Hom degree r reindex the factor p to p-a and multiply by (-1)^(a*r).
The ratio of these scalars in degrees r+1 and r is (-1)^a. With the shifted
differentials (-1)^a d_P and (-1)^b d_I this makes both terms of the Hom differential
commute. Reversing the reindexing with the same unit scalar gives the inverse.
Thus the formula constructs ChainShift on both sites for all integers, including
negative shifts. Apply each Hom-product projection to the two routes in ShiftLaws.chain.
Both equal (-1)^(a*r) times reindexing of the same factor, since the termwise shift
comparison has identity components and reindexing is additive. Product extensionality
gives the chain square. Shifted K-injective complexes are K-injective: shift a map
from an acyclic source back, null-homotope it, and shift the homotopy forward with
the factor (-1)^b. The derived_model equation therefore localizes the chain square.
The normalized sourceShift and homCommShift are characterized by these same signed
product projections, so the localized square uses precisely signedShift. Naturality
along resolutions gives ShiftLaws.derived for arbitrary derived objects. -/
theorem signed_shift_laws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∃ (sX : ChainShift l E X s) (sY : ChainShift l E Y s),
      ShiftLaws l E g s SX SY TX TY c sX sY := by
  obtain ⟨sX, sY, hchain⟩ := chain_shift_part_exists l E g s SX SY TX TY c
  refine ⟨sX, sY, ⟨hchain, ?_⟩⟩
  exact derived_shift_part l E g s SX SY TX TY c

end WeilConjectures.PodReindexingCoherence
