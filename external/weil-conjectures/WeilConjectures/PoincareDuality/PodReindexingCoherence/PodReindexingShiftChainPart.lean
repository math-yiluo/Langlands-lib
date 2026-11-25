/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingChainShiftPresentations
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingChainShiftSquare

/-! # Chain part of signed shift laws for reindexing comparisons

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-signed-shifts).

The chain square is isolated from the derived localization square so that the
representative construction can be proved independently.
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

/-- The chain square required by `ShiftLaws`, with its shift presentations supplied. -/
def ChainShiftPart {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (sX : ChainShift l E X s) (sY : ChainShift l E Y s) : Prop :=
  ∀ (P I : K l E Y s) (a b : ℤ),
    (c.chain (P⟦a⟧) (I⟦b⟧)).hom ≫
      (((podReindexingHom l E X s).map
        ((complexShift l E g s a).inv.app P).op).app
          ((podReindexingComplexFunctor l E g s).obj (I⟦b⟧)) ≫
        ((podReindexingHom l E X s).obj
          (op (((podReindexingComplexFunctor l E g s).obj P)⟦a⟧))).map
            ((complexShift l E g s b).hom.app I)) ≫
      (sX.iso ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I) a b).hom =
      (podReindexingComplexFunctor l E g s).map (sY.iso P I a b).hom ≫
        (complexShift l E g s (b-a)).hom.app
          (hom l E Y s P I) ≫ ((c.chain P I).hom)⟦b-a⟧'

/-- Construct normalized chain shifts and prove their reindexing square.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-signed-shifts).

Proof: define the degree-r map by reindexing the p-factor to p-a and multiplying
by `(-1)^(a*r)`. The ratio of consecutive degree scalars compensates the two
terms of the Hom differential. Product projections prove the chain identity,
and the specified comparison projections prove the reindexing square. -/
theorem chain_shift_part_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∃ (sX : ChainShift l E X s) (sY : ChainShift l E Y s),
      ChainShiftPart l E g s SX SY TX TY c sX sY := by
  obtain ⟨sX, sY, _⟩ := chain_shift_presentations l E g s SX SY TX TY c
  exact ⟨sX, sY, chain_shift_reindexing_square l E g s SX SY TX TY c sX sY⟩

end WeilConjectures.PodReindexingCoherence
