/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.CompletionDimensionEquality
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Dimension of the completion of a Noetherian local ring

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07NV
(blueprint: lem-weil-pbc-completion-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

/-- The maximal-ideal completion of a Noetherian local ring has the same finite Krull dimension.
Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07NV, alternative proof via
Algebra Lemma Tag 00ON (blueprint: lem-weil-pbc-completion-dimension).

1. The canonical map to the completion is faithfully flat
   (`lem-weil-pbc-local-completion-faithfully-flat`). The completion is Noetherian
   (`lem-weil-pbc-adic-completion-noetherian`) and local, with maximal ideal the extension of
   the original maximal ideal and the same residue field
   (`lem-weil-pbc-local-completion-local-ring`).
2. The contraction of the completion's maximal ideal contains the original maximal ideal
   and is proper, since it does not contain 1. By maximality it equals the original ideal.
3. Apply the flat height formula (`lem-weil-pbc-flat-height-formula`) at these maximal ideals.
   Localization at the maximal ideal of a local ring is an isomorphism, since the elements
   inverted are already units (`def-weil-pbc-localization-at-prime`). Thus the completion's
   dimension equals the original dimension plus the dimension of the closed fibre.
4. The closed fibre is the residue field, of dimension zero, giving equality. The maximal
   ideal is finitely generated (`def-weil-pbc-noetherian-ring`), and the original dimension
   is bounded by its number of generators
   (`lem-weil-pbc-noetherian-local-dimension-le-generators`). Equality makes both finite.
-/
theorem completion_dimension (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) = ringKrullDim A ∧
      ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) < ⊤ ∧
      ringKrullDim A < ⊤ := by
  have hA : ringKrullDim A < ⊤ := ringKrullDim_lt_top
  have heq := completion_dimension_eq A
  have hB : ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) < ⊤ :=
    heq ▸ hA
  exact ⟨heq, hB, hA⟩

end RingTheory
