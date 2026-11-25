/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingComparisonCoreHomData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingComparisonCoreTensorData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingComparisonCoreTensorModel

/-! # Core comparison data for reindexing

Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 0GMX, 0A8X, 08J9.
(blueprint: lem-pod-reindexing-comparison-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/--
The normalized tensor and Hom comparison data exists for reindexing along a scheme
isomorphism.  This is the construction of all fields of `Comparison`, before the
evaluation equation is imposed.

Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 0GMX and 0A8X
(blueprint: lem-pod-reindexing-comparison-core).

Proof: combine the product-Hom comparison and derived resolution model with the
sectionwise tensor comparison.  Totalize the pure-tensor maps, descend them through
the localization on independent K-flat representatives, and use the recorded
K-injective model equations.  The resulting maps satisfy every field of
`Comparison`, including the projection and model normalizations.
-/
theorem comparison_core_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) :
    Nonempty (Comparison l E g s SX SY TX TY) := by
  obtain ⟨h⟩ := comparison_core_hom_data_exists l E g s SX SY TX TY
  obtain ⟨t⟩ := comparison_core_tensor_data_exists l E g s SX SY TX TY
  obtain ⟨tensor, ⟨m⟩⟩ := comparison_core_tensor_model_exists l E g s SX SY TX TY t
  exact ⟨{
    chain := h.chain
    chain_projection := h.chain_projection
    derived := h.derived
    derived_model := h.derived_model
    tensorChain := t.tensorChain
    tensorChain_pure := t.tensorChain_pure
    tensor := tensor
    tensor_model := m.tensor_model }⟩

end WeilConjectures.PodReindexingCoherence
