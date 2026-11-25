/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingComparisonCore
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationLaw

/-! # Evaluation-normalized reindexing comparison

Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 0GMX, 0A8X, 08J9.
(blueprint: lem-pod-reindexing-evaluated-comparison).
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

/-- Construct the normalized chain, derived and tensor comparisons with their evaluation equation.
Source: blueprint dual-Tate compatibility, Steps 1--2; Stacks 0GMX, 0A8X, 08J9
(blueprint: lem-pod-reindexing-evaluated-comparison).

Proof: reindex each product factor of the ordinary Hom complex. Its differential is
preserved because reindexing is additive and respects both compositions. For K-injective
targets this is the comparison of the Hom-resolution-model lemma. Descend through
localization to its specified natural derived comparison. Reindex total-tensor summands;
pure-tensor sections give the tensorChain comparison. Localize on independent K-flat
representatives, obtaining tensor with its tensor_model equation. These constructions
satisfy all four representative normalization fields of Comparison.
For evaluation take a flat-term K-flat P and a K-injective target I. The one-sided
chain-transpose lemma applied to the identity of Hom(P,I) gives evaluation on
Hom(P,I) tensor P by f tensor x maps to f(x), followed by inverse target augmentation.
After reindexing the two chain evaluations agree on every pure tensor by chain_projection
and tensorChain_pure. Sheafification and total-summand extensionality give equality of
chain maps. Localize and cancel the K-flat and K-injective model isomorphisms. Naturality
along independent resolutions extends the resulting equation to arbitrary derived M,N.
This construction asserts neither the shift squares nor the uniqueness and transpose laws. -/
theorem evaluated_comparison_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) :
    ∃ c : Comparison l E g s SX SY TX TY,
      ∀ M N : podReindexingDerived l E Y s,
        c.tensor.hom.app ((podReindexingDerivedHom l E Y s).obj (op M, N), M) ≫
          SX.tensor.map (Prod.mkHom (c.derived.hom.app (op M, N))
            (𝟙 ((podReindexingDerivedFunctor l E g s).obj M))) ≫
          SX.evaluation ((podReindexingDerivedFunctor l E g s).obj M)
            ((podReindexingDerivedFunctor l E g s).obj N) =
          (podReindexingDerivedFunctor l E g s).map (SY.evaluation M N) := by
  obtain ⟨c⟩ := comparison_core_exists l E g s SX SY TX TY
  refine ⟨c, ?_⟩
  exact comparison_evaluation_law l E g s SX SY TX TY c

end WeilConjectures.PodReindexingCoherence
