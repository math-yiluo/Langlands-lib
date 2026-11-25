/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import WeilConjectures.NumberTheory.Padics.CoefficientExtension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Topology.Algebra.Module.Compact
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.RingTheory.FiniteOverCompleteRing

set_option linter.privateModule false

/-!
# Adic systems of finite modules over p-adic coefficient rings

Source: Stacks Project, Tags 09B8, 031D, 031B and 00MA;
blueprint `proposition-lattices-representations-normal-scheme`, steps 6, 7, 9 and 10
(auxiliary; not a blueprint node).

Indices `n : ℕ` denote the positive exponent `n + 1`. A module over the coefficient
quotient is represented by its underlying module over the valuation ring, annihilated
by the corresponding ideal. Surjectivity and the specified kernel say that the
transition induces the required quotient isomorphism.
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped Pointwise
open Topology

namespace Padic

private theorem coefficientIntegers_complete (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsAdicComplete (coefficientExtensionMaximalIdeal l E)
      (coefficientExtensionIntegers l E) := by
  let R := coefficientExtensionIntegers l E
  let J := coefficientExtensionMaximalIdeal l E
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hR : ∀ x : E, x ∈ R ↔ coefficientExtensionAbsoluteValue l E x ≤ 1 := h.1
  let : IsLocalRing R := h.2.2.2.1
  let : IsDiscreteValuationRing R := h.2.2.2.2.2.2.2.1
  have hJ : J = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  let : NormedField E := spectralNorm.normedField ℚ_[l] E
  let : NormedSpace ℚ_[l] E := spectralNorm.normedSpace ℚ_[l] E
  let : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  have hball : (R : Set E) = Metric.closedBall 0 1 := by
    ext x
    change x ∈ R ↔ _
    rw [hR]
    simp only [Metric.mem_closedBall, dist_zero_right]
    rfl
  have : CompactSpace R := by
    rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype]
    change IsCompact (R : Set E)
    rw [hball]
    exact isCompact_closedBall (0 : E) 1
  change IsAdicComplete J R
  rw [hJ]
  refine { prec' := ?_ }
  intro f hf
  let S n : Set R := f n +ᵥ (((IsLocalRing.maximalIdeal R) ^ n : Ideal R) : Set R)
  have hS n : S (n + 1) ⊆ S n := by
    apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
    simpa [S] using (hf n.le_succ).symm
  have hc n : IsClosed (S n) :=
    (IsNoetherianRing.isClosed_ideal ((IsLocalRing.maximalIdeal R) ^ n)).vadd (f n)
  obtain ⟨L, hL⟩ := (hc 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hS (by simp [S]) hc
  refine ⟨L, fun n ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
  simpa [SModEq.sub_mem] using hy

end Padic
