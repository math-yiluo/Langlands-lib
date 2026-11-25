/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersModPow

/-!
# The residue field of the ring of integers of a subfield of `ℚ̄_ℓ`

Let `E` be a subfield of `ℚ̄_ℓ = PadicAlgCl ℓ` with ring of integers
`𝒪_E = PadicAlgCl.integers ℓ E`, topologised as a subspace of `E` with the norm restricted from
`ℚ̄_ℓ` (`PadicAlgCl.normedFieldOfAlgebra`). This file sets up the residue field
`PadicAlgCl.integersResidueField ℓ E = 𝒪_E ⧸ 𝔪_E` with the discrete topology, and proves that the
residue map `𝒪_E ⟶ 𝒪_E ⧸ 𝔪_E` is continuous (`PadicAlgCl.continuous_integersResidue`): its
fibres are open balls of radius `1`. The prime `ℓ` is zero in the residue field
(`PadicAlgCl.natCast_eq_zero_integersResidueField`).
-/

@[expose] public section

open Topology NNReal

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]

/-- The residue field `𝒪_E ⧸ 𝔪_E` of the ring of integers of a subfield `E ⊆ ℚ̄_ℓ`, with the
discrete topology. -/
def integersResidueField : Type :=
  IsLocalRing.ResidueField (integers l E)

noncomputable instance : Field (integersResidueField l E) :=
  inferInstanceAs (Field (IsLocalRing.ResidueField (integers l E)))

instance : TopologicalSpace (integersResidueField l E) := ⊥

instance : DiscreteTopology (integersResidueField l E) := ⟨rfl⟩

/-- `𝔽_E` is a topological ring. All occurrences of `IsTopologicalRing 𝔽_E` should be this named
instance: kernel checks comparing terms built from different (definitionally equal) proofs of
`IsTopologicalRing 𝔽_E` can be very expensive. -/
instance isTopologicalRing_integersResidueField : IsTopologicalRing (integersResidueField l E) :=
  DiscreteTopology.topologicalRing

/-- The residue map `𝒪_E → 𝒪_E ⧸ 𝔪_E`. -/
noncomputable def integersResidue : integers l E →+* integersResidueField l E :=
  IsLocalRing.residue _

lemma integersResidue_surjective : Function.Surjective (integersResidue l E) :=
  IsLocalRing.residue_surjective

/-- An integer of `E` lies in the maximal ideal if and only if its norm is `< 1`. -/
lemma mem_maximalIdeal_integers_iff (x : integers l E) :
    x ∈ IsLocalRing.maximalIdeal (integers l E) ↔ ‖algebraMap E (PadicAlgCl l) (x : E)‖ < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff]
  unfold integers
  rw [← (Valuation.isEquiv_valuation_valuationSubring (valuationOfAlgebra l E)).lt_one_iff_lt_one]
  change valuationOfAlgebra l E (x : E) < 1 ↔ _
  rw [valuationOfAlgebra_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

lemma integersResidue_eq_iff (x y : integers l E) :
    integersResidue l E x = integersResidue l E y ↔
      ‖algebraMap E (PadicAlgCl l) ((x : E) - y)‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub]
  exact (IsLocalRing.residue_eq_zero_iff _).trans (mem_maximalIdeal_integers_iff l E _)

/-- The residue map `𝒪_E → 𝒪_E ⧸ 𝔪_E` is continuous: its fibres are open balls of radius `1`. -/
lemma continuous_integersResidue :
    letI := normedFieldOfAlgebra l E
    Continuous (integersResidue l E) := by
  let := normedFieldOfAlgebra l E
  refine continuous_discrete_rng.2 fun q ↦ ?_
  obtain ⟨x, rfl⟩ := integersResidue_surjective l E q
  have : integersResidue l E ⁻¹' {integersResidue l E x} =
      Subtype.val ⁻¹' Metric.ball (x : E) 1 := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball, dist_eq_norm]
    exact integersResidue_eq_iff l E y x
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

/-- The prime `ℓ` is zero in the residue field of `𝒪_E`. -/
lemma natCast_eq_zero_integersResidueField : (l : integersResidueField l E) = 0 := by
  rw [← map_natCast (integersResidue l E)]
  refine (IsLocalRing.residue_eq_zero_iff _).2 ((mem_maximalIdeal_integers_iff l E _).2 ?_)
  rw [show ((l : integers l E) : E) = (l : E) by simp, norm_algebraMap_natCast_self]
  exact inv_prime_lt_one l

end PadicAlgCl
