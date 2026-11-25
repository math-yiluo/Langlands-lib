/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-! Core valuation-ring existence for a finite extension of a p-adic field.

This is the ring-theoretic and finite-residue-field portion of
`Padic.extension_integers_dvr`; the uniformizer association and factorization clauses
are supplied separately.

Source: Serre, Local Fields, Chapter II, §2, Proposition 3.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

namespace Padic

/-- The valuation ring and maximal ideal with all ring-theoretic properties needed before
uniformizer factorization.  This theorem is a strict substatement of
`extension_integers_dvr` and is intended as its ring-theoretic core.

Source: Serre, Local Fields, Chapter II, §2, Proposition 3.
Proof: Equip the finite extension with the extending nonarchimedean norm, apply the
properness criterion for valued fields, and identify the resulting integer ring and
maximal ideal with the absolute-value inequalities.  The DVR and finite-residue-field
properties, together with the elementary unit and fraction-field arguments, give exactly
the displayed conjunction.
(auxiliary; not a blueprint node)
-/
theorem extension_integers_dvr_core (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (abv : AbsoluteValue E ℝ)
    (h_ext : ∀ a : ℚ_[l], abv (algebraMap ℚ_[l] E a) = ‖a‖) :
    ∃ O : Subring E, ∃ m : Ideal O,
      (∀ x : E, x ∈ O ↔ abv x ≤ 1) ∧
      (∀ x : O, x ∈ m ↔ abv (x : E) < 1) ∧
      (∀ x : O, IsUnit x ↔ abv (x : E) = 1) ∧
      IsLocalRing O ∧ m.IsMaximal ∧
      (∀ J : Ideal O, J.IsMaximal → J = m) ∧
      IsFractionRing O E ∧
      IsDiscreteValuationRing O ∧ IsPrincipalIdealRing O ∧ m ≠ ⊥ ∧
      (∀ J : Ideal O, J.IsPrime ∧ J ≠ ⊥ ↔ J = m) ∧
      Finite (O ⧸ m) ∧
      (∃ r : ℝ,
        (∃ y : O, y ∈ m ∧ y ≠ 0 ∧ abv (y : E) = r) ∧
        (∀ y : O, y ∈ m → y ≠ 0 → abv (y : E) ≤ r) ∧
        (∀ π : O, Ideal.span ({π} : Set O) = m ↔
          π ≠ 0 ∧ abv (π : E) = r)) ∧
      (∃ π : O, Ideal.span ({π} : Set O) = m) := by
  let : NormedField E := abv.toNormedField
  let : NormedAlgebra ℚ_[l] E :=
    { norm_smul_le a x := by
        change abv (a • x) ≤ ‖a‖ * abv x
        rw [Algebra.smul_def, map_mul, h_ext] }
  let : NontriviallyNormedField E :=
    { abv.toNormedField with
      non_trivial := by
        obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm ℚ_[l]
        exact ⟨algebraMap ℚ_[l] E a, by simpa only [norm_algebraMap'] using ha⟩ }
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  let : Valued E NNReal := NormedField.toValued
  have : (Valued.v : Valuation E NNReal).RankOne :=
    inferInstanceAs (NormedField.valuation (K := E)).RankOne
  have hi : (Valued.integer E : Set E) = Metric.closedBall 0 1 := by
    ext x
    change ‖x‖₊ ≤ 1 ↔ _
    simp [← NNReal.coe_le_coe]
  have : CompactSpace (Valued.integer E) := by
    rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype]
    change IsCompact (Valued.integer E : Set E)
    rw [hi]
    exact isCompact_closedBall (0 : E) 1
  have h := open Valued.integer in
    compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
      (K := E) (Γ₀ := NNReal) |>.mp (inferInstance : CompactSpace (Valued.integer E))
  let : IsDiscreteValuationRing (Valued.integer E) := h.2.1
  have hmem (x : E) : x ∈ Valued.integer E ↔ abv x ≤ 1 := by
    change ‖x‖₊ ≤ 1 ↔ _
    exact NNReal.coe_le_coe.symm
  have hunit (x : Valued.integer E) : IsUnit x ↔ abv (x : E) = 1 := by
    exact Valued.integer.isUnit_iff_norm_eq_one
  have hmax (x : Valued.integer E) :
      x ∈ IsLocalRing.maximalIdeal (Valued.integer E) ↔ abv (x : E) < 1 := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    exact ⟨lt_of_le_of_ne ((hmem _).mp x.property), fun hx ↦ hx.ne⟩
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible (Valued.integer E)
  have hdvd (x y : Valued.integer E) : x ∣ y ↔ abv (y : E) ≤ abv (x : E) := by
    have hv := (Valuation.integer.integers (NormedField.valuation (K := E))).dvd_iff_le
      (x := x) (y := y)
    change x ∣ y ↔ ‖(y : E)‖₊ ≤ ‖(x : E)‖₊ at hv
    exact hv.trans NNReal.coe_le_coe.symm
  have hgen (π : Valued.integer E) :
      Ideal.span ({π} : Set (Valued.integer E)) =
        IsLocalRing.maximalIdeal (Valued.integer E) ↔ abv (π : E) = abv (ρ : E) := by
    rw [hρ.maximalIdeal_eq, Ideal.span_singleton_eq_span_singleton,
      ← dvd_dvd_iff_associated, hdvd, hdvd, and_comm, ← le_antisymm_iff]
  refine ⟨Valued.integer E, IsLocalRing.maximalIdeal (Valued.integer E), hmem, hmax,
    hunit, inferInstance, inferInstance, fun J hJ ↦ IsLocalRing.eq_maximalIdeal hJ,
    inferInstance, inferInstance, inferInstance,
    IsDiscreteValuationRing.not_a_field (Valued.integer E), ?_, h.2.2, ?_,
    ⟨ρ, hρ.maximalIdeal_eq.symm⟩⟩
  · intro J
    constructor
    · rintro ⟨hprime, hne⟩
      let : J.IsPrime := hprime
      exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne)
    · rintro rfl
      exact ⟨inferInstance, IsDiscreteValuationRing.not_a_field (Valued.integer E)⟩
  · refine ⟨abv (ρ : E), ⟨ρ, ?_, hρ.ne_zero, rfl⟩, ?_, ?_⟩
    · rw [hρ.maximalIdeal_eq]
      exact Ideal.subset_span (Set.mem_singleton ρ)
    · intro y hy _
      rw [hρ.maximalIdeal_eq, Ideal.mem_span_singleton] at hy
      exact (hdvd ρ y).mp hy
    · intro π
      constructor
      · intro hπ
        exact ⟨((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ.symm).ne_zero,
          (hgen π).mp hπ⟩
      · rintro ⟨_, hπ⟩
        exact (hgen π).mpr hπ

end Padic
