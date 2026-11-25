/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Jacobson.Ideal

import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Reduction of a semilocal Dedekind domain to discrete valuation rings

Source: Stacks Project, Algebra, Tags 034W and 034X, and Varieties, Lemma 33.37.8
(Tag 09N5), the reduction to local rings
(blueprint: lem-sc-semilocal-dedekind-dvr-reduction).
-/

@[expose] public section

universe u v

namespace MaximalSpectrum

/-- A semilocal Dedekind domain of dimension one has finitely many
maximal ideals. Its localizations there are DVRs with the original fraction field; an element
of that field comes from the Jacobson radical precisely when it comes from the maximal ideal
of each localization. The local algebra structures are the canonical localization embeddings.
Mathlib's Dedekind predicate permits dimension zero, so dimension one is stated
separately to retain the node's convention.
Source: Stacks Project, Algebra, Tags 034W and 034X; Varieties, Tag 09N5, local-ring reduction
(blueprint: lem-sc-semilocal-dedekind-dvr-reduction).

Proof:
1. Semilocality says that the maximal spectrum is finite. Dimension one and the domain
   hypothesis imply that each maximal ideal is a nonzero prime.
2. Apply `lem-sc-dedekind-localization-dvr` to each such prime. The canonical embedding
   identifies the fraction field of its localization with the original field: every fraction
   of elements of the base ring is also a fraction of elements of the localization.
3. An element from the Jacobson radical belongs to every maximal ideal, hence to every
   localized maximal ideal. Conversely, membership in all the localized maximal ideals
   first implies membership in all localizations. The intersection assertion of
   `lem-sc-dedekind-intersection-localizations` puts it in the base ring, and the contraction
   assertion puts it in each maximal ideal of the base ring, hence in its Jacobson radical. -/
theorem semilocal_dedekind_dvr_reduction
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K] :
    let a := fun m : MaximalSpectrum B =>
      IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime m.asIdeal) K
        m.asIdeal.primeCompl (nonZeroDivisors B) m.asIdeal.primeCompl_le_nonZeroDivisors
    Finite (MaximalSpectrum B) ∧
      (∀ m : MaximalSpectrum B,
        letI := a m
        IsDiscreteValuationRing (Localization.AtPrime m.asIdeal) ∧
          IsFractionRing (Localization.AtPrime m.asIdeal) K) ∧
      (∀ x : K,
        (∃ b : B, b ∈ Ideal.jacobson (⊥ : Ideal B) ∧ algebraMap B K b = x) ↔
          ∀ m : MaximalSpectrum B,
            letI := a m
            ∃ y : Localization.AtPrime m.asIdeal,
              y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) ∧
                algebraMap (Localization.AtPrime m.asIdeal) K y = x) := by
  let a := fun m : MaximalSpectrum B ↦
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime m.asIdeal) K
      m.asIdeal.primeCompl (nonZeroDivisors B) m.asIdeal.primeCompl_le_nonZeroDivisors
  have tower (m : MaximalSpectrum B) :
      let := a m
      IsScalarTower B (Localization.AtPrime m.asIdeal) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _
      m.asIdeal.primeCompl_le_nonZeroDivisors
  have frac (m : MaximalSpectrum B) :
      let := a m
      IsFractionRing (Localization.AtPrime m.asIdeal) K := by
    let := a m
    let := tower m
    exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      m.asIdeal.primeCompl _ _
  refine ⟨inferInstance, ?_, ?_⟩
  · intro m
    let := a m
    refine ⟨?_, frac m⟩
    apply IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
      (P := m.asIdeal) (Aₘ := _)
    exact Ring.ne_bot_of_isMaximal_of_not_isField m.isMaximal fun h ↦ by
      have hz := ringKrullDim_eq_zero_of_isField h
      rw [hdim] at hz
      exact one_ne_zero hz
  · intro x
    constructor
    · rintro ⟨b, hb, rfl⟩ m
      let := a m
      let := tower m
      refine ⟨algebraMap B (Localization.AtPrime m.asIdeal) b, ?_, ?_⟩
      · apply (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m.asIdeal b).mpr
        exact (sInf_le (show m.asIdeal ∈
          {J : Ideal B | (⊥ : Ideal B) ≤ J ∧ J.IsMaximal} from ⟨bot_le, m.isMaximal⟩)) hb
      · exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime m.asIdeal) K b).symm
    · intro hx
      have hlocal : x ∈ ⨅ m : MaximalSpectrum B,
          Localization.subalgebra.ofField K _ m.asIdeal.primeCompl_le_nonZeroDivisors := by
        rw [Algebra.mem_iInf]
        intro m
        let := a m
        obtain ⟨y, hy, he⟩ := hx m
        apply (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField K
          m.asIdeal.primeCompl m.asIdeal.primeCompl_le_nonZeroDivisors
          (Localization.AtPrime m.asIdeal) x).mp
        exact ⟨y, he⟩
      rw [MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at hlocal
      obtain ⟨b, hb⟩ := hlocal
      refine ⟨b, ?_, hb⟩
      apply Ideal.mem_sInf.mpr
      rintro J ⟨hJ, hmax⟩
      let m : MaximalSpectrum B := ⟨J, hmax⟩
      let := a m
      let := tower m
      let := frac m
      obtain ⟨y, hy, he⟩ := hx m
      have heq : algebraMap B (Localization.AtPrime m.asIdeal) b = y := by
        apply IsFractionRing.injective (Localization.AtPrime m.asIdeal) K
        rw [← IsScalarTower.algebraMap_apply, hb, he]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m.asIdeal b).mp
        (heq.symm ▸ hy)

end MaximalSpectrum
