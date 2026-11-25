/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# Power series over a field or Cohen ring

Source: Stacks Project, Algebra, Remark Tag 032C and Definition Tag 0327
(blueprint: lem-weil-pbc-power-series-field-cohen-regular-complete).
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace MvPowerSeries

private theorem maximalIdeal_eq_comap {A : Type u} [CommRing A] [IsLocalRing A]
    (d : ℕ) : IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A) =
      (IsLocalRing.maximalIdeal A).comap constantCoeff := by
  ext f
  simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_constantCoeff]

private theorem maximalIdeal_eq_map_sup {A : Type u} [CommRing A] [IsLocalRing A]
    (d : ℕ) : IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A) =
      (IsLocalRing.maximalIdeal A).map C ⊔ Ideal.span (Set.range (X : Fin d → _)) := by
  have hk := (quotient_first_variables A d d le_rfl).2.2.2.2.1
  rw [maximalIdeal_eq_comap]
  apply le_antisymm
  · intro f hf
    have hdiff : f - C (constantCoeff f) ∈ RingHom.ker (constantCoeff (σ := Fin d)) := by
      simp
    rw [hk] at hdiff
    have hc := Ideal.mem_map_of_mem (C : A →+* MvPowerSeries (Fin d) A)
      (show constantCoeff f ∈ IsLocalRing.maximalIdeal A from hf)
    simpa using (Submodule.mem_sup.mpr ⟨_, hc, _, hdiff, add_sub_cancel _ _⟩)
  · apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · rw [← hk]
      exact Ideal.comap_mono bot_le

private theorem dimension_lower {A : Type u} [CommRing A] (d : ℕ) :
    ringKrullDim A + (d : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin d) A) := by
  induction d with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    exact (ringKrullDim_eq_of_ringEquiv (isEmptyEquiv (Fin 0) A).toRingEquiv).ge
  | succ d ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    calc
      ringKrullDim A + (d : WithBot ℕ∞) + 1 ≤
          ringKrullDim (MvPowerSeries (Fin d) A) + 1 := by
            simpa only [add_comm] using add_le_add_right ih 1
      _ ≤ ringKrullDim (PowerSeries (MvPowerSeries (Fin d) A)) :=
        ringKrullDim_succ_le_ringKrullDim_powerseries
      _ = ringKrullDim (MvPowerSeries (Fin (d + 1)) A) :=
        (ringKrullDim_eq_of_ringEquiv (finSuccEquiv A d).toRingEquiv).symm

private theorem residue_equiv {A : Type u} [CommRing A] [IsLocalRing A] (d : ℕ)
    (J : Ideal A) (hJ : IsLocalRing.maximalIdeal A = J) :
    ∃ e : (A ⧸ J) ≃+*
        (MvPowerSeries (Fin d) A ⧸ IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A)),
      ∀ a : A, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (C a) := by
  classical
  have hm : IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A) = J.comap constantCoeff := by
    rw [maximalIdeal_eq_comap, hJ]
  let q := Ideal.quotientMap J (constantCoeff : MvPowerSeries (Fin d) A →+* A) hm.le
  have hq : Function.Bijective q := by
    constructor
    · rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
      intro x hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk J (constantCoeff f) = 0 at hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [hm]
      change constantCoeff f ∈ J
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
    · intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨Ideal.Quotient.mk _ (C a), by simp [q]⟩
  let e := RingEquiv.ofBijective q hq
  refine ⟨e.symm, fun a ↦ ?_⟩
  apply e.injective
  simp [e, q]

private theorem rank_variables_le {A : Type u} [CommRing A] (d : ℕ) :
    (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) A))).spanFinrank ≤ d := by
  calc
    _ ≤ (Set.range (X : Fin d → MvPowerSeries (Fin d) A)).ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
    _ ≤ d := by
      simpa only [Set.image_univ, Set.ncard_univ, Nat.card_fin] using
        Set.ncard_image_le (s := (Set.univ : Set (Fin d)))
        (f := (X : Fin d → MvPowerSeries (Fin d) A))

private theorem rank_cohen_variables_le {A : Type u} [CommRing A] (d p : ℕ) :
    (Ideal.span (insert (C (p : A))
      (Set.range (X : Fin d → MvPowerSeries (Fin d) A)))).spanFinrank ≤ d + 1 := by
  calc
    _ ≤ (insert (C (p : A)) (Set.range (X : Fin d → MvPowerSeries (Fin d) A))).ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite ((Set.finite_range _).insert _)
    _ ≤ (Set.range (X : Fin d → MvPowerSeries (Fin d) A)).ncard + 1 :=
      Set.ncard_insert_le _ _
    _ ≤ d + 1 := by
      gcongr
      simpa only [Set.image_univ, Set.ncard_univ, Nat.card_fin] using
        Set.ncard_image_le (s := (Set.univ : Set (Fin d)))
        (f := (X : Fin d → MvPowerSeries (Fin d) A))

/-- A finite-variable power series ring over a field or Cohen ring is complete,
regular local, and has the expected dimension.

Source: Stacks Project, Algebra, Remark Tag 032C; Cohen rings are Definition Tag 0327.
(blueprint: lem-weil-pbc-power-series-field-cohen-regular-complete)

Proof (the blueprint's eight steps):
1. A field is Noetherian, local, and a domain; a Cohen ring is a local PID, hence
   Noetherian and a domain. Its nonzero maximal ideal is generated by p, so p is nonzero
   (def-weil-pbc-cohen-ring, def-weil-pbc-noetherian-ring).
2. Apply lem-weil-pbc-power-series-noetherian and lem-weil-pbc-power-series-domain to
   the coefficient ring, using def-weil-pbc-multivariate-power-series.
3. By lem-weil-pbc-power-series-local-ring the maximal ideal consists of series whose
   constant coefficient is in the coefficient maximal ideal. Split each series into its
   constant term and the remaining series. By lem-weil-pbc-power-series-quotient-variables
   the latter lies in the variables' ideal. This gives the displayed maximal ideal.
4. The composite coefficient map to the quotient is surjective since every series is
   congruent to its constant coefficient. Its kernel is the coefficient maximal ideal
   by step 3. The induced quotient map is therefore the stated ring isomorphism.
5. Over a field apply lem-weil-pbc-power-series-variables-complete. Over a Cohen ring
   apply lem-weil-pbc-power-series-complete-over-complete-base to the complete ideal pΛ
   (def-weil-pbc-adically-complete-ring, def-weil-pbc-cohen-ring).
6. The maximal ideal has d generators over a field and d+1 over a Cohen ring. Apply
   lem-weil-pbc-noetherian-local-dimension-le-generators for the dimension upper bound.
7. The ideals generated by the first i variables, for 0 ≤ i ≤ d, are prime: their
   quotients are power series domains by lem-weil-pbc-power-series-quotient-variables
   and lem-weil-pbc-power-series-domain. Each inclusion is strict because the next
   variable survives the quotient. In the Cohen case p survives the quotient by all
   variables and extends this chain by one strict inclusion into the maximal ideal.
   This gives the dimension lower bound (def-weil-pbc-krull-dimension-ring).
8. The two bounds give the stated dimension. The displayed maximal-ideal generators
   number exactly this dimension, proving regularity (def-weil-regular-scheme).
-/
theorem power_series_field_cohen_regular_complete
    {Λ : Type u} [CommRing Λ] (d : ℕ)
    (hΛ : IsField Λ ∨ (∃ p : ℕ, IsCohenRing p Λ)) :
    ((IsField Λ ∧
        ∃ (_ : IsNoetherianRing (MvPowerSeries (Fin d) Λ))
          (_ : IsDomain (MvPowerSeries (Fin d) Λ)) (_ : IsLocalRing (MvPowerSeries (Fin d) Λ)),
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ) =
              Ideal.span (Set.range (fun i : Fin d ↦
                (MvPowerSeries.X i : (MvPowerSeries (Fin d) Λ)))) ∧
            ∃ e : (Λ ⧸ (⊥ : Ideal Λ)) ≃+*
                ((MvPowerSeries (Fin d) Λ) ⧸ IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ)),
              (∀ a : Λ, e (Ideal.Quotient.mk _ a) =
                Ideal.Quotient.mk _ (MvPowerSeries.C a)) ∧
            IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ))
              (MvPowerSeries (Fin d) Λ) ∧
            IsRegularLocalRing (MvPowerSeries (Fin d) Λ) ∧
            ringKrullDim (MvPowerSeries (Fin d) Λ) = (d : WithBot ℕ∞)) ∨
      (∃ p : ℕ, IsCohenRing p Λ ∧
        ∃ (_ : IsNoetherianRing (MvPowerSeries (Fin d) Λ))
          (_ : IsDomain (MvPowerSeries (Fin d) Λ)) (_ : IsLocalRing (MvPowerSeries (Fin d) Λ)),
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ) =
              Ideal.span (insert (MvPowerSeries.C (p : Λ))
                (Set.range (fun i : Fin d ↦
                  (MvPowerSeries.X i : (MvPowerSeries (Fin d) Λ))))) ∧
            ∃ e : (Λ ⧸ Ideal.span {(p : Λ)}) ≃+*
                ((MvPowerSeries (Fin d) Λ) ⧸ IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ)),
              (∀ a : Λ, e (Ideal.Quotient.mk _ a) =
                Ideal.Quotient.mk _ (MvPowerSeries.C a)) ∧
            IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ))
              (MvPowerSeries (Fin d) Λ) ∧
            IsRegularLocalRing (MvPowerSeries (Fin d) Λ) ∧
            ringKrullDim (MvPowerSeries (Fin d) Λ) = ((d + 1 : ℕ) : WithBot ℕ∞))) := by
  classical
  rcases hΛ with hfield | ⟨p, hp⟩
  · let := hfield.toField
    have : IsDomain (MvPowerSeries (Fin d) Λ) := NoZeroDivisors.to_isDomain _
    have hm : IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ) =
        Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) Λ)) := by
      rw [maximalIdeal_eq_map_sup, IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot, bot_sup_eq]
    have hlo : (d : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin d) Λ) := by
      simpa [ringKrullDim_eq_zero_of_isField hfield] using dimension_lower (A := Λ) d
    have hrank : (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ)).spanFinrank ≤ d := by
      rw [hm]
      exact rank_variables_le d
    have hrank' : ((IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ)).spanFinrank :
        WithBot ℕ∞) ≤ d := by exact_mod_cast hrank
    have hdim := le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans hrank') hlo
    have hreg : IsRegularLocalRing (MvPowerSeries (Fin d) Λ) :=
      IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hrank'.trans hlo)
    obtain ⟨e, he⟩ := residue_equiv (A := Λ) d ⊥ IsLocalRing.maximalIdeal_eq_bot
    refine Or.inl ⟨hfield, inferInstance, inferInstance, inferInstance, hm, e, he, ?_,
      hreg, hdim⟩
    rw [hm]
    infer_instance
  · have hcohen := hp
    obtain ⟨hprime, hdomain, hdvr, hmax, hcomplete⟩ := hp
    let := hdomain
    let := hdvr
    let := hcomplete
    have : IsDomain (MvPowerSeries (Fin d) Λ) := NoZeroDivisors.to_isDomain _
    have hm : IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ) =
        Ideal.span (insert (C (p : Λ))
          (Set.range (X : Fin d → MvPowerSeries (Fin d) Λ))) := by
      rw [maximalIdeal_eq_map_sup, hmax, Ideal.map_span, Set.image_singleton,
        ← Ideal.span_insert]
    have hlo : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin d) Λ) := by
      have hbase : ringKrullDim Λ = 1 :=
        IsPrincipalIdealRing.ringKrullDim_eq_one Λ (IsDiscreteValuationRing.not_isField Λ)
      simpa only [hbase, Nat.cast_add, Nat.cast_one, add_comm] using dimension_lower (A := Λ) d
    have hrank : (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ)).spanFinrank ≤ d + 1 := by
      rw [hm]
      exact rank_cohen_variables_le d p
    have hrank' : ((IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) Λ)).spanFinrank :
        WithBot ℕ∞) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hrank
    have hdim := le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans hrank') hlo
    have hreg : IsRegularLocalRing (MvPowerSeries (Fin d) Λ) :=
      IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hrank'.trans hlo)
    obtain ⟨e, he⟩ := residue_equiv (A := Λ) d (Ideal.span {(p : Λ)}) hmax
    refine Or.inr ⟨p, hcohen, inferInstance, inferInstance, inferInstance, hm, e, he, ?_,
      hreg, hdim⟩
    have hc := power_series_complete_over_complete_base Λ (Ideal.span {(p : Λ)}) d
    rw [hm]
    simpa only [Ideal.map_span, Set.image_singleton, ← c_eq_algebraMap, ← Ideal.span_insert]
      using hc

end MvPowerSeries
