/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.FiniteLengthOfFiniteMaximalSupport
import WeilConjectures.RingTheory.FiniteMaximalsOverElement
import WeilConjectures.RingTheory.LengthQuotSMulTopFractionFieldSubmodule

/-!
# Global finite length for a fraction-field submodule

Source: Stacks Project, Algebra, Tag 00PF, `lemma-finite-length-global`
(blueprint: lem-sc-finite-length-global-submodule).
-/

@[expose] public section

universe u v

namespace Submodule

/-- For a Noetherian domain of dimension one, every submodule of a finite power of its
fraction field has finite length after reduction modulo a nonzero scalar.
Source: Stacks Project, Algebra, Tag 00PF, `lemma-finite-length-global`
(blueprint: lem-sc-finite-length-global-submodule).

Proof (the node's four steps):
1. If `x` is a unit, then `xM = M`, and the quotient is zero, of length zero
   (`def-weil-pbc-module-length`).
2. Otherwise `lem-sc-finite-maximals-over-element` supplies the finite set `S` of maximal
   ideals containing `x`. At each of these ideals the localized ring is a Noetherian local
   domain of dimension one with fraction field `K`; the localized module remains a submodule
   of `K^r`. Apply `lem-weil-pbc-dim-one-submodule-quotient-finite-length` to obtain finite
   length of each localized quotient.
3. Write `Q = M/xM`. Since `x` kills `Q`, its localizations outside `S` vanish. A nonzero
   subquotient has a nonzero element whose proper annihilator lies in a maximal ideal.
   This ideal contains `x`, so belongs to `S`; localization there preserves nonzeroness.
   Thus every strict submodule inclusion in `Q` remains strict at some ideal in `S`.
4. Assign each step of a strict chain in `Q` to one such ideal. At a fixed ideal, the number
   of assigned steps is bounded by the finite local length from step 2. Summing these bounds
   over `S` bounds every chain length, so `Module.length R Q` is finite
   (`def-weil-pbc-module-length`). -/
theorem length_quotSMulTop_lt_top_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (r : ℕ) (M : Submodule R (Fin r → K)) (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ≠ 0) : Module.length R (QuotSMulTop x M) < ⊤ := by
  classical
  let : MulActionWithZero R (Submodule R M) := Submodule.pointwiseMulActionWithZero
  let S : Set (MaximalSpectrum R) := {m | x ∈ m.asIdeal}
  have hS : S.Finite := by
    have h := Ring.finite_maximalIdeals_containing_nonzero R hdim x hx
    have h' := h.preimage (show Function.Injective
      (fun m : MaximalSpectrum R ↦ m.asIdeal) from fun a b hab ↦ MaximalSpectrum.ext hab).injOn
    exact h'.subset (fun m hm ↦ ⟨m.isMaximal, hm⟩)
  apply Module.length_lt_top_of_finite_maximal_support S hS
  · intro m hm
    apply LocalizedModule.subsingleton_iff.mpr
    intro q
    exact ⟨x, hm, Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M x) q⟩
  · intro m hm
    let A := Localization.AtPrime m.asIdeal
    let φ : A →ₐ[R] K := IsLocalization.liftAlgHom
      (f := Algebra.ofId R K) (fun s : m.asIdeal.primeCompl ↦ by
        apply isUnit_iff_ne_zero.mpr
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.mpr (fun hs ↦ s.2 (hs ▸ m.asIdeal.zero_mem))))
    let : Algebra A K := φ.toRingHom.toAlgebra
    have : IsScalarTower R A K := IsScalarTower.of_algHom φ
    have : IsFractionRing A K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.asIdeal.primeCompl A K
    have : IsDomain A := IsLocalization.isDomain_of_atPrime A m.asIdeal
    have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A m.asIdeal
    have : IsNoetherianRing A :=
      IsLocalization.isNoetherianRing m.asIdeal.primeCompl A inferInstance
    have hA : ringKrullDim A = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal A]
      have hne : m.asIdeal ≠ ⊥ := by
        intro h
        exact hx (by simpa [S, h] using hm)
      have hlo := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
      have hhi := m.asIdeal.height_le_ringKrullDim_of_isPrime
      rw [hdim] at hhi
      rw [Ideal.height_bot, zero_add] at hlo
      exact le_antisymm hhi (WithBot.coe_le_coe.mpr hlo)
    have hid : IsLocalizedModule m.asIdeal.primeCompl
        (LinearMap.id : (Fin r → K) →ₗ[R] (Fin r → K)) :=
      isLocalizedModule_id _ _ A
    let L : Submodule A (Fin r → K) :=
      M.localized' A m.asIdeal.primeCompl LinearMap.id
    let f : M →ₗ[R] L := M.toLocalized' A m.asIdeal.primeCompl LinearMap.id
    have hax : algebraMap R A x ≠ 0 := fun h ↦
      hx (IsLocalization.injective A m.asIdeal.primeCompl_le_nonZeroDivisors
        (h.trans (map_zero _).symm))
    have hloc := (length_quotSMulTop_le_of_ringKrullDim_eq_one_of_isLocalRing
      r L hA (algebraMap R A x) hax).2.1
    let : MulActionWithZero A (Submodule A L) := Submodule.pointwiseMulActionWithZero
    have heq : (x • (⊤ : Submodule R M)).localized' A m.asIdeal.primeCompl f =
        (algebraMap R A x) • (⊤ : Submodule A L) := by
      rw [← ideal_span_singleton_smul, Submodule.localized'_smul,
        Submodule.localized'_top]
      change (Submodule.span R {x}).localized' A m.asIdeal.primeCompl
        (Algebra.linearMap R A) • ⊤ = _
      rw [Submodule.localized'_span]
      simpa using (ideal_span_singleton_smul (algebraMap R A x)
        (⊤ : Submodule A L))
    let g := (x • (⊤ : Submodule R M)).toLocalizedQuotient'
      A m.asIdeal.primeCompl f
    let e := (IsLocalizedModule.linearEquiv m.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap m.asIdeal.primeCompl (QuotSMulTop x M)) g
      ).extendScalarsOfIsLocalization m.asIdeal.primeCompl A
    rw [e.length_eq]
    change Module.length A
      (L ⧸ (x • (⊤ : Submodule R M)).localized' A m.asIdeal.primeCompl f) < ⊤
    rw [heq]
    exact hloc

end Submodule
