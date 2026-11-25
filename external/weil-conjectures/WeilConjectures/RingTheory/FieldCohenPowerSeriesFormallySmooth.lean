/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.PowerSeriesCohenFormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicUniverseLift
import Mathlib.RingTheory.Smooth.Basic

/-!
# Formal smoothness of field and Cohen power series rings

Source: Stacks Project, More on Algebra, Lemma Tag 07NL, clauses (1) and (3)
(blueprint: lem-weil-pbc-field-cohen-power-series-formally-smooth).
-/

@[expose] public section

universe u v

namespace MvPowerSeries

private theorem field_power_series_lift
    {Λ : Type u} [Field Λ] [CharZero Λ] (n : ℕ)
    (D : Type v) [CommRing D] (J : Ideal D) (hJ : J ^ 2 = ⊥)
    (g : MvPowerSeries (Fin n) Λ →+* D ⧸ J)
    (r : ℕ) (hr : 1 ≤ r)
    (hg : ∀ x ∈ (Ideal.span (Set.range (fun i : Fin n ↦
      (X i : MvPowerSeries (Fin n) Λ)))) ^ r, g x = 0) :
    ∃ h : MvPowerSeries (Fin n) Λ →+* D, (Ideal.Quotient.mk J).comp h = g := by
  have : Algebra.FormallySmooth ℤ ℚ :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors ℤ)
  let gRat := (g.comp (algebraMap ℚ (MvPowerSeries (Fin n) Λ))).toIntAlgHom
  obtain ⟨μ, _⟩ := Algebra.FormallySmooth.comp_surjective ℤ ℚ J hJ gRat
  let : Algebra ℚ D := μ.toRingHom.toAlgebra
  let gQ : MvPowerSeries (Fin n) Λ →ₐ[ℚ] D ⧸ J :=
    { g with commutes' := g.map_rat_algebraMap }
  obtain ⟨h, hh⟩ := Algebra.formallySmoothAdic_lift_universe ℚ _ _
    (formallySmoothAdic_rat Λ n) D J hJ gQ ⟨r, hr, hg⟩
  exact ⟨h.toRingHom, congrArg AlgHom.toRingHom hh⟩

private theorem field_cohen_power_series_lift
    {Λ : Type u} [CommRing Λ] (n : ℕ) (m : Ideal (MvPowerSeries (Fin n) Λ))
    (hΛ : (IsField Λ ∧ CharZero Λ ∧
        m = Ideal.span (Set.range (fun i : Fin n ↦
          (X i : MvPowerSeries (Fin n) Λ)))) ∨
      (∃ p : ℕ, IsCohenRing p Λ ∧
        m = Ideal.span (insert (C (p : Λ))
          (Set.range (fun i : Fin n ↦ (X i : MvPowerSeries (Fin n) Λ))))))
    (D : Type v) [CommRing D] (J : Ideal D) (hJ : J ^ 2 = ⊥)
    (g : MvPowerSeries (Fin n) Λ →+* D ⧸ J)
    (r : ℕ) (hr : 1 ≤ r) (hg : ∀ x ∈ m ^ r, g x = 0) :
    ∃ h : MvPowerSeries (Fin n) Λ →+* D, (Ideal.Quotient.mk J).comp h = g := by
  rcases hΛ with ⟨hfield, hchar, rfl⟩ | ⟨p, hcohen, rfl⟩
  · let : Field Λ := hfield.toField
    let : CharZero Λ := hchar
    exact field_power_series_lift n D J hJ g r hr hg
  · let gZ : MvPowerSeries (Fin n) Λ →ₐ[ℤ] D ⧸ J :=
      { g with commutes' := fun z ↦ by simp }
    obtain ⟨h, hh⟩ := Algebra.formallySmoothAdic_lift_universe ℤ _ _
      (formallySmoothAdic_int_of_isCohenRing p Λ hcohen n) D J hJ gZ
      ⟨r, hr, hg⟩
    exact ⟨h.toRingHom, congrArg AlgHom.toRingHom hh⟩

/-- Power series over a characteristic-zero field or a Cohen ring are formally smooth
 over the integers for the indicated maximal-ideal adic topology, with a bound on lifts.

Source: Stacks Project, More on Algebra, Lemma Tag 07NL, clauses (1) and (3), and
Lemma Tag 07EC for the bound on the lifted map.
(blueprint: lem-weil-pbc-field-cohen-power-series-formally-smooth)

Proof:
1. Unpack theorem-finite-etale-covers-proper-henselian--2: every ring is uniquely a `ℤ`-algebra,
   and its `ℤ`-algebra maps are precisely ring maps (def-weil-pbc-algebra-hom-quotient).
2. In the Cohen case, apply clause (2) of
   lem-weil-pbc-power-series-cohen-formally-smooth-adic to the square-zero test datum,
   using lem-weil-pbc-fs-adic-universe-lift to allow any target universe.
3. In the characteristic-zero field case, compose `ℚ → Λ → R → D/J` and lift this
   map to `ℚ → D` by lem-weil-pbc-localization-square-zero-lifting, since `ℚ` is
   the localization of `ℤ` at nonzero integers. This gives compatible `ℚ`-algebra
   structures on `D` and `D/J` (def-weil-pbc-algebra-hom-quotient).
4. Apply clause (1) of lem-weil-pbc-power-series-cohen-formally-smooth-adic over `ℚ`
   and lem-weil-pbc-fs-adic-universe-lift to obtain the lift in any target universe;
   it is in particular a ring homomorphism over `ℤ`.
5. If `g` kills `m ^ r`, every lift sends `m ^ r` into `J`. Since
   `m ^ (2 * r) = m ^ r * m ^ r`, it sends this ideal into `J ^ 2 = 0`.
   This also supplies continuity, as in theorem-finite-etale-covers-proper-henselian--2. -/
theorem field_cohen_power_series_formally_smooth
    {Λ : Type u} [CommRing Λ] (n : ℕ) (m : Ideal (MvPowerSeries (Fin n) Λ))
    (hΛ : (IsField Λ ∧ CharZero Λ ∧
        m = Ideal.span (Set.range (fun i : Fin n ↦
          (MvPowerSeries.X i : MvPowerSeries (Fin n) Λ)))) ∨
      (∃ p : ℕ, IsCohenRing p Λ ∧
        m = Ideal.span (insert (MvPowerSeries.C (p : Λ))
          (Set.range (fun i : Fin n ↦
            (MvPowerSeries.X i : MvPowerSeries (Fin n) Λ)))))) :
    Algebra.FormallySmoothAdic ℤ (MvPowerSeries (Fin n) Λ) m ∧
      ∀ (D : Type v) [CommRing D] (J : Ideal D), J ^ 2 = ⊥ →
        ∀ (g : MvPowerSeries (Fin n) Λ →+* D ⧸ J) (r : ℕ), 1 ≤ r →
          (∀ x ∈ m ^ r, g x = 0) →
            ∃ h : MvPowerSeries (Fin n) Λ →+* D,
              (Ideal.Quotient.mk J).comp h = g ∧
                ∀ x ∈ m ^ (2 * r), h x = 0 := by
  constructor
  · intro D _ _ J hJ g hg
    obtain ⟨r, hr, hgr⟩ := hg
    obtain ⟨h, hh⟩ := field_cohen_power_series_lift n m hΛ D J hJ g.toRingHom r hr hgr
    refine ⟨{ h with commutes' := fun z ↦ by simp }, ?_⟩
    ext x
    exact DFunLike.congr_fun hh x
  · intro D _ J hJ g r hr hg
    obtain ⟨h, hh⟩ := field_cohen_power_series_lift n m hΛ D J hJ g r hr hg
    refine ⟨h, hh, ?_⟩
    have hm : m ^ r ≤ J.comap h := by
      intro x hx
      change h x ∈ J
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact (DFunLike.congr_fun hh x).trans (hg x hx)
    have hbound : m ^ (2 * r) ≤ (⊥ : Ideal D).comap h := by
      calc
        m ^ (2 * r) = (m ^ r) ^ 2 := by rw [mul_comm 2 r, pow_mul]
        _ ≤ (J.comap h) ^ 2 := Ideal.pow_right_mono hm 2
        _ ≤ (J ^ 2).comap h := Ideal.le_comap_pow h 2
        _ = (⊥ : Ideal D).comap h := by rw [hJ]
    intro x hx
    exact Ideal.mem_bot.mp (hbound hx)

end MvPowerSeries
