/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.PowerSeriesParameterQuotient
import WeilConjectures.RingTheory.FieldCohenPowerSeriesFormallySmooth
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Ring lifts with prescribed parameter values

Source: Stacks Project, Tags 07NQ, 07NM and 07NL.
(blueprint: lem-weil-pbc-power-series-parameter-preserving-ring-lift)
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace MvPowerSeries

private theorem complete_nilpotent {D : Type*} [CommRing D] (a : Ideal D)
    (ha : IsNilpotent a) : IsAdicComplete a D := by
  obtain ⟨N, hN⟩ := ha
  refine { haus' := fun x hx ↦ ?_, prec' := fun f hf ↦ ⟨f N, fun m ↦ ?_⟩ }
  · simpa [hN, SModEq.bot] using hx N
  · by_cases hm : m ≤ N
    · exact hf hm
    · have hNm : N ≤ m := by omega
      have heq : f N = f m := by simpa [hN, SModEq.bot] using hf hNm
      rw [heq]

private theorem nilpotent_span {D : Type*} [CommRing D] {d : ℕ}
    (z : Fin d → D) (hz : ∀ j, IsNilpotent (z j)) :
    IsNilpotent (Ideal.span (Set.range z)) := by
  apply (Ideal.FG.isNilpotent_iff_le_nilradical
    (Submodule.fg_span (Set.finite_range z))).2
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact mem_nilradical.mpr (hz j)

private theorem adjust_coordinates
    {R T Λ D : Type*} [CommRing R] [CommRing T] [CommRing Λ] [CommRing D]
    [Algebra R T] [Algebra R D] [IsLocalRing T]
    (s : List R) (y : List T) (J : Ideal D) (hJ : J ^ 2 = ⊥)
    (g : T →ₐ[R] D ⧸ J)
    (hg : ∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ maximalIdeal T ^ k, g x = 0)
    (f₀ : T →+* D) (hf₀ : (Ideal.Quotient.mk J).comp f₀ = g.toRingHom)
    (e : MvPowerSeries (Fin ((s.map (algebraMap R T) ++ y).length)) Λ ≃+* T)
    (he : ∀ j, e (X j) = (s.map (algebraMap R T) ++ y).get j)
    (hemax : ∀ j, e (X j) ∈ maximalIdeal T) :
    ∃ f : T →+* D, (Ideal.Quotient.mk J).comp f = g.toRingHom ∧
      ∀ r ∈ s, f (algebraMap R T r) = algebraMap R D r := by
  classical
  let z : Fin ((s.map (algebraMap R T) ++ y).length) → D := fun j ↦
    if h : j.val < s.length then algebraMap R D (s.get ⟨j.val, h⟩) else f₀ (e (X j))
  have hz (j : Fin ((s.map (algebraMap R T) ++ y).length)) :
      Ideal.Quotient.mk J (z j) = g (e (X j)) := by
    dsimp [z]
    split_ifs with h
    · rw [he]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left (by simpa using h), List.getElem_map]
      exact (g.commutes (s.get ⟨j.val, h⟩)).symm
    · exact RingHom.congr_fun hf₀ _
  obtain ⟨k, hk, hgk⟩ := hg
  have hzn (j : Fin ((s.map (algebraMap R T) ++ y).length)) : IsNilpotent (z j) := by
    have hzk : z j ^ k ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_pow, hz, ← map_pow]
      exact hgk _ (Ideal.pow_mem_pow (hemax j) k)
    refine ⟨k * 2, ?_⟩
    have hm := Ideal.pow_mem_pow hzk 2
    rw [hJ] at hm
    simpa only [Ideal.mem_bot, pow_mul] using hm
  let a : Ideal D := Ideal.span (Set.range z)
  let : IsAdicComplete a D := complete_nilpotent a (nilpotent_span z hzn)
  let α : Λ →+* D := f₀.comp (e.toRingHom.comp C)
  obtain ⟨Φ, hΦC, hΦX, _, _⟩ := exists_ringHom_of_isAdicComplete a α _ z
    (fun j ↦ Ideal.subset_span ⟨j, rfl⟩)
  let b : Ideal (D ⧸ J) := Ideal.span (Set.range (fun j ↦ g (e (X j))))
  have hbn : IsNilpotent b := nilpotent_span _ (fun j ↦
    ⟨k, by rw [← map_pow]; exact hgk _ (Ideal.pow_mem_pow (hemax j) k)⟩)
  let : IsAdicComplete b (D ⧸ J) := complete_nilpotent b hbn
  obtain ⟨Ψ, _, _, _, huniq⟩ := exists_ringHom_of_isAdicComplete b
    (g.toRingHom.comp (e.toRingHom.comp C)) _ (fun j ↦ g (e (X j)))
    (fun j ↦ Ideal.subset_span ⟨j, rfl⟩)
  have hqΦ : (Ideal.Quotient.mk J).comp Φ = g.toRingHom.comp e.toRingHom := by
    apply (huniq _ ?_ ?_).trans (huniq _ (fun _ ↦ rfl) (fun _ ↦ rfl)).symm
    · intro r
      change Ideal.Quotient.mk J (Φ (C r)) = g (e (C r))
      rw [hΦC]
      exact RingHom.congr_fun hf₀ _
    · intro j
      change Ideal.Quotient.mk J (Φ (X j)) = g (e (X j))
      rw [hΦX]
      exact hz j
  let f := Φ.comp e.symm.toRingHom
  refine ⟨f, ?_, ?_⟩
  · ext x
    change Ideal.Quotient.mk J (Φ (e.symm x)) = g x
    exact (RingHom.congr_fun hqΦ (e.symm x)).trans
      (congrArg g (e.apply_symm_apply x))
  · intro r hr
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr
    let j' : Fin ((s.map (algebraMap R T) ++ y).length) :=
      ⟨j.val, by simp only [List.length_append, List.length_map]; omega⟩
    have hej : e (X j') = algebraMap R T (s.get j) := by
      rw [he]
      simp only [List.get_eq_getElem]
      dsimp only [j']
      rw [List.getElem_append_left (by simp), List.getElem_map]
    change Φ (e.symm (algebraMap R T r)) = algebraMap R D r
    rw [← hj, ← hej, e.symm_apply_apply, hΦX]
    dsimp [z, j']
    rw [dite_eq_left j.isLt]

/-- An unrestricted ring lift can be chosen to agree with the base map on parameters.
No assertion of linearity over the whole base ring is made.
Source: Stacks Project, Tag 07NQ, construction of psi before the defect derivation.
(blueprint: lem-weil-pbc-power-series-parameter-preserving-ring-lift)

Proof: Use the full parameter system i(t),y as power-series coordinates, omitting
p as a variable in the Cohen case (Tag 07NM). Tag 07NL first supplies a ring lift
of g over the prime ring. In the field case D is a rational algebra: every nonzero
integer is invertible modulo J, and invertibility lifts through a square-zero ideal.
Retain the lifted coefficient map; replace the coordinate values belonging to i(t)
by their prescribed images under R -> D, and retain the other lifted values.
The coordinate values are nilpotent, since their k-th powers lie in J and their
2k-th powers vanish. Their finitely generated ideal is nilpotent. Evaluation of
series therefore uses finite truncations and gives a ring map. In D/J its values
on coefficients and coordinates are unchanged, so uniqueness of evaluation makes
its composite equal to g. The p-coordinate already agrees, since ring maps preserve
integers. Empty lists require no replacement. No closed-fibre assumption is used.
-/
theorem exists_parameterPreserving_ringLift
    (ΛR : Type u) (ΛT : Type v) [CommRing ΛR] [CommRing ΛT] (n m : ℕ)
    [IsRegularLocalRing (MvPowerSeries (Fin n) ΛR)]
    [IsRegularLocalRing (MvPowerSeries (Fin m) ΛT)]
    (i : MvPowerSeries (Fin n) ΛR →+* MvPowerSeries (Fin m) ΛT) [IsLocalHom i]
    (t : List (MvPowerSeries (Fin n) ΛR))
    (y : List (MvPowerSeries (Fin m) ΛT))
    (hy : IsRegularSystemOfParameters (t.map i ++ y))
    (hcoeff : (IsField ΛR ∧ IsField ΛT ∧ CharZero ΛR ∧ CharZero ΛT) ∨
      ∃ p : ℕ, p.Prime ∧ IsCohenRing p ΛR ∧ IsCohenRing p ΛT ∧
        t.head? = some (p : MvPowerSeries (Fin n) ΛR)) :
    let R := MvPowerSeries (Fin n) ΛR
    let T := MvPowerSeries (Fin m) ΛT
    letI : Algebra R T := i.toAlgebra
    ∀ (D : Type w) [CommRing D] [Algebra R D] (J : Ideal D), J ^ 2 = ⊥ →
      ∀ g : T →ₐ[R] D ⧸ J,
      (∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ maximalIdeal T ^ k, g x = 0) →
      ∃ f : T →+* D, (Ideal.Quotient.mk J).comp f = g.toRingHom ∧
        ∀ r ∈ t, f (i r) = algebraMap R D r  := by
  classical
  dsimp only
  let R := MvPowerSeries (Fin n) ΛR
  let T := MvPowerSeries (Fin m) ΛT
  let : Algebra R T := i.toAlgebra
  intro D _ _ J hJ g hg
  obtain ⟨k, hk, hgk⟩ := hg
  have : Nontrivial ΛT := ⟨⟨0, 1, fun h ↦ (zero_ne_one : (0 : T) ≠ 1)
    (by simpa using congrArg (C : ΛT →+* T) h)⟩⟩
  have hXmax (j : Fin m) : (X j : T) ∈ maximalIdeal T := by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]
    simp
  have hvarle : Ideal.span (Set.range (X : Fin m → T)) ≤ maximalIdeal T := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hXmax j
  have hg' : ∃ b : ℕ, 1 ≤ b ∧ ∀ x ∈ maximalIdeal T ^ b, g x = 0 :=
    ⟨k, hk, hgk⟩
  rcases hcoeff with ⟨_, hfield, _, hchar⟩ | ⟨p, hp, _, hcohen, hhead⟩
  · let : Field ΛT := hfield.toField
    let : CharZero ΛT := hchar
    let a : Ideal T := Ideal.span (Set.range (X : Fin m → T))
    obtain ⟨f₀, hf₀, _⟩ := (field_cohen_power_series_formally_smooth m a
      (Or.inl ⟨hfield, hchar, rfl⟩)).2 D J hJ g.toRingHom k hk
      (fun x hx ↦ hgk x ((pow_le_pow_left' hvarle k) hx))
    obtain ⟨_, _, e₀, _, he₀⟩ := exists_algEquiv_quotient_parameters_field ΛT m []
      (t.map i ++ y) (by simpa using hy)
    have hempty : Ideal.span {a : T | a ∈ ([] : List T)} = ⊥ := by simp
    let e := e₀.toRingEquiv.trans
      ((Ideal.quotientEquivAlgOfEq ΛT hempty).toRingEquiv.trans (RingEquiv.quotientBot T))
    have he (j : Fin (t.map i ++ y).length) :
        e (X j) = (t.map i ++ y).get j := by
      change RingEquiv.quotientBot T
        (Ideal.quotientEquivAlgOfEq ΛT hempty (e₀ (X j))) = _
      rw [he₀, Ideal.quotientEquivAlgOfEq_mk, RingEquiv.quotientBot_mk]
    apply adjust_coordinates t y J hJ g hg' f₀ hf₀ e he
    intro j
    change Fin (t.map i ++ y).length at j
    change e (X j) ∈ maximalIdeal T
    rw [he]
    rw [← hy.1]
    exact Ideal.subset_span (List.get_mem _ _)
  · let hdom := hcohen.2.1
    let hdvr := hcohen.2.2.1
    let := hdom
    let := hdvr
    have hpmax : (p : T) ∈ maximalIdeal T := by
      have hcoef : (p : ΛT) ∈ maximalIdeal ΛT := by
        rw [hcohen.2.2.2.1]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]
      simpa using hcoef
    let a : Ideal T := Ideal.span (insert (C (p : ΛT)) (Set.range (X : Fin m → T)))
    have hale : a ≤ maximalIdeal T := by
      apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · simpa using hpmax
      · obtain ⟨j, rfl⟩ := hx
        exact hXmax j
    obtain ⟨f₀, hf₀, _⟩ := (field_cohen_power_series_formally_smooth m a
      (Or.inr ⟨p, hcohen, rfl⟩)).2 D J hJ g.toRingHom k hk
      (fun x hx ↦ hgk x ((pow_le_pow_left' hale k) hx))
    have htcons : t = (p : R) :: t.tail := by
      cases t with
      | nil => simp at hhead
      | cons x s => simp only [List.head?_cons, Option.some.injEq] at hhead
                    simpa using hhead
    have hy' : IsRegularSystemOfParameters
        (C (p : ΛT) :: (t.tail.map i ++ y)) := by
      rw [htcons] at hy
      have hCp : C (p : ΛT) = (p : T) := map_natCast (C : ΛT →+* T) p
      simpa only [List.map_cons, List.cons_append, map_natCast, hCp] using hy
    obtain ⟨_, _, e₀, _, he₀, _⟩ := exists_algEquiv_quotient_parameters_cohen ΛT p m
      hcohen [] (t.tail.map i ++ y) (by simpa using hy')
    have hempty : Ideal.span {a : T | a ∈ ([] : List T)} = ⊥ := by simp
    let e := e₀.toRingEquiv.trans
      ((Ideal.quotientEquivAlgOfEq ΛT hempty).toRingEquiv.trans (RingEquiv.quotientBot T))
    have he (j : Fin (t.tail.map i ++ y).length) :
        e (X j) = (t.tail.map i ++ y).get j := by
      change RingEquiv.quotientBot T
        (Ideal.quotientEquivAlgOfEq ΛT hempty (e₀ (X j))) = _
      rw [he₀, Ideal.quotientEquivAlgOfEq_mk, RingEquiv.quotientBot_mk]
    have hemax (j : Fin (t.tail.map i ++ y).length) : e (X j) ∈ maximalIdeal T := by
      rw [he]
      rw [← hy'.1]
      exact Ideal.subset_span (List.mem_cons_of_mem _ (List.get_mem _ _))
    obtain ⟨f, hf, hft⟩ := adjust_coordinates t.tail y J hJ g hg' f₀ hf₀ e he hemax
    refine ⟨f, hf, ?_⟩
    intro r hr
    rw [htcons] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [map_natCast]
    · exact hft r hr

end MvPowerSeries
