/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.AnnihilatorElementFlatBaseChange
import Mathlib.RingTheory.Nakayama

/-! # Local elimination of the desingularization relations

Source: Stacks Project, Smoothing Ring Maps, final local argument in Tag 07CR.
-/

@[expose] public section

universe u v

namespace Algebra

private theorem annihilator_sq_of_flat_unit
    {R : Type u} {T : Type v} [CommRing R] [CommRing T]
    (φ : R →+* T) (hflat : φ.Flat) (π r : R) (hu : IsUnit (φ r))
    (hr : ∀ x : R, π ^ 2 * x = 0 → r * π * x = 0)
    (z : T) (hz : φ π ^ 2 * z = 0) : φ π * z = 0 := by
  have hz' : z ∈ Module.annihilator T (Ideal.span {φ (π ^ 2)}) := by
    change z ∈ (Submodule.span T ({φ (π ^ 2)} : Set T)).annihilator
    rw [Submodule.mem_annihilator_span_singleton]
    simpa [smul_eq_mul, mul_comm] using hz
  rw [RingHom.annihilator_element_flat_base_change φ hflat] at hz'
  change z ∈ Ideal.span (φ '' (Module.annihilator R (Ideal.span {π ^ 2}) : Set R)) at hz'
  have hkill : φ r * φ π * z = 0 := by
    clear hz
    induction hz' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      have hx' : π ^ 2 * x = 0 := by
        change x ∈ (Submodule.span R ({π ^ 2} : Set R)).annihilator at hx
        rw [Submodule.mem_annihilator_span_singleton] at hx
        simpa [smul_eq_mul, mul_comm] using hx
      simpa only [map_mul, map_zero] using congrArg φ (hr x hx')
    | zero => simp
    | add x y hx hy ihx ihy => simp [mul_add, ihx, ihy]
    | smul a x hx ih =>
      change φ r * φ π * (a * x) = 0
      calc
        φ r * φ π * (a * x) = a * (φ r * φ π * x) := by ring
        _ = 0 := by rw [ih, mul_zero]
  exact (hu.mul_left_eq_zero).mp (by simpa [mul_comm, mul_left_comm, mul_assoc] using hkill)

private theorem quadratic_ideal_eq_bot
    {R : Type u} {T : Type v} [CommRing R] [CommRing T]
    [IsNoetherianRing T] [IsLocalRing T]
    (φ : R →+* T) (hflat : φ.Flat) (π r : R) (hu : IsUnit (φ r))
    (hr : ∀ x : R, π ^ 2 * x = 0 → r * π * x = 0)
    (ht : φ π ∈ IsLocalRing.maximalIdeal T) (J : Ideal T)
    (hdiv : J ≤ Ideal.span {φ π ^ 2})
    (hquad : Ideal.span {φ π} * J ≤ J ^ 2) : J = ⊥ := by
  let P : Ideal T := Ideal.span {φ π}
  let N : Ideal T := P * J
  have hN : N ≤ P * N := by
    calc
      N ≤ J * J := by simpa [N, P, pow_two] using hquad
      _ ≤ Ideal.span {φ π ^ 2} * J := Ideal.mul_mono_left hdiv
      _ = P * N := by rw [← Ideal.span_singleton_pow, pow_two, mul_assoc]
  have hP : P ≤ Ideal.jacobson ⊥ :=
    (Ideal.span_singleton_le_iff_mem _).mpr
      (IsLocalRing.maximalIdeal_le_jacobson ⊥ ht)
  have hzero : N = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot P N N.fg_of_isNoetherianRing
    · simpa only [Ideal.smul_eq_mul] using hN
    · exact hP
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (hdiv hx)
  have htx : φ π * x = 0 := by
    have hmem : φ π * x ∈ N :=
      Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton _)) hx
    rw [hzero] at hmem
    exact hmem
  have ht3 : φ π ^ 2 * (φ π * z) = 0 := by
    calc
      φ π ^ 2 * (φ π * z) = φ π * (z * φ π ^ 2) := by ring
      _ = 0 := by rw [hz, htx]
  have ht2 := annihilator_sq_of_flat_unit φ hflat π r hu hr (φ π * z) ht3
  have ht2' : φ π ^ 2 * z = 0 := by simpa [pow_two, mul_assoc] using ht2
  change x = 0
  rw [← hz, mul_comm]
  exact ht2'

private theorem exists_outside_annihilating_ideal
    {S : Type v} [CommRing S] (p : Ideal S) [p.IsPrime]
    (K : Ideal S) (hK : K.FG)
    (hzero : ∀ x ∈ K, algebraMap S (Localization.AtPrime p) x = 0) :
    ∃ s : S, s ∉ p ∧ ∀ x ∈ K, s * x = 0 := by
  classical
  obtain ⟨t, ht⟩ := hK
  have hfin : ∃ s : S, s ∉ p ∧ ∀ x ∈ t, s * x = 0 := by
    have hz : ∀ x ∈ t, ∃ s : S, s ∉ p ∧ s * x = 0 := by
      intro x hx
      have hxK : x ∈ K := ht ▸ Submodule.subset_span hx
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl
        (Localization.AtPrime p) x).mp (hzero x hxK)
      exact ⟨s, s.property, hs⟩
    clear ht hzero
    induction t using Finset.induction_on with
    | empty => exact ⟨1, Ideal.IsPrime.one_notMem (inferInstance : p.IsPrime), by simp⟩
    | @insert a t ha ih =>
      obtain ⟨s, hs, hsa⟩ := hz a (Finset.mem_insert_self a t)
      obtain ⟨d, hd, hdt⟩ := ih (fun x hx ↦ hz x (Finset.mem_insert_of_mem hx))
      refine ⟨s * d, p.primeCompl.mul_mem hs hd, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · calc
          s * d * x = d * (s * x) := by ring
          _ = 0 := by rw [hsa, mul_zero]
      · rw [mul_assoc, hdt x hx, mul_zero]
  obtain ⟨s, hs, hst⟩ := hfin
  refine ⟨s, hs, ?_⟩
  intro x hx
  rw [← ht] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hst y hy
  | zero => simp
  | add x y hx hy ihx ihy => simp [mul_add, ihx, ihy]
  | smul a x hx ih =>
    change s * (a * x) = 0
    rw [mul_left_comm, ih, mul_zero]

/-- A quadratic relation ideal divisible by `π²` vanishes locally where the annihilator
obstruction is invertible; a smooth neighbourhood therefore descends to the quotient.

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR, final local argument
(blueprint: lem-weil-pbc-quadratic-relations-smooth-quotient).

Proof: put `q' = q ∩ S` and `T = S_{q'}`. Let `J = KT` and let `t` be the image of `π`.
Then `J ≤ (t²)` and `(t)J ≤ J² ≤ (t²)J`. The finitely generated ideal `N = (t)J`
satisfies `N ≤ (t)N`. Since `t` is in the maximal ideal of the Noetherian local ring `T`,
Nakayama (or Krull intersection) gives `N=0`. Flat base change identifies `Ann_T(t²)`
and `Ann_T(t)` with the extensions of the corresponding annihilators in `R`. The
hypothesis on `r` says that `r Ann_R(π²) ≤ Ann_R(π)`. Its image is invertible in `T`,
so `Ann_T(t²) = Ann_T(t)`. Induction gives `Ann_T(t³) = Ann_T(t)`. Each element of
`J` is `t²z` and is killed by `t`, whence `t³z=0`, then `tz=0`, then `t²z=0`.
Thus `J=0`. As `K` is finitely generated, clear finitely many denominators to obtain
`s ∉ q'` annihilating `K`. Multiply `s` by an element `g ∉ q'` whose principal
localization of `S` is smooth. The localization at `sg` is still smooth by localization
and composition; its quotient by `K` is identical since `K` vanishes there. The image
of `sg` is outside `q` and exhibits the required smoothness of `S/K`. -/
theorem smoothAtPrime_quotient_of_quadratic_relations
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] (π : R) (K : Ideal S)
    (hdiv : K ≤ Ideal.span {(algebraMap R S π) ^ 2})
    (hquad : Ideal.span {algebraMap R S π} * K ≤ K ^ 2)
    (q : PrimeSpectrum (S ⧸ K))
    (hπ : algebraMap R (S ⧸ K) π ∈ q.asIdeal)
    (hsmooth : IsSmoothAtPrime R (PrimeSpectrum.comap (Ideal.Quotient.mk K) q))
    (hflat : Module.Flat R
      (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk K) q).asIdeal))
    (r : R) (hr : ∀ x : R, π ^ 2 * x = 0 → r * π * x = 0)
    (hrq : algebraMap R (S ⧸ K) r ∉ q.asIdeal) :
    IsSmoothAtPrime R q := by
  let p := (PrimeSpectrum.comap (Ideal.Quotient.mk K) q).asIdeal
  let T := Localization.AtPrime p
  let f := algebraMap S T
  let φ := algebraMap R T
  have hflat' : φ.Flat := RingHom.flat_algebraMap_iff.mpr hflat
  have hdiv' : K.map f ≤ Ideal.span {φ π ^ 2} := by
    have h := Ideal.map_mono (f := f) hdiv
    dsimp only [f] at h
    simpa only [Ideal.map_span, Set.image_singleton, map_pow,
      φ, ← IsScalarTower.algebraMap_apply R S T] using h
  have hquad' : Ideal.span {φ π} * K.map f ≤ K.map f ^ 2 := by
    have h := Ideal.map_mono (f := f) hquad
    rw [Ideal.map_mul f, Ideal.map_pow f, Ideal.map_span, Set.image_singleton] at h
    simpa only [f, φ, ← IsScalarTower.algebraMap_apply R S T] using h
  have hu : IsUnit (φ r) := by
    change IsUnit (f (algebraMap R S r))
    exact IsLocalization.map_units T (⟨algebraMap R S r, hrq⟩ : p.primeCompl)
  have ht : φ π ∈ IsLocalRing.maximalIdeal T := by
    change f (algebraMap R S π) ∈ IsLocalRing.maximalIdeal T
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff T p _).mpr hπ
  have hJ := quadratic_ideal_eq_bot φ hflat' π r hu hr ht (K.map f) hdiv' hquad'
  obtain ⟨s, hs, hkill⟩ := exists_outside_annihilating_ideal p K
    K.fg_of_isNoetherianRing (fun x hx ↦ by
      have hm := Ideal.mem_map_of_mem f hx
      rw [hJ] at hm
      exact hm)
  obtain ⟨g, hg, hsm⟩ := hsmooth
  let e := s * g
  let C := Localization.Away e
  let fB := Ideal.Quotient.mkₐ R K
  let D := Localization.Away (fB e)
  let E := Localization.Away (algebraMap S (Localization.Away g) s)
  have : Smooth R (Localization.Away g) := hsm
  have : Smooth (Localization.Away g) E :=
    Smooth.of_isLocalization_Away (algebraMap S (Localization.Away g) s)
  have : Smooth R E := Smooth.comp R (Localization.Away g) E
  have : IsLocalization.Away e E :=
    IsLocalization.Away.mul (Localization.Away g) E g s
  have : Smooth R C := Smooth.of_equiv
    ((IsLocalization.algEquiv (.powers e) E C).restrictScalars R)
  let F : C →ₐ[R] D := IsLocalization.Away.mapₐ C D fB e
  have hFi : Function.Injective F := by
    apply (IsLocalization.Away.map_injective_iff (S := C) D fB.toRingHom e).mpr
    intro x hx
    refine ⟨1, ?_⟩
    have hxK : x ∈ K := Ideal.Quotient.eq_zero_iff_mem.mp hx
    simpa only [pow_one, e, mul_right_comm, zero_mul] using
      congrArg (fun y : S ↦ y * g) (hkill x hxK)
  have hFs : Function.Surjective F :=
    IsLocalization.Away.mapₐ_surjective_of_surjective
      (Aₚ := C) (Bₚ := D) (f := fB) e Ideal.Quotient.mk_surjective
  have hD : Smooth R D := Smooth.of_equiv (AlgEquiv.ofBijective F ⟨hFi, hFs⟩)
  exact ⟨fB e, p.primeCompl.mul_mem hs hg, hD⟩

end Algebra
