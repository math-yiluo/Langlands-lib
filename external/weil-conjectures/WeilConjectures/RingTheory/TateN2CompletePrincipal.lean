/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import WeilConjectures.RingTheory.TatePurelyInseparableClosureQuotientFinite
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import WeilConjectures.RingTheory.N2CharPPurelyInseparableCriterion

/-!
# Tate's criterion for an N-2 complete principal domain

Source: Stacks Project, Algebra, Lemma Tag 032P (lemma-tate-japanese),
lines 45534--45589 (blueprint: lem-weil-pbc-tate-n2-complete-principal).
-/

@[expose] public section

universe u v

set_option autoImplicit false

/-- An integral element in every x^n S has a p-power in every x^n R.
Normality puts those powers in R; separatedness of R and the domain property
then force the element to vanish. This is step 11 of Stacks Tag 032P. -/
private theorem closure_hausdorff (R : Type u) (K L : Type v)
    [CommRing R] [IsDomain R] [Field K] [Field L] [Algebra R K]
    [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (x : R) [IsIntegrallyClosed R]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsPurelyInseparable K L]
    [IsHausdorff (Ideal.span ({x} : Set R)) R] :
    IsHausdorff (Ideal.span ({x} : Set R)) (integralClosure R L) := by
  let I : Ideal R := Ideal.span ({x} : Set R)
  have hmem (n : ℕ) (s : integralClosure R L) :
      s ∈ (I ^ n • ⊤ : Submodule R (integralClosure R L)) ↔
        ∃ t : integralClosure R L, x ^ n • t = s := by
    rw [show I ^ n = Ideal.span ({x ^ n} : Set R) from Ideal.span_singleton_pow x n,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp
  constructor
  intro s hs
  have hs' (n : ℕ) : ∃ t : integralClosure R L, x ^ n • t = s :=
    (hmem n s).mp (by simpa only [SModEq.sub_mem, sub_zero] using hs n)
  by_cases hx : x = 0
  · obtain ⟨t, ht⟩ := hs' 1
    simpa [hx] using ht.symm
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hxL : algebraMap R L x ≠ 0 := fun h ↦ hx (hRL (h.trans (map_zero _).symm))
  obtain ⟨e, k, hk⟩ := IsPurelyInseparable.pow_mem K p (s : L)
  let q := p ^ e
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos e
  have hik : IsIntegral R k :=
    (isIntegral_algebraMap_iff (R := R) (A := K) (B := L)).mp (hk ▸ s.property.pow q)
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hik
  have hrL : algebraMap R L r = (s : L) ^ q := by
    rw [IsScalarTower.algebraMap_apply R K L, hr, hk]
  have hrzero : r = 0 := IsHausdorff.haus (inferInstance : IsHausdorff I R) r fun n ↦ by
    obtain ⟨t, ht⟩ := hs' n
    have htL : (algebraMap R L x) ^ n * (t : L) = (s : L) := by
      simpa [Algebra.smul_def] using congrArg (fun z : integralClosure R L ↦ (z : L)) ht
    let a : K := k / (algebraMap R K x) ^ (n * q)
    have ha : algebraMap K L a = (t : L) ^ q := by
      dsimp [a]
      rw [map_div₀, map_pow, ← IsScalarTower.algebraMap_apply R K L]
      symm
      apply (eq_div_iff (pow_ne_zero (n * q) hxL)).mpr
      rw [hk, ← htL, mul_pow, pow_mul]
      exact mul_comm _ _
    have hia : IsIntegral R a :=
      (isIntegral_algebraMap_iff (R := R) (A := K) (B := L)).mp (ha ▸ t.property.pow q)
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hia
    have hbeq : x ^ (n * q) * b = r := by
      apply hRL
      simp only [map_mul, map_pow, IsScalarTower.algebraMap_apply R K L, hb, ha, hr, hk]
      rw [← htL, mul_pow, pow_mul]
      rw [← IsScalarTower.algebraMap_apply R K L]
    have hrmem : r ∈ I ^ (n * q) := by
      rw [show I ^ (n * q) = Ideal.span ({x ^ (n * q)} : Set R) from
        Ideal.span_singleton_pow x (n * q), Ideal.mem_span_singleton]
      exact ⟨b, by simpa [mul_comm] using hbeq.symm⟩
    have : r ∈ I ^ n := Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right n hq) hrmem
    apply SModEq.sub_mem.mpr
    rw [sub_zero]
    simpa only [smul_eq_mul, mul_one] using
      (Submodule.smul_mem_smul this (Submodule.mem_top : (1 : R) ∈ ⊤) :
        r • (1 : R) ∈ (I ^ n • ⊤ : Submodule R R))
  apply Subtype.ext
  have : (s : L) ^ q = 0 := by rw [← hrL, hrzero, map_zero]
  exact (pow_eq_zero_iff hq.ne').mp this

/-- A Noetherian normal domain complete along a principal ideal whose quotient is N-2
is itself N-2. Source: Stacks Project, Algebra, Lemma Tag 032P (lemma-tate-japanese).
(blueprint: lem-weil-pbc-tate-n2-complete-principal).

Proof: split by the characteristic of K. In characteristic zero every finite
extension is separable, so Mathlib's `IsIntegralClosure.finite` applies directly.
In characteristic p use `isN2_of_finite_purelyInseparable_integralClosure` to
reduce to a finite purely inseparable extension L/K. Its integral closure S
is x-adically Hausdorff by the Frobenius-power argument `closure_hausdorff`.
The closed-fibre lemma gives finiteness of S/xS over R/xR. Apply
`Module.finite_and_span_eq_top_of_adicComplete` to the complete base R and S.
This proves finiteness of the integral closure for the criterion. -/
theorem tate_n2_complete_principal (R : Type u) (K : Type v) [CommRing R]
    [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [IsNoetherianRing R] (x : R) (hnormal : IsIntegrallyClosed R)
    [IsAdicComplete (Ideal.span ({x} : Set R)) R]
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    (hquot : IsN2 (R ⧸ Ideal.span ({x} : Set R))
      (FractionRing (R ⧸ Ideal.span ({x} : Set R)))) :
    IsN2 R K := by
  have : IsIntegrallyClosed R := hnormal
  let : CharP K (ringChar K) := inferInstance
  by_cases hzero : ringChar K = 0
  · let : CharP K 0 := hzero ▸ inferInstance
    let : CharZero K := CharP.charP_to_charZero K
    intro L _ _ _ _ _
    exact IsIntegralClosure.finite R K L (integralClosure R L)
  · have hp : Nat.Prime (ringChar K) :=
      (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hzero
    let : Fact (Nat.Prime (ringChar K)) := ⟨hp⟩
    apply isN2_of_finite_purelyInseparable_integralClosure R K (ringChar K)
    intro L _ _ _ _ _ _
    have : IsHausdorff (Ideal.span ({x} : Set R)) (integralClosure R L) :=
      closure_hausdorff R K L x (ringChar K)
    have : Module.Finite (R ⧸ Ideal.span ({x} : Set R))
        ((integralClosure R L) ⧸
          (Ideal.span ({x} : Set R) • ⊤ : Submodule R (integralClosure R L))) :=
      tate_purely_inseparable_closure_quotient_finite R K L x hnormal (ringChar K) hquot
    exact (Module.finite_and_span_eq_top_of_adicComplete
      (Ideal.span ({x} : Set R)) (integralClosure R L)).1
