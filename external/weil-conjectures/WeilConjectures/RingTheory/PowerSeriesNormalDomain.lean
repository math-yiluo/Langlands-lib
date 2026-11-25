/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral

/-!
# Power series over a Noetherian normal domain

Source: Stacks Project, Algebra, Lemma 10.37.9 (Tag 0BI0)
(blueprint: lem-weil-pbc-power-series-normal-domain).

The one-variable ring is Mathlib's `PowerSeries R`, the one-variable case of the
recorded power series notion.
Normality for a domain is `IsIntegrallyClosed`, integrality in its fraction field.
-/

@[expose] public section

universe u

namespace PowerSeries

/-- The first potentially nonzero coefficient of an almost integral power series is
almost integral. Source: Stacks 0BI0, the lowest-term calculation. -/
private theorem coeff_almostIntegral (R K : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : PowerSeries K) (hf : IsAlmostIntegral (PowerSeries R) f)
    (n : ℕ) (hn : ∀ i < n, coeff i f = 0) : IsAlmostIntegral R (coeff n f) := by
  classical
  obtain ⟨h, hh, hhf⟩ := hf
  have hh0 : h ≠ 0 := by simpa using hh
  obtain ⟨g, hg⟩ := X_pow_dvd_iff.mpr hn
  let m := h.order.toNat
  have hfactor : h = X ^ m * h.divXPowOrder := X_pow_order_mul_divXPowOrder.symm
  have hg0 : constantCoeff g = coeff n f := by
    simp [hg, coeff_X_pow_mul', coeff_zero_eq_constantCoeff]
  refine ⟨coeff m h, ?_, fun e ↦ ?_⟩
  · simpa using coeff_order hh0
  · obtain ⟨a, ha⟩ := hhf e
    refine ⟨coeff (m + n * e) a, ?_⟩
    have heq := congrArg (coeff (m + n * e)) ha
    change (map (algebraMap R K) a) = _ at ha
    have hprod : map (algebraMap R K) h * f ^ e =
        X ^ (m + n * e) * (map (algebraMap R K) h.divXPowOrder * g ^ e) := by
      conv_lhs => rw [hfactor, map_mul, map_pow, map_X, hg, mul_pow, ← pow_mul]
      rw [pow_add]
      ring
    have heq' : algebraMap R K (coeff (m + n * e) a) =
        algebraMap R K (coeff m h) * coeff n f ^ e := by
      calc
        _ = coeff (m + n * e) (map (algebraMap R K) h * f ^ e) := by
          simpa only [coeff_map, Algebra.smul_def, algebraMap_apply''] using heq
        _ = _ := by
          rw [hprod]
          simp only [coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
            coeff_zero_eq_constantCoeff, map_mul, map_pow]
          rw [← coeff_zero_eq_constantCoeff, coeff_map]
          simp only [coeff_zero_eq_constantCoeff, constantCoeff_divXPowOrder, hg0]
          rfl
    simpa only [Algebra.smul_def] using heq'

/-- Subtract the polynomial of previously descended coefficients, then apply the
lowest-term calculation. Source: Stacks 0BI0, the induction on coefficients. -/
private theorem coeff_mem_range (R K : Type u) [CommRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (f : PowerSeries K) (hf : IsAlmostIntegral (PowerSeries R) f) (n : ℕ) :
    ∃ r : R, algebraMap R K r = coeff n f := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hprev : ∀ i : Fin n, ∃ r : R, algebraMap R K r = coeff i f :=
      fun i ↦ ih i i.isLt
    choose r hr using hprev
    let p : PowerSeries R := ∑ i : Fin n, monomial i (r i)
    let g : PowerSeries K := f - map (algebraMap R K) p
    have hp (i : ℕ) : coeff i p = ∑ j : Fin n, if i = j then r j else 0 := by
      simp [p, coeff_monomial]
    have hg (i : ℕ) : coeff i g = coeff i f - algebraMap R K (coeff i p) := by
      simp [g, coeff_map]
    have hgn : ∀ i < n, coeff i g = 0 := by
      intro i hi
      rw [hg, hp]
      have hsum : (∑ j : Fin n, if i = j then r j else 0) = r ⟨i, hi⟩ := by
        rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
        · simp
        · intro j _ hj
          simp only [ite_eq_right_iff]
          intro he
          exact (hj (Fin.ext he.symm)).elim
        · simp
      rw [hsum, hr, sub_self]
    have hgncoeff : coeff n g = coeff n f := by
      rw [hg, hp]
      have hsum : (∑ j : Fin n, if n = j then r j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact ite_eq_right (ne_of_gt j.isLt)
      rw [hsum, map_zero, sub_zero]
    have hgalmost : IsAlmostIntegral (PowerSeries R) g :=
      (completeIntegralClosure (PowerSeries R) (PowerSeries K)).sub_mem hf
        ((completeIntegralClosure (PowerSeries R) (PowerSeries K)).algebraMap_mem p)
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (coeff_almostIntegral R K g hgalmost n hgn).isIntegral
    exact ⟨a, ha.trans hgncoeff⟩

/-- A one-variable power series ring over a Noetherian normal domain is a Noetherian normal
 domain. Source: Stacks Project, Algebra, Lemma 10.37.9 (Tag 0BI0)
(blueprint: lem-weil-pbc-power-series-normal-domain).

Proof following Stacks 0BI0, with the negative-order argument replaced by Mathlib's
normality of power series over a field:

1. Mathlib supplies Noetherianity and the domain property.
2. Put `K = Frac(R)` and embed `Frac(R[[x]])` into `K((x))` by the fraction-field lift of
coefficientwise inclusion followed by `HahnSeries.ofPowerSeries`.
3. An integral element maps to an element integral over `K[[x]]`. Power series over a field
are a unique factorization domain, hence integrally closed, and `K((x))` is their fraction
field. Thus the Laurent image is a power series `f` over `K`.
4. Transport the almost-integrality witness of the original fraction to `f`. If coefficients
below `n` vanish, factor `f = X^n * g`. For a nonzero witness `h`, put `m = order(h)` and
factor `h = X^m * h.divXPowOrder`. The coefficient of `h*f^e` at `m+n*e` is
`coeff m h * (coeff n f)^e`. It belongs to `R` for every `e`, so `coeff n f` is almost
integral over `R`. Noetherianity and normality put this coefficient in `R`.
5. Induct on `n`, subtracting the finite polynomial of already descended coefficients.
Almost integral elements form a subalgebra, so the difference remains almost integral.
Apply step 4 to obtain its coefficient at `n`, which equals that of `f`.
6. Choose coefficient preimages from these proved membership statements and form the power
series over `R` using `PowerSeries.mk`. Its Laurent image equals the image of the original
fraction. Injectivity of the fraction-field lift finishes the proof. -/
theorem noetherian_normal_domain (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R] :
    IsNoetherianRing (PowerSeries R) ∧
      IsDomain (PowerSeries R) ∧ IsIntegrallyClosed (PowerSeries R) := by
  classical
  refine ⟨inferInstance, inferInstance, ?_⟩
  let K := FractionRing R
  let A := PowerSeries R
  let F := FractionRing A
  let c : A →+* PowerSeries K := map (algebraMap R K)
  let i : A →+* LaurentSeries K := (HahnSeries.ofPowerSeries ℤ K).comp c
  have hc : Function.Injective c := map_injective _ (IsFractionRing.injective R K)
  have hi : Function.Injective i := (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)).comp hc
  let j : F →+* LaurentSeries K := IsFractionRing.lift (K := F) hi
  have hj (a : A) : j (algebraMap A F a) = i a :=
    IsFractionRing.lift_algebraMap (K := F) hi a
  refine (isIntegrallyClosed_iff F).mpr fun {w} hw ↦ ?_
  have hwK : IsIntegral (PowerSeries K) (j w) :=
    hw.map_of_comp_eq c j (by apply RingHom.ext; intro a; exact (hj a).symm)
  obtain ⟨f, hf⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hwK
  have hfalmost : IsAlmostIntegral A f := by
    obtain ⟨h, hh, hhw⟩ := hw.isAlmostIntegral
    refine ⟨h, hh, fun e ↦ ?_⟩
    obtain ⟨a, ha⟩ := hhw e
    refine ⟨a, ?_⟩
    rw [Algebra.smul_def]
    change map (algebraMap R K) a = map (algebraMap R K) h * f ^ e
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    have he := congrArg j ha
    simp only [Algebra.smul_def, map_mul, map_pow] at he
    change j (algebraMap A F a) = j (algebraMap A F h) * j w ^ e at he
    rw [hj, hj, ← hf] at he
    simpa only [Algebra.smul_def, map_mul, map_pow,
      i, RingHom.comp_apply, c, algebraMap_apply'', LaurentSeries.coe_algebraMap] using he
  have hcoeff := coeff_mem_range R K f hfalmost
  choose r hr using hcoeff
  let g : A := mk r
  have hg : c g = f := by
    ext n
    exact (coeff_map (algebraMap R K) n g).trans
      ((congrArg (algebraMap R K) (coeff_mk n r)).trans (hr n))
  refine ⟨g, j.injective ?_⟩
  rw [hj]
  change HahnSeries.ofPowerSeries ℤ K (c g) = j w
  rw [hg]
  exact hf

end PowerSeries

