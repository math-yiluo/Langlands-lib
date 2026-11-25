/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.PointCountFiber
public import WeilConjectures.WeilSheaf.TraceFunction
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.LocalPolynomial

/-!
# The `L`-series of a Weil sheaf

The `L`-series of a Weil sheaf `F` on a `k₀`-scheme `X₀` of finite type is the Euler product

`L(X₀, F, t) = ∏_{x ∈ |X₀|} det(1 - Fₓ t^{d(x)} | F_x̄)⁻¹ ∈ ℂ⟦t⟧`,

transported to `ℂ` along `ι`, converging in the product topology. Its logarithmic derivative is
the generating series of the sums of the trace function over the rational points:

`t L'(t) / L(t) = ∑_{n ≥ 1} (∑_{y ∈ X₀(𝔽_{qⁿ})} ι t_{F,n}(y)) tⁿ`.

This is the point-counting regrouping of the Euler product: by the determinant-trace identity
(`LinearMap.X_mul_derivative_charpolyRev`) the logarithmic derivative of the local factor at `x`
is `∑_{m ≥ 1} d(x) ι tr(Fₓᵐ) t^{d(x) m}`, and the `𝔽_{qⁿ}`-rational points over a closed point
`x` with `d(x) ∣ n` are `d(x)` in number, each with trace `tr(Fₓ^{n / d(x)})`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.lFactor`: the local factor `ι det(1 - Fₓ t^{d(x)})⁻¹`.
- `AlgebraicGeometry.WeilSheaf.lSeries`: the `L`-series.
- `AlgebraicGeometry.WeilSheaf.sum_traceFunction_eq_sum`: the regrouping of the rational
  points over the closed points.
- `AlgebraicGeometry.WeilSheaf.X_mul_derivative_lSeries`: the logarithmic derivative of the
  `L`-series.
-/

@[expose] public section

universe u

open CategoryTheory PowerSeries

open scoped PowerSeries.WithPiTopology

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The local factor `ι det(1 - Fₓ t^{d(x)} | F_x̄)⁻¹ ∈ ℂ⟦t⟧` of the `L`-series of a Weil sheaf
at a closed point `x` of degree `d(x)`. -/
noncomputable def lFactor (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    (x : X.finitePoints) : PowerSeries ℂ :=
  ((((F.stalk x).localPolynomial.map ι).comp
    (Polynomial.X ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial ℂ) :
      PowerSeries ℂ)⁻¹

/-- The `L`-series `L(X₀, F, t) = ∏_{x ∈ |X₀|} det(1 - Fₓ t^{d(x)} | F_x̄)⁻¹ ∈ ℂ⟦t⟧` of a Weil
sheaf, the product over the closed points of `X₀` of the inverses of the local polynomials
`FrobeniusModule.localPolynomial` of the stalks, transported to `ℂ` along `ι` and substituted
into `t^{d(x)}` for the degree `d(x) = [κ(x) : k₀]`. It is taken in the product topology on
`ℂ⟦t⟧`, in which it converges for `X₀` of finite type over `k₀`
(`AlgebraicGeometry.WeilSheaf.multipliable_lFactor`). -/
noncomputable def lSeries (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : PowerSeries ℂ :=
  ∏' x : X.finitePoints, ((((F.stalk x).localPolynomial.map ι).comp
    (Polynomial.X ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial ℂ) :
      PowerSeries ℂ)⁻¹

theorem lSeries_eq_tprod (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    F.lSeries ι = ∏' x, F.lFactor ι x :=
  rfl

/-- The coercion of `P(X ^ d)` is the expansion of the coercion of `P`. -/
theorem _root_.Polynomial.coe_comp_X_pow {R : Type*} [CommRing R] (P : Polynomial R) {d : ℕ}
    (hd : d ≠ 0) :
    ((P.comp (Polynomial.X ^ d) : Polynomial R) : R⟦X⟧) = expand d hd (P : R⟦X⟧) := by
  ext n
  rw [Polynomial.coeff_coe, ← Polynomial.expand_eq_comp_X_pow,
    Polynomial.coeff_expand (Nat.pos_of_ne_zero hd), coeff_expand]
  split_ifs <;> simp [Polynomial.coeff_coe]

/-- The power series of the image under `ι` of the local polynomial `det(1 - T Fₓ)`. -/
noncomputable abbrev locPoly (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    (x : X.finitePoints) : ℂ⟦X⟧ :=
  (((F.stalk x).localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧)

/-- The generating series `∑_{m ≥ 1} ι tr(Fₓᵐ) Tᵐ` of the traces of the local Frobenius. -/
noncomputable abbrev traceGen (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    (x : X.finitePoints) : ℂ⟦X⟧ :=
  PowerSeries.map ι (PowerSeries.mk fun n ↦ if n = 0 then 0 else
    LinearMap.trace (PadicAlgCl l) _ ((F.stalk x).frobeniusEnd ^ n))

/-- The logarithmic derivative of the local factor at `x`:
`d(x) ∑_{m ≥ 1} ι tr(Fₓᵐ) t^{d(x) m}`. -/
noncomputable def lFactorLogDeriv (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    (x : X.finitePoints) : ℂ⟦X⟧ :=
  C ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 : ℂ) *
    expand _ ((X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2) (traceGen ι F x)

private lemma constantCoeff_locPoly (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    (x : X.finitePoints) : constantCoeff (locPoly ι F x) = 1 := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_map,
    FrobeniusModule.coeff_zero_localPolynomial, map_one]

private lemma lFactor_eq (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (x : X.finitePoints) :
    F.lFactor ι x =
      (expand _ ((X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2) (locPoly ι F x))⁻¹ := by
  rw [lFactor, Polynomial.coe_comp_X_pow]

/-- The constant coefficient of a local factor is `1`. -/
theorem constantCoeff_lFactor (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    (x : X.finitePoints) : constantCoeff (F.lFactor ι x) = 1 := by
  rw [lFactor_eq, constantCoeff_inv, constantCoeff_expand, constantCoeff_locPoly, inv_one]

/-- The logarithmic derivative of a local factor: `t lₓ' = (d(x) ∑_{m ≥ 1} ι tr(Fₓᵐ) t^{d(x) m})
lₓ`, by the determinant-trace identity `LinearMap.X_mul_derivative_charpolyRev`. -/
theorem X_mul_derivative_lFactor (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    (x : X.finitePoints) :
    PowerSeries.X * derivative (R := ℂ) (F.lFactor ι x) =
      F.lFactorLogDeriv ι x * F.lFactor ι x := by
  set d := (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
  have hd : d ≠ 0 := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  set P := locPoly ι F x
  set Q := expand d hd P
  have hP : constantCoeff P = 1 := constantCoeff_locPoly ι F x
  have hQ : constantCoeff Q = 1 := by rw [constantCoeff_expand, hP]
  have hPP : P * P⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hP]; exact one_ne_zero)
  have hQQ : Q * Q⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hQ]; exact one_ne_zero)
  -- the determinant-trace identity for the stalk
  have hT : traceGen ι F x = -(PowerSeries.X * derivative (R := ℂ) P) * P⁻¹ :=
    LinearMap.map_mk_trace_pow (F.stalk x).frobeniusEnd ι
  have hP' : PowerSeries.X * derivative (R := ℂ) P = -traceGen ι F x * P := by
    rw [hT]
    linear_combination (-(PowerSeries.X * derivative (R := ℂ) P)) * hPP
  have hQ' : PowerSeries.X * derivative (R := ℂ) Q = -F.lFactorLogDeriv ι x * Q := by
    rw [X_mul_derivative_expand, hP', map_mul, map_neg, lFactorLogDeriv]
    ring
  rw [lFactor_eq, derivative_inv']
  linear_combination (-Q⁻¹ ^ 2) * hQ' + F.lFactorLogDeriv ι x * Q⁻¹ * hQQ

/-- A series with constant coefficient `0`, expanded by `d`, is divisible by `X ^ d`. -/
private lemma X_pow_dvd_expand {f : ℂ⟦X⟧} (hf : constantCoeff f = 0) {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.X ^ d ∣ expand d hd f := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  exact ⟨expand d hd g, by rw [map_mul, expand_X]⟩

/-- A local factor at a point of degree `d(x) > n` is congruent to `1` modulo `X ^ (n + 1)`. -/
theorem X_pow_dvd_lFactor_sub_one (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    {x : X.finitePoints} {n : ℕ} (hx : n < (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) :
    PowerSeries.X ^ (n + 1) ∣ F.lFactor ι x - 1 := by
  have hd := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  have h : PowerSeries.X ^ (n + 1) ∣ expand _ hd (locPoly ι F x) - 1 := by
    refine (pow_dvd_pow _ hx).trans ?_
    have h0 : constantCoeff (locPoly ι F x - 1) = 0 := by
      rw [map_sub, constantCoeff_locPoly, map_one, sub_self]
    simpa [map_sub] using X_pow_dvd_expand h0 hd
  have h1 : constantCoeff (expand _ hd (locPoly ι F x)) ≠ 0 := by
    rw [constantCoeff_expand, constantCoeff_locPoly]
    exact one_ne_zero
  have h' := X_pow_dvd_inv_sub_inv h1 (by simp) h
  rwa [inv_one, ← lFactor_eq] at h'

/-- The logarithmic derivative of a local factor at a point of degree `d(x) > n` is divisible by
`X ^ (n + 1)`. -/
theorem X_pow_dvd_lFactorLogDeriv (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    {x : X.finitePoints} {n : ℕ} (hx : n < (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) :
    PowerSeries.X ^ (n + 1) ∣ F.lFactorLogDeriv ι x :=
  ((pow_dvd_pow _ hx).trans (X_pow_dvd_expand (by
    rw [traceGen, <- coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_mk, ite_eq_left rfl,
      map_zero]) _)).mul_left _

/-- The coefficients of the logarithmic derivative of a local factor:
`d(x) ι tr(Fₓ^{n / d(x)})` in degrees `n ≥ 1` divisible by `d(x)`, and `0` otherwise. -/
theorem coeff_lFactorLogDeriv (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    (x : X.finitePoints) (n : ℕ) :
    coeff n (F.lFactorLogDeriv ι x) =
      if (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ n ∧ n ≠ 0 then
        ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 : ℂ) *
          ι (LinearMap.trace (PadicAlgCl l) _ ((F.stalk x).frobeniusEnd ^
            (n / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1)))
      else 0 := by
  have hd := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  rw [lFactorLogDeriv, coeff_C_mul, coeff_expand]
  by_cases h₁ : (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ n
  · rw [ite_eq_left h₁]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnd : n / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≠ 0 :=
        (Nat.div_ne_zero_iff_of_dvd h₁).2 ⟨hn, hd⟩
      rw [ite_eq_left ⟨h₁, hn⟩, traceGen, coeff_map, coeff_mk, ite_eq_right hnd]
  · rw [ite_eq_right h₁, ite_eq_right fun h ↦ h₁ h.1, mul_zero]

variable [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The local factors of the `L`-series are multipliable in the product topology. -/
theorem hasProd_lFactor (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    HasProd (F.lFactor ι) (F.lSeries ι) := by
  have hfin := (X ↘ Spec (CommRingCat.of k₀)).finite_setOf_degreeOver_le
  refine (WithPiTopology.hasProd_of_X_pow_dvd_sub_one (fun n ↦ (hfin n).toFinset)
    fun n x hx ↦ X_pow_dvd_lFactor_sub_one ι F ?_).multipliable.hasProd
  by_contra h
  exact hx ((hfin n).mem_toFinset.2 (not_lt.1 h))

theorem multipliable_lFactor (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    Multipliable (F.lFactor ι) :=
  (F.hasProd_lFactor ι).multipliable

/-- **Regrouping of the rational points over the closed points.** The sum of the trace function
over `X₀(𝔽_{qⁿ})`, `n ≥ 1`, is `∑_{x, d(x) ∣ n} d(x) tr(Fₓ^{n / d(x)})`: the `𝔽_{qⁿ}`-points
over a closed point `x` with `d(x) ∣ n` are `d(x)` in number, each with trace `tr(Fₓ^{n/d(x)})`.
Here `T` is any finite set of closed points containing those of degree dividing `n`. -/
theorem sum_traceFunction_eq_sum (F : WeilSheaf k₀ l X) {n : ℕ} (hn : n ≠ 0)
    {T : Finset X.finitePoints}
    (hT : ∀ x : X.finitePoints, (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ n → x ∈ T) :
    ∑ᶠ y, F.traceFunction n y =
      ∑ x ∈ T with (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ n,
        ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 : PadicAlgCl l) *
          LinearMap.trace (PadicAlgCl l) _ ((F.stalk x).frobeniusEnd ^
            (n / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1)) := by
  classical
  set K := FiniteField.galoisExtension k₀ n
  have : Finite K := Module.finite_of_finite k₀
  have := (X ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints K
  let : Fintype ((X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) := Fintype.ofFinite _
  set T' := T.filter fun x ↦ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ n
  -- the number of rational points over a closed point
  have hmaps : ∀ y ∈ (Finset.univ : Finset ((X ↘ Spec (CommRingCat.of k₀)).fieldPoints K)),
      finitePointOfFieldPoint y ∈ T' :=
    fun y _ ↦ Finset.mem_filter.2 ⟨hT _ (degreeOver_finitePointOfFieldPoint_dvd y),
      degreeOver_finitePointOfFieldPoint_dvd y⟩
  have hcle : ∀ x ∈ T', (Finset.univ.filter fun y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K ↦
        finitePointOfFieldPoint y = x).card ≤
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 := fun x _ ↦ by
    refine le_trans ?_ ((X ↘ Spec (CommRingCat.of k₀)).card_fieldPoints_base_eq_le K x.2)
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun p ↦ ⟨p.1, congrArg Subtype.val
      (Finset.mem_filter.1 p.2).2⟩) fun p p' h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)
  have hcsum : ∑ x ∈ T', (Finset.univ.filter fun y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K ↦
        finitePointOfFieldPoint y = x).card =
      ∑ x ∈ T', (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 := by
    rw [← (X ↘ Spec (CommRingCat.of k₀)).pointCount_eq_sum hn hT, Scheme.Hom.pointCount,
      Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
  have hc := (Finset.sum_eq_sum_iff_of_le hcle).1 hcsum
  rw [finsum_eq_sum_of_fintype]
  simp_rw [traceFunction_eq_trace]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.sum_congr rfl fun y hy ↦ by rw [(Finset.mem_filter.1 hy).2], Finset.sum_const,
    nsmul_eq_mul, hc x hx]

/-- The logarithmic derivative of the `L`-series is the generating series of the sums of the
trace function over the rational points:
`t L'(t) = (∑_{n ≥ 1} (∑_{y ∈ X₀(𝔽_{qⁿ})} ι t_{F,n}(y)) tⁿ) L(t)`, the Euler-product form of the
point count. -/
theorem X_mul_derivative_lSeries (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    PowerSeries.X * derivative (R := ℂ) (F.lSeries ι) =
      PowerSeries.mk (fun n ↦ if n = 0 then 0 else ∑ᶠ y, ι (F.traceFunction n y)) *
        F.lSeries ι := by
  classical
  have hfin := (X ↘ Spec (CommRingCat.of k₀)).finite_setOf_degreeOver_le
  have hmem {n : ℕ} {x : X.finitePoints} (hx : x ∉ (hfin n).toFinset) :
      n < (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 := by
    by_contra h
    exact hx ((hfin n).mem_toFinset.2 (not_lt.1 h))
  refine WithPiTopology.X_mul_derivative_tprod_of_X_pow_dvd_sub_one (fun n ↦ (hfin n).toFinset)
    (fun n x hx ↦ X_pow_dvd_lFactor_sub_one ι F (hmem hx))
    (fun n x hx ↦ X_pow_dvd_lFactorLogDeriv ι F (hmem hx)) (X_mul_derivative_lFactor ι F)
    fun n ↦ ?_
  rw [coeff_mk]
  simp_rw [coeff_lFactorLogDeriv]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have := (X ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints (FiniteField.galoisExtension k₀ n)
  let : Fintype ((X ↘ Spec (CommRingCat.of k₀)).fieldPoints
    (FiniteField.galoisExtension k₀ n)) := Fintype.ofFinite _
  have hsum := F.sum_traceFunction_eq_sum hn (T := (hfin n).toFinset)
    fun x hx ↦ (hfin n).mem_toFinset.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hx)
  rw [finsum_eq_sum_of_fintype] at hsum
  rw [ite_eq_right hn, finsum_eq_sum_of_fintype, ← map_sum, hsum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [hn, ne_eq, not_false_eq_true, and_true, map_mul, map_natCast]

end WeilSheaf

end AlgebraicGeometry
