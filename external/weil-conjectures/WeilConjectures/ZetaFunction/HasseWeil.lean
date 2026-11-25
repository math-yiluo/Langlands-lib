/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.Statement
public import WeilConjectures.ZetaFunction.BettiSymmetry
public import WeilConjectures.ZetaFunction.CurveZeta
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# The Hasse–Weil bound

Let `X` be a smooth proper geometrically integral scheme of dimension `d ≥ 1` over a finite
field `k` with `q` elements, and let `P 0, …, P_{2d} ∈ ℤ[T]` be integral Frobenius factors of
its zeta function satisfying the Riemann hypothesis. The number of rational points of `X` is
the alternating sum of the traces of Frobenius, the two endpoint factors `P 0 = 1 - T` and
`P (2 * d) = 1 - qᵈ T` contribute `1` and `qᵈ`, and each of the `deg (P i)` reciprocal roots
in an intermediate degree `i` has absolute value `q^{i/2}`. The triangle inequality then
bounds the deviation of the point count from `qᵈ + 1`.

For a smooth projective curve of genus `g` this is the classical Hasse–Weil bound
`|N₁ - (q + 1)| ≤ 2 g √q`, since there `d = 1` and `deg (P 1) = 2 g`. The hypothesis `1 ≤ d` is
needed: for `d = 0` the two endpoint factors coincide and the bound fails.

This file formalises the Hasse–Weil bound of the blueprint block on zeta functions and the Weil
conjectures.

The proof compares logarithmic derivatives in the factorization of the zeta function: this
expresses `N n` as the alternating sum `∑ (-1) ^ i ∑ αⁿ` of the power sums of the reciprocal
roots `α` of the `P i`, the shadow of the Lefschetz trace formula.

## Main statements

- `AlgebraicGeometry.Scheme.abs_pointCount_sub_le_sum_finrank`: the Hasse–Weil bound with the
  Betti numbers `dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` (`corollary-point-count-estimates--1`), using the endpoint
  cohomology of `theorem-weil-conjectures-smooth-proper-schemes`
  (`AlgebraicGeometry.Scheme.endpoints_of_isIntegralFrobeniusFactor`).
- `AlgebraicGeometry.Scheme.Hom.pointCount_eq_sum_roots`: `N n = ∑ (-1) ^ i ∑ αⁿ`.
- `AlgebraicGeometry.Scheme.Hom.abs_pointCount_sub_le`: the Hasse–Weil bound over the degree `n`
  extension, `|N n - (q ^ (d n) + 1)| ≤ ∑_{0 < i < 2d} deg (P i) · q ^ (i n / 2)`.
- `AlgebraicGeometry.Scheme.Hom.abs_pointCount_one_sub_le`: the Hasse–Weil bound, the case
  `n = 1`.
- `AlgebraicGeometry.Scheme.Hom.abs_pointCount_sub_le_two_mul_genus`: the Hasse–Weil bound
  `|N n - (qⁿ + 1)| ≤ 2 g q^{n/2}` for a smooth proper geometrically integral curve of genus `g`.
  It uses `AlgebraicGeometry.Scheme.Hom.natDegree_eq_two_mul_genus_of_isWeilFactorization`,
  the identity `deg P 1 = 2 g`, proved by counting effective divisors with Riemann–Roch.

## References

- [A. Weil, *Numbers of solutions of equations in finite fields*][weil1949]
- [J.-P. Serre, *Zeta and L functions*][serre1965]
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

open PowerSeries

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

omit [Finite k] in
/-- **The point count as an alternating sum of power sums of reciprocal roots.** If the zeta
function of `X` factors as `∏ P i ^ ((-1) ^ (i + 1))` with `P i (0) = 1`, then for every `n ≥ 1`
the number of points of `X` over the degree `n` extension of `k` is
`N n = ∑ i, (-1) ^ i ∑_α αⁿ`, where `α` runs over the reciprocal roots `z⁻¹` of `P i`.

This is the trace formula `N n = ∑ (-1) ^ i tr (Fⁿ | V i)` of Step 1 of the blueprint proof of
`corollary-point-count-estimates--1`, read off from the factorization of the zeta function by
comparing logarithmic derivatives. -/
theorem Hom.pointCount_eq_sum_roots (f : X.Hom (Spec (.of k))) {q d : ℕ}
    {P : Fin (2 * d + 1) → Polynomial ℤ} (hfact : IsWeilFactorization q d f.zetaSeries P)
    {n : ℕ} (hn : n ≠ 0) :
    (f.pointCount n : ℂ) = ∑ i : Fin (2 * d + 1), (-1) ^ i.1 *
      (((P i).map (Int.castRingHom ℂ)).roots.map fun z ↦ z⁻¹ ^ n).sum := by
  classical
  set Q : Fin (2 * d + 1) → Polynomial ℂ := fun i ↦ (P i).map (Int.castRingHom ℂ) with hQdef
  have hQ0 : ∀ i, (Q i).coeff 0 = 1 := fun i ↦ by
    simp [hQdef, Polynomial.coeff_map, hfact.coeff_zero_eq_one i]
  set T : Fin (2 * d + 1) → ℂ⟦X⟧ := fun i ↦
    -PowerSeries.mk fun n ↦ if n = 0 then 0 else ((Q i).roots.map fun z ↦ z⁻¹ ^ n).sum with hT
  set NS : ℂ⟦X⟧ := PowerSeries.mk fun n ↦ if n = 0 then 0 else (f.pointCount n : ℂ) with hNS
  set se := Finset.univ.filter fun i : Fin (2 * d + 1) ↦ Even (i : ℕ) with hse
  set so := Finset.univ.filter fun i : Fin (2 * d + 1) ↦ Odd (i : ℕ) with hso
  set Zc : ℂ⟦X⟧ := map (algebraMap ℚ ℂ) f.zetaSeries with hZc
  have hQd : ∀ i, PowerSeries.X * derivative (R := ℂ) (Q i : ℂ⟦X⟧) =
      T i * (Q i : ℂ⟦X⟧) := fun i ↦
    X_mul_derivative_coe_of_coeff_zero_eq_one (IsAlgClosed.splits _) (hQ0 i)
  have hZ : PowerSeries.X * derivative (R := ℂ) Zc = NS * Zc := by
    have h0 : PowerSeries.X * derivative (R := ℚ) f.zetaSeries =
        (PowerSeries.mk fun n ↦ if n = 0 then 0 else (f.pointCount n : ℚ)) * f.zetaSeries :=
      X_mul_derivative_exp_subst _
    have h := congrArg (map (algebraMap ℚ ℂ)) h0
    rw [map_mul, map_mul, PowerSeries.map_X, map_derivative] at h
    rw [h]
    congr 1
    ext n
    simp only [hNS, PowerSeries.coeff_mk, coeff_map]
    split <;> simp
  have hfac : Zc * ∏ i ∈ se, (Q i : ℂ⟦X⟧) = ∏ i ∈ so, (Q i : ℂ⟦X⟧) := by
    have h := congrArg (map (algebraMap ℚ ℂ)) hfact.factorization
    have hcast : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    simpa only [map_mul, map_prod, ← Polynomial.polynomial_map_coe, Polynomial.map_map,
      hcast] using h
  have hE := X_mul_derivative_prod se fun i _ ↦ hQd i
  have hO := X_mul_derivative_prod so fun i _ ↦ hQd i
  have hL : PowerSeries.X * derivative (R := ℂ) (Zc * ∏ i ∈ se, (Q i : ℂ⟦X⟧)) =
      (NS + ∑ i ∈ se, T i) * (Zc * ∏ i ∈ se, (Q i : ℂ⟦X⟧)) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    linear_combination Zc * hE + (∏ i ∈ se, (Q i : ℂ⟦X⟧)) * hZ
  have hunit : IsUnit (∏ i ∈ so, (Q i : ℂ⟦X⟧)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_prod]
    simp [Polynomial.constantCoeff_coe, hQ0]
  have hkey : NS + ∑ i ∈ se, T i = ∑ i ∈ so, T i := by
    rw [hfac, hO] at hL
    exact (hunit.mul_left_cancel (by rw [mul_comm, hL, mul_comm])).symm
  have hc := congrArg (PowerSeries.coeff n) hkey
  simp only [map_add, map_sum, hNS, hT, PowerSeries.coeff_mk, map_neg, ite_eq_right hn,
    Finset.sum_neg_distrib, hse, hso, Finset.sum_filter, apply_ite (PowerSeries.coeff n),
    map_zero] at hc
  have halt : ∀ c : Fin (2 * d + 1) → ℂ, ∑ i : Fin (2 * d + 1), (-1) ^ i.1 * c i =
      (∑ i : Fin (2 * d + 1), if Even i.1 then c i else 0) -
        ∑ i : Fin (2 * d + 1), if Odd i.1 then c i else 0 := fun c ↦ by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases Nat.even_or_odd i.1 with h | h
    · rw [ite_eq_left h, ite_eq_right (by simpa using h), h.neg_one_pow, one_mul, sub_zero]
    · rw [ite_eq_right (by simpa using h), ite_eq_left h, h.neg_one_pow, neg_one_mul, zero_sub]
  rw [halt]
  linear_combination hc

/-- **The Hasse–Weil bound in every degree.** If the zeta function of `X` has integral Frobenius
factors `P i` satisfying the Riemann hypothesis, `d ≥ 1`, then for every `n ≥ 1` the number
`N n` of points of `X` over the degree `n` extension of `k` satisfies
`|N n - (q ^ (d n) + 1)| ≤ ∑_{0 < i < 2d} deg (P i) · q ^ (i n / 2)`.

The two endpoint factors `P 0 = 1 - T` and `P (2 * d) = 1 - qᵈ T` (the content of the blueprint
node `theorem-weil-conjectures-smooth-proper-schemes`, recorded in
`AlgebraicGeometry.IsWeilFactorization`) contribute `1` and `q ^ (d n)`, and each of the `deg (P i)`
reciprocal roots in degree `i` has absolute value `q ^ (i / 2)`.
(blueprint: `corollary-point-count-estimates--1`) -/
theorem Hom.abs_pointCount_sub_le (f : X.Hom (Spec (.of k))) {q d : ℕ}
    (hq : q = Nat.card k) (hd : 1 ≤ d) {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hfact : IsWeilFactorization q d f.zetaSeries P)
    (hrh : WeilRiemannHypothesis q d P) {n : ℕ} (hn : n ≠ 0) :
    |(f.pointCount n : ℝ) - ((q : ℝ) ^ (d * n) + 1)| ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ 0 < i.1 ∧ i.1 < 2 * d),
        ((P i).natDegree : ℝ) * (q : ℝ) ^ ((i.1 : ℝ) * n / 2) := by
  classical
  set s : Fin (2 * d + 1) → ℂ := fun i ↦
    (((P i).map (Int.castRingHom ℂ)).roots.map fun z ↦ z⁻¹ ^ n).sum with hs
  have hN := f.pointCount_eq_sum_roots hfact hn
  have hq0 : (q : ℂ) ≠ 0 := by
    rw [hq]
    exact_mod_cast Nat.card_pos.ne'
  have hs0 : s 0 = 1 := by
    have h : (P 0).map (Int.castRingHom ℂ) = 1 - Polynomial.C 1 * Polynomial.X := by
      simp [hfact.apply_zero]
    simp only [hs, h, Polynomial.roots_one_sub_C_mul_X one_ne_zero]
    simp
  have hslast : s (Fin.last _) = (q : ℂ) ^ (d * n) := by
    have h : (P (Fin.last _)).map (Int.castRingHom ℂ) =
        1 - Polynomial.C ((q : ℂ) ^ d) * Polynomial.X := by
      simp [hfact.apply_last]
    simp only [hs, h, Polynomial.roots_one_sub_C_mul_X (pow_ne_zero d hq0)]
    simp [pow_mul]
  have h0v : ((0 : Fin (2 * d + 1)) : ℕ) = 0 := rfl
  have hlast0 : (Fin.last (2 * d)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, h0v] at this
    omega
  have hsplit : ∑ i : Fin (2 * d + 1), (-1) ^ i.1 * s i =
      ((q : ℂ) ^ (d * n) + 1) + ∑ i ∈ Finset.univ.filter
        (fun i : Fin (2 * d + 1) ↦ 0 < i.1 ∧ i.1 < 2 * d), (-1) ^ i.1 * s i := by
    have hmem : Fin.last (2 * d) ∈ Finset.univ.erase (0 : Fin (2 * d + 1)) :=
      Finset.mem_erase.2 ⟨hlast0, Finset.mem_univ _⟩
    have hfil : (Finset.univ.erase (0 : Fin (2 * d + 1))).erase (Fin.last (2 * d)) =
        Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ 0 < i.1 ∧ i.1 < 2 * d) := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_filter, ne_eq, Fin.ext_iff,
        Fin.val_last, h0v, and_true, true_and]
      omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ← Finset.add_sum_erase _ _ hmem, hfil,
      hs0, hslast, h0v, Fin.val_last, pow_zero, (even_two_mul d).neg_one_pow]
    ring
  have hbound : ∀ i, ‖s i‖ ≤ ((P i).natDegree : ℝ) * (q : ℝ) ^ ((i.1 : ℝ) * n / 2) := by
    intro i
    have hq0' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hterm : ∀ z ∈ ((P i).map (Int.castRingHom ℂ)).roots,
        ‖z⁻¹ ^ n‖ = (q : ℝ) ^ ((i.1 : ℝ) * n / 2) := by
      intro z hz
      rw [norm_pow, norm_inv, hrh i z hz, ← Real.rpow_neg hq0', ← Real.rpow_natCast,
        ← Real.rpow_mul hq0']
      congr 1
      ring
    have hcard : Multiset.card ((P i).map (Int.castRingHom ℂ)).roots = (P i).natDegree := by
      rw [Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _),
        Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    refine (norm_multiset_sum_le _).trans (le_of_eq ?_)
    rw [Multiset.map_map, Function.comp_def, Multiset.map_congr rfl fun z hz ↦ hterm z hz,
      Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul]
  have hreal : ((f.pointCount n : ℝ) - ((q : ℝ) ^ (d * n) + 1) : ℝ) =
      ((f.pointCount n : ℂ) - ((q : ℂ) ^ (d * n) + 1)) := by
    push_cast
    rfl
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal, hN, hsplit, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hbound i

/-- **The Hasse–Weil bound.** If the zeta function of `X` has integral Frobenius factors `P i`
satisfying the Riemann hypothesis, then the number `N₁` of `k`-rational points of `X` differs
from `qᵈ + 1` by at most `∑_{0 < i < 2d} deg (P i) · q^{i/2}`.
(blueprint: `corollary-point-count-estimates`) -/
theorem Hom.abs_pointCount_one_sub_le (f : X.Hom (Spec (.of k))) {q d : ℕ}
    (hq : q = Nat.card k) (hd : 1 ≤ d) {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hfact : IsWeilFactorization q d f.zetaSeries P)
    (hrh : WeilRiemannHypothesis q d P) :
    |(f.pointCount 1 : ℝ) - ((q : ℝ) ^ d + 1)| ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ 0 < i.1 ∧ i.1 < 2 * d),
        ((P i).natDegree : ℝ) * (q : ℝ) ^ ((i.1 : ℝ) / 2) := by
  simpa using f.abs_pointCount_sub_le hq hd hfact hrh one_ne_zero

/-- **The degree of the middle Weil factor of a curve is twice the genus.** For a smooth proper
geometrically integral curve over a finite field, the factor `P 1` in the factorization
`Z = P 1 / ((1 - T) (1 - q T))` of its zeta function has degree `2 g`.

This is the zeta-function form of Step 4 of the blueprint proof of
`corollary-point-count-estimates--2`, `dim H¹(C ⊗ k̄, ℚ̄_ℓ) = 2 g`. It is proved here without
`ℓ`-adic cohomology, by F. K. Schmidt's argument: Riemann–Roch counts the effective divisors of
large degree, which are the coefficients of the zeta function, and together with the Riemann
hypothesis for `P 1` this forces `deg P 1 = 2 g`
(`AlgebraicGeometry.Scheme.natDegree_eq_two_mul_arithmeticGenus_of_isWeilFactorization`). The
genus `dim_k Γ(C, Ω¹)` is the arithmetic genus by
`AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`. -/
theorem Hom.natDegree_eq_two_mul_genus_of_isWeilFactorization
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] {P : Fin (2 * 1 + 1) → Polynomial ℤ}
    (hfact : IsWeilFactorization (Nat.card k) 1 f.zetaSeries P) :
    (P 1).natDegree = 2 * f.genus := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k)) :=
    ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := ‹IsProper f›
  have : GeometricallyIntegral (X ↘ Spec (CommRingCat.of k)) := ‹GeometricallyIntegral f›
  have : GeometricallyConnected (X ↘ Spec (CommRingCat.of k)) :=
    GeometricallyIntegral.geometricallyConnected f
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨P', hfact', -, hrh'⟩ := Scheme.weil_conjectures f 1
  obtain rfl : P = P' := hfact.eq_of_one hfact'
  rw [natDegree_eq_two_mul_arithmeticGenus_of_isWeilFactorization (C := X) hfact' hrh',
    ← genus_eq_arithmeticGenus]
  rfl

/-- **The Hasse–Weil bound for curves.** Let `C` be a smooth proper geometrically integral curve
of genus `g` over a finite field `k` with `q` elements. Then for every `n ≥ 1`,
`|#C(𝔽_{qⁿ}) - (qⁿ + 1)| ≤ 2 g q^{n/2}`.
(blueprint: `corollary-point-count-estimates--2`) -/
theorem Hom.abs_pointCount_sub_le_two_mul_genus (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f] {n : ℕ}
    (hn : n ≠ 0) :
    |(f.pointCount n : ℝ) - ((Nat.card k : ℝ) ^ n + 1)| ≤
      2 * f.genus * (Nat.card k : ℝ) ^ ((n : ℝ) / 2) := by
  obtain ⟨P, hfact, -, hrh⟩ := Scheme.weil_conjectures f 1
  have h := f.abs_pointCount_sub_le rfl le_rfl hfact hrh hn
  have hfil : Finset.univ.filter (fun i : Fin (2 * 1 + 1) ↦ 0 < i.1 ∧ i.1 < 2 * 1) = {1} := by
    decide
  rw [hfil, Finset.sum_singleton, f.natDegree_eq_two_mul_genus_of_isWeilFactorization hfact,
    one_mul] at h
  simpa using h

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

namespace Scheme

section Endpoints

open _root_.Polynomial

variable (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

variable (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `corollary-point-count-estimates--1` (Hasse–Weil bound in every dimension), in its
cohomological form: for `X₀` smooth, proper and geometrically connected of pure dimension
`d ≥ 1` over `k₀ = 𝔽_q` and every prime `ℓ ≠ p`, the number `N n = #X₀(𝔽_{qⁿ})` satisfies
`|N n - (q^{dn} + 1)| ≤ ∑_{0 < i < 2d} bᵢ q^{in/2}` with the Betti numbers
`bᵢ = dim_{ℚ̄_ℓ} Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`. -/
theorem abs_pointCount_sub_le_sum_finrank (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (hd : 1 ≤ d) {n : ℕ} (hn : n ≠ 0) :
    |((X ↘ Spec (CommRingCat.of k₀)).pointCount n : ℝ) - ((Nat.card k₀ : ℝ) ^ (d * n) + 1)| ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ 0 < i.1 ∧ i.1 < 2 * d),
        (Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℝ) *
          (Nat.card k₀ : ℝ) ^ ((i.1 : ℝ) * n / 2) := by
  obtain ⟨P, hfact, -, hrh, hP⟩ := exists_isWeilFactorization_of_smoothProper k₀ X d
  refine ((X ↘ Spec (CommRingCat.of k₀)).abs_pointCount_sub_le rfl hd hfact hrh hn).trans
    (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
  rw [natDegree_eq_finrank_of_isIntegralFrobeniusFactor k₀ X (hP i) l]

end Endpoints

end Scheme

end AlgebraicGeometry

end
