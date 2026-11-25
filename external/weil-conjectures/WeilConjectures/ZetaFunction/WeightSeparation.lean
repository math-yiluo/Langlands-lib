/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.SmoothProper

/-!
# Weight separation and the parity factorization

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over
`k₀ = 𝔽_q`, and `ℓ ≠ p`. By root purity
(`AlgebraicGeometry.Scheme.isPureOfWeight_map_frobeniusCharpolyRev`)
every reciprocal root of `P_{i,ℓ}` has absolute value `q^{i/2}` under every embedding
`ι : ℚ̄_ℓ → ℂ`. These absolute values are pairwise distinct, so distinct `P_{i,ℓ}` are coprime,
the parity products `N_ℓ = ∏_{i odd} P_{i,ℓ}` and `D_ℓ = ∏_{i even} P_{i,ℓ}` are coprime, and
`Z(X₀, T) = N_ℓ(T) / D_ℓ(T)`; the roots of `P_{i,ℓ}` are exactly the roots of the parity product
of the parity of `i` of absolute value `q^{-i/2}`.

## Main statements

- `AlgebraicGeometry.Scheme.isCoprime_frobeniusCharpolyRev`: `P_{i,ℓ}` and `P_{j,ℓ}` are coprime
  for `i ≠ j`.
- `AlgebraicGeometry.Scheme.isCoprime_oddFrobeniusProduct_evenFrobeniusProduct`: `N_ℓ` and `D_ℓ`
  are coprime.
- `AlgebraicGeometry.Scheme.roots_map_frobeniusCharpolyRev_eq_filter`: the roots of `ι P_{i,ℓ}`
  are the roots of `ι N_ℓ` or `ι D_ℓ` of absolute value `q^{-i/2}`.
- `AlgebraicGeometry.Scheme.weight_separation`: blueprint `lemma-reciprocal-roots-zeta` and
  `lemma-reciprocal-roots-zeta`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace Scheme

variable (k₀) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

include d

/-- Blueprint `lemma-reciprocal-roots-zeta`: for `i ≠ j` the determinant factors `P_{i,ℓ}` and
`P_{j,ℓ}` have no common root and are coprime in `ℚ̄_ℓ[T]`: under an embedding `ι : ℚ̄_ℓ → ℂ` their
roots have the distinct absolute values `q^{-i/2}` and `q^{-j/2}`. -/
theorem isCoprime_frobeniusCharpolyRev {i j : ℕ} (hij : i ≠ j) :
    IsCoprime (frobeniusCharpolyRev k₀ l X i) (frobeniusCharpolyRev k₀ l X j) := by
  obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringHom_complex l
  exact (isCoprime_map ι).1 <|
    (isPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι i).isCoprime Finite.one_lt_card
      (isPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι j) hij

/-- Blueprint `lemma-reciprocal-roots-zeta`: the parity products `N_ℓ` and `D_ℓ` are coprime, a
common root coming from a pair of factors of distinct parities, hence of distinct weights. -/
theorem isCoprime_oddFrobeniusProduct_evenFrobeniusProduct :
    IsCoprime (oddFrobeniusProduct k₀ l X d) (evenFrobeniusProduct k₀ l X d) := by
  refine IsCoprime.prod_left fun i hi ↦ IsCoprime.prod_right fun j hj ↦ ?_
  simp only [Finset.mem_filter] at hi hj
  exact isCoprime_frobeniusCharpolyRev k₀ l X d fun h ↦ (Nat.not_odd_iff_even.2 hj.2) (h ▸ hi.2)

omit [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] in
/-- Blueprint `lemma-reciprocal-roots-zeta`: the odd parity product has constant coefficient `1`. -/
theorem coeff_zero_oddFrobeniusProduct [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    (oddFrobeniusProduct k₀ l X d).coeff 0 = 1 := by
  rw [oddFrobeniusProduct, coeff_zero_prod]
  exact Finset.prod_eq_one fun i _ ↦ coeff_zero_frobeniusCharpolyRev k₀ l X i

omit [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] in
/-- Blueprint `lemma-reciprocal-roots-zeta`: the even parity product has constant coefficient
`1`. -/
theorem coeff_zero_evenFrobeniusProduct [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    (evenFrobeniusProduct k₀ l X d).coeff 0 = 1 := by
  rw [evenFrobeniusProduct, coeff_zero_prod]
  exact Finset.prod_eq_one fun i _ ↦ coeff_zero_frobeniusCharpolyRev k₀ l X i

/-- The parity product containing the factor of degree `i`: `N_ℓ` for `i` odd and `D_ℓ` for `i`
even. -/
noncomputable abbrev parityFrobeniusProduct (i : ℕ) : Polynomial (PadicAlgCl l) :=
  if Even i then evenFrobeniusProduct k₀ l X d else oddFrobeniusProduct k₀ l X d

/-- Blueprint `lemma-reciprocal-roots-zeta`, multiset clause: for `i ≤ 2d` and an embedding
`ι : ℚ̄_ℓ → ℂ`, the ordinary root multiset of `ι P_{i,ℓ}` is the submultiset of the roots of the
parity product of the parity of `i` whose reciprocals `α` satisfy `|α| = q^{i/2}`, i.e. of
absolute value `q^{-i/2}`. -/
theorem roots_map_frobeniusCharpolyRev_eq_filter (ι : PadicAlgCl l →+* ℂ) {i : ℕ}
    (hi : i ≤ 2 * d) :
    ((frobeniusCharpolyRev k₀ l X i).map ι).roots =
      (((parityFrobeniusProduct k₀ l X d i).map ι).roots.filter
        fun z ↦ ‖z‖ = (Nat.card k₀ : ℝ) ^ (-(i : ℝ) / 2)) := by
  have hP (j : ℕ) : ((frobeniusCharpolyRev k₀ l X j).map ι).IsPureOfWeight (Nat.card k₀) j :=
    isPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι j
  have hmem : i ∈ Finset.range (2 * d + 1) := Finset.mem_range.2 (by omega)
  unfold parityFrobeniusProduct
  split_ifs with h
  · rw [evenFrobeniusProduct, Polynomial.map_prod]
    exact (Polynomial.roots_prod_filter_norm_eq Finite.one_lt_card (fun j _ ↦ hP j)
      (Finset.mem_filter.2 ⟨hmem, h⟩)).symm
  · rw [oddFrobeniusProduct, Polynomial.map_prod]
    exact (Polynomial.roots_prod_filter_norm_eq Finite.one_lt_card (fun j _ ↦ hP j)
      (Finset.mem_filter.2 ⟨hmem, Nat.not_even_iff_odd.1 h⟩)).symm

/-- Blueprint `lemma-reciprocal-roots-zeta` and `lemma-reciprocal-roots-zeta` (weight separation and
the parity factorization): for `X₀` smooth, proper and geometrically connected of pure dimension
`d`,

* `P_{i,ℓ}` and `P_{j,ℓ}` are coprime for `i ≠ j`;
* the parity products `N_ℓ = ∏_{i odd} P_{i,ℓ}` and `D_ℓ = ∏_{i even} P_{i,ℓ}` are coprime and
  have constant coefficient `1`;
* `Z(X₀, T) = N_ℓ(T) / D_ℓ(T)` in `ℚ̄_ℓ⟦T⟧`;
* for every embedding `ι : ℚ̄_ℓ → ℂ` and `i ≤ 2d`, the roots of `ι P_{i,ℓ}` are the roots of
  `ι N_ℓ` (`i` odd) or `ι D_ℓ` (`i` even) of absolute value `q^{-i/2}`. -/
theorem weight_separation :
    (∀ i j : ℕ, i ≠ j →
      IsCoprime (frobeniusCharpolyRev k₀ l X i) (frobeniusCharpolyRev k₀ l X j)) ∧
    IsCoprime (oddFrobeniusProduct k₀ l X d) (evenFrobeniusProduct k₀ l X d) ∧
    (oddFrobeniusProduct k₀ l X d).coeff 0 = 1 ∧ (evenFrobeniusProduct k₀ l X d).coeff 0 = 1 ∧
    PowerSeries.map (algebraMap ℚ (PadicAlgCl l)) (X ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        (evenFrobeniusProduct k₀ l X d : PowerSeries (PadicAlgCl l)) =
      (oddFrobeniusProduct k₀ l X d : PowerSeries (PadicAlgCl l)) ∧
    ∀ (ι : PadicAlgCl l →+* ℂ) (i : ℕ), i ≤ 2 * d →
      ((frobeniusCharpolyRev k₀ l X i).map ι).roots =
        (((parityFrobeniusProduct k₀ l X d i).map ι).roots.filter
          fun z ↦ ‖z‖ = (Nat.card k₀ : ℝ) ^ (-(i : ℝ) / 2)) :=
  ⟨fun _ _ ↦ isCoprime_frobeniusCharpolyRev k₀ l X d,
    isCoprime_oddFrobeniusProduct_evenFrobeniusProduct k₀ l X d,
    coeff_zero_oddFrobeniusProduct k₀ l X d, coeff_zero_evenFrobeniusProduct k₀ l X d,
    map_zetaSeries_mul_evenFrobeniusProduct k₀ l X d,
    fun ι _ hi ↦ roots_map_frobeniusCharpolyRev_eq_filter k₀ l X d ι hi⟩

end Scheme

end AlgebraicGeometry
