/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.BettiNumbers
public import WeilConjectures.Mathlib.Algebra.Polynomial.RingDivision
public import WeilConjectures.ZetaFunction.IntegralFrobeniusFactors
public import WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots

/-!
# Betti numbers of a smooth proper variety

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over
`k₀ = 𝔽_q`, with integral Frobenius factors `P₀, …, P_{2d}` and Betti numbers `bᵢ = deg Pᵢ`.
Then `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `ℓ ≠ p`, `bᵢ = b_{2d-i}`, `b₀ = b_{2d} = 1`,
`P₀ = 1 - T` and `P_{2d} = 1 - qᵈ T`; consequently `Z(X₀, T)` has a pole of order exactly one at
`T = 1` and, for `d ≥ 1`, at `T = q^{-d}` (blueprint
`theorem-weil-conjectures-smooth-proper-schemes`).

## Main statements

- `AlgebraicGeometry.Scheme.natDegree_eq_finrank_of_isIntegralFrobeniusFactor`:
  `deg Pᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` (`theorem-weil-conjectures-smooth-proper-schemes--8`).
- `AlgebraicGeometry.Scheme.weilBettiNumber_eq_finrank`: `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for all
  `i ∈ ℤ` (`theorem-weil-conjectures-smooth-proper-schemes--8`).
- `AlgebraicGeometry.Scheme.betti_symmetry`: blueprint
`theorem-weil-conjectures-smooth-proper-schemes`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace WeilRiemannHypothesis

variable {q d : ℕ} {P : Fin (2 * d + 1) → Polynomial ℤ}

/-- Under the Riemann hypothesis, a rational root `x` of `Pᵢ` has `|x| = q^{-i/2}`. -/
theorem abs_eq_of_isRoot (hrh : WeilRiemannHypothesis q d P) (h0 : ∀ i, (P i).coeff 0 = 1)
    {i : Fin (2 * d + 1)} {x : ℚ} (h : ((P i).map (Int.castRingHom ℚ)).IsRoot x) :
    |(x : ℝ)| = (q : ℝ) ^ (-(i.1 : ℝ) / 2) := by
  have hne : (P i).map (Int.castRingHom ℂ) ≠ 0 := fun h' ↦ by
    simpa [h0 i] using congr(Polynomial.coeff $h' 0)
  have hz : (x : ℂ) ∈ ((P i).map (Int.castRingHom ℂ)).roots := by
    rw [Polynomial.mem_roots hne]
    have := h.map (f := Rat.castHom ℂ)
    rwa [Polynomial.map_map, RingHom.ext_int ((Rat.castHom ℂ).comp (Int.castRingHom ℚ))
      (Int.castRingHom ℂ)] at this
  rw [← hrh i _ hz, Complex.norm_ratCast]

/-- Under the Riemann hypothesis, the complex reciprocal roots of `Pᵢ` (the roots of the reversed
polynomial) have absolute value `q^{i/2}`. -/
theorem norm_eq_of_mem_roots_reverse (hrh : WeilRiemannHypothesis q d P)
    (h0 : ∀ i, (P i).coeff 0 = 1) (i : Fin (2 * d + 1)) {y : ℂ}
    (hy : y ∈ ((P i).reverse.map (Int.castRingHom ℂ)).roots) :
    ‖y‖ = (q : ℝ) ^ ((i.1 : ℝ) / 2) := by
  have hne : (P i).map (Int.castRingHom ℂ) ≠ 0 := fun h' ↦ by
    simpa [h0 i] using congr(Polynomial.coeff $h' 0)
  rw [← Polynomial.reverse_map (RingHom.injective_int _), Polynomial.mem_roots_reverse_iff hne]
    at hy
  have := hrh i _ ((Polynomial.mem_roots hne).2 hy.2)
  rwa [norm_inv, neg_div, Real.rpow_neg (Nat.cast_nonneg q), inv_inj] at this

/-- Under the Riemann hypothesis, a positive rational `x = q^{-j/2}` is a root of no factor `Pᵢ`
with `i ≠ j`. -/
theorem not_isRoot (hrh : WeilRiemannHypothesis q d P) (h0 : ∀ i, (P i).coeff 0 = 1)
    (hq : 1 < q) {j : Fin (2 * d + 1)} {x : ℚ} (hx : (x : ℝ) = (q : ℝ) ^ (-(j.1 : ℝ) / 2))
    {i : Fin (2 * d + 1)} (hij : i ≠ j) : ¬ ((P i).map (Int.castRingHom ℚ)).IsRoot x := by
  intro h
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hpos : (0 : ℝ) ≤ x := hx ▸ (Real.rpow_pos_of_pos (by linarith) _).le
  have e := hrh.abs_eq_of_isRoot h0 h
  rw [abs_of_nonneg hpos, hx] at e
  have e' : (-(j.1 : ℝ) / 2) = -(i.1 : ℝ) / 2 :=
    le_antisymm ((Real.rpow_le_rpow_left_iff hq').1 e.le) ((Real.rpow_le_rpow_left_iff hq').1 e.ge)
  exact hij (Fin.ext (by exact_mod_cast (by linarith : (i.1 : ℝ) = j.1)))

/-- **Weight separation at a pole.** Under the Riemann hypothesis, if `x = q^{-j/2}` is a simple
root of `Pⱼ` for an even `j`, then `x` is a simple root of `∏_{i even} Pᵢ` and not a root of
`∏_{i odd} Pᵢ`: the quotient `∏_{i odd} Pᵢ / ∏_{i even} Pᵢ` has a simple pole at `x`. -/
theorem pole_of_rootMultiplicity_eq_one (hrh : WeilRiemannHypothesis q d P)
    (h0 : ∀ i, (P i).coeff 0 = 1) (hq : 1 < q) {j : Fin (2 * d + 1)} (hj : Even j.1) {x : ℚ}
    (hx : (x : ℝ) = (q : ℝ) ^ (-(j.1 : ℝ) / 2))
    (hm : ((P j).map (Int.castRingHom ℚ)).rootMultiplicity x = 1) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
        (P i).map (Int.castRingHom ℚ)).rootMultiplicity x = 1 ∧
      ¬ (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
        (P i).map (Int.castRingHom ℚ)).IsRoot x := by
  have hne (i : Fin (2 * d + 1)) : (P i).map (Int.castRingHom ℚ) ≠ 0 := fun h' ↦ by
    simpa [h0 i] using congr(Polynomial.coeff $h' 0)
  refine ⟨?_, ?_⟩
  · rw [Polynomial.rootMultiplicity_prod _ _ _ (Finset.prod_ne_zero_iff.2 fun i _ ↦ hne i),
      Finset.sum_eq_single j (fun i _ hij ↦ Polynomial.rootMultiplicity_eq_zero
        (hrh.not_isRoot h0 hq hx hij)) (fun h ↦ (h (by simpa using hj)).elim), hm]
  · rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    rintro ⟨i, hi, h⟩
    refine hrh.not_isRoot h0 hq hx (fun hij ↦ ?_) h
    rw [Finset.mem_filter, hij, ← Nat.not_even_iff_odd] at hi
    exact hi.2 hj

end WeilRiemannHypothesis

namespace Scheme

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes--8`: the degree of an integral
Frobenius factor in degree `i` is `dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every prime `ℓ ≠ p`: scalar extension
along the injective `ℤ → ℚ̄_ℓ` preserves degrees, and `deg P_{i,ℓ} = dim Hⁱ`
(`AlgebraicGeometry.Scheme.natDegree_frobeniusCharpolyRev`). In particular the degree does not
depend on `ℓ`. -/
theorem natDegree_eq_finrank_of_isIntegralFrobeniusFactor
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {i : ℤ} {P : Polynomial ℤ}
    (hP : IsIntegralFrobeniusFactor k₀ X i P) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] :
    P.natDegree =
      Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l X).cohomology i).carrier := by
  rw [← natDegree_frobeniusCharpolyRev, ← hP l,
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]

/-- Blueprint `corollary-functional-equation--3`: the image in `ℚ̄_ℓ` of the determinant constant
`D = (-1)^b [T^b] P` of an integral Frobenius factor `P` in degree `i` is the determinant
`det(F | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))` of the geometric Frobenius, for every prime `ℓ ≠ p`: the leading
coefficient of `det(1 - T F)` is `(-1)^{dim} det F`. -/
theorem map_weilDeterminantConstant_eq_det
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {i : ℤ} {P : Polynomial ℤ}
    (hP : IsIntegralFrobeniusFactor k₀ X i P) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] :
    (weilDeterminantConstant P : PadicAlgCl l) =
      LinearMap.det ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd := by
  have hlc : (P.leadingCoeff : PadicAlgCl l) =
      (frobeniusCharpolyRev k₀ l X i).leadingCoeff := by
    rw [← hP l, Polynomial.leadingCoeff_map_of_injective (RingHom.injective_int _)]
    rfl
  rw [weilDeterminantConstant, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    ← Polynomial.leadingCoeff, hlc,
    leadingCoeff_frobeniusCharpolyRev, natDegree_eq_finrank_of_isIntegralFrobeniusFactor k₀ X hP l,
    ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

variable (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

omit [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] in
/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes--8` (Betti-number comparison): for
`X₀` smooth, proper and geometrically connected of pure dimension `d` with integral Frobenius
factors `Pᵢ`, the Betti numbers `bᵢ` (`AlgebraicGeometry.weilBettiNumber`; `deg Pᵢ` for `0 ≤ i ≤ 2d`
and `0` otherwise) satisfy `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `i ∈ ℤ` and every prime `ℓ ≠ p`;
in particular they do not depend on `ℓ`. Outside `[0, 2d]` both sides vanish
(`AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant`). -/
theorem weilBettiNumber_eq_finrank {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) (l : ℕ)
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (i : ℤ) :
    weilBettiNumber P i =
      Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l X).cohomology i).carrier := by
  by_cases hi : 0 ≤ i ∧ i ≤ 2 * d
  · lift i to ℕ using hi.1
    have hi' : i < 2 * d + 1 := by omega
    rw [show (i : ℤ) = ((⟨i, hi'⟩ : Fin (2 * d + 1)) : ℕ) from rfl, weilBettiNumber_natCast,
      natDegree_eq_finrank_of_isIntegralFrobeniusFactor k₀ X (hP _) l]
  · have hi' : i < 0 ∨ ((2 * d : ℕ) : ℤ) < i := by omega
    have := WeilSheaf.subsingleton_cohomology_adicConstant k₀ l X d (i := i) (by omega)
    rw [weilBettiNumber_eq_zero P hi', Module.finrank_zero_of_subsingleton]

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes` (endpoint cohomology): for `X₀`
smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, there are
Frobenius-equivariant isomorphisms `H⁰(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ`, with geometric Frobenius acting by
`1`, and `H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-d)`, with geometric Frobenius acting by `qᵈ`. -/
theorem exists_linearEquiv_cohomology_endpoints (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] :
    (∃ e : ((WeilSheaf.adicConstant k₀ l X).cohomology 0).carrier ≃ₗ[PadicAlgCl l]
        PadicAlgCl l,
      ∀ z, e (((WeilSheaf.adicConstant k₀ l X).cohomology 0).frobenius z) = e z) ∧
    ∃ e : ((WeilSheaf.adicConstant k₀ l X).cohomology (2 * d)).carrier ≃ₗ[PadicAlgCl l]
        PadicAlgCl l,
      ∀ z, e (((WeilSheaf.adicConstant k₀ l X).cohomology (2 * d)).frobenius z) =
        (Nat.card k₀ : PadicAlgCl l) ^ d * e z := by
  refine ⟨⟨LinearEquiv.ofFinrankEq _ _ (by
    rw [WeilSheaf.finrank_cohomology_zero_adicConstant, Module.finrank_self]), fun z ↦ ?_⟩, ?_⟩
  · rw [WeilSheaf.frobenius_cohomology_zero_adicConstant]
    rfl
  · obtain ⟨T, htr, -, -, -, hF, -⟩ := WeilSheaf.poincareDuality k₀ l X d
    exact ⟨LinearEquiv.ofBijective T.trace htr, hF⟩

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes` (endpoint factors): for `X₀` smooth,
proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, the integral Frobenius
factors satisfy `P₀ = 1 - T` and `P_{2d} = 1 - qᵈ T`, and the endpoint Betti numbers are
`b₀ = b_{2d} = 1`. -/
theorem endpoints_of_isIntegralFrobeniusFactor {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    P 0 = 1 - Polynomial.X ∧
      P (Fin.last (2 * d)) = 1 - Polynomial.C ((Nat.card k₀ : ℤ) ^ d) * Polynomial.X ∧
      (P 0).natDegree = 1 ∧ (P (Fin.last (2 * d))).natDegree = 1 := by
  obtain ⟨l, hl, hne⟩ : ∃ l : ℕ, l.Prime ∧ ringChar k₀ ≠ l := by
    by_cases h : ringChar k₀ = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, h⟩
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (ringChar k₀ ≠ l) := ⟨hne⟩
  obtain ⟨P', hfact, -, -, hP'⟩ := exists_isWeilFactorization_of_smoothProper k₀ X d
  obtain rfl : P = P' := funext fun i ↦
    Polynomial.map_injective _ (RingHom.injective_int (Int.castRingHom (PadicAlgCl l)))
      ((hP i l).trans (hP' i l).symm)
  refine ⟨hfact.apply_zero, hfact.apply_last, ?_, ?_⟩
  · rw [natDegree_eq_finrank_of_isIntegralFrobeniusFactor k₀ X (hP 0) l, Fin.val_zero,
      Nat.cast_zero,
      WeilSheaf.finrank_cohomology_zero_adicConstant]
  · obtain ⟨-, e, -⟩ := exists_linearEquiv_cohomology_endpoints k₀ X d l
    rw [natDegree_eq_finrank_of_isIntegralFrobeniusFactor k₀ X (hP _) l, Fin.val_last,
      Nat.cast_mul,
      Nat.cast_two, e.finrank_eq, Module.finrank_self]

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes` (Betti symmetry and the endpoint
factors): for `X₀` smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`,
with integral Frobenius factors `Pᵢ` and Betti numbers `bᵢ = deg Pᵢ`:

* `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every prime `ℓ ≠ p`;
* `bᵢ = b_{2d-i}` and `b₀ = b_{2d} = 1`;
* `P₀ = 1 - T` and `P_{2d} = 1 - qᵈ T`;
* `Z(X₀, T) = ∏_{i odd} Pᵢ / ∏_{i even} Pᵢ` has a pole of order exactly one at `T = 1`: the
  denominator vanishes there to order one and the numerator does not vanish there; and, if
  `d ≥ 1`, likewise at `T = q^{-d}`. -/
theorem betti_symmetry {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    (∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (i : Fin (2 * d + 1)),
      (P i).natDegree = Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier) ∧
    (∀ i : Fin (2 * d + 1), (P i.rev).natDegree = (P i).natDegree) ∧
    (P 0).natDegree = 1 ∧ (P (Fin.last (2 * d))).natDegree = 1 ∧
    P 0 = 1 - Polynomial.X ∧
    P (Fin.last (2 * d)) = 1 - C ((Nat.card k₀ : ℤ) ^ d) * Polynomial.X ∧
    ((∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
        (P i).map (Int.castRingHom ℚ)).rootMultiplicity 1 = 1 ∧
      ¬ (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
        (P i).map (Int.castRingHom ℚ)).IsRoot 1) ∧
    (1 ≤ d →
      (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
        (P i).map (Int.castRingHom ℚ)).rootMultiplicity ((Nat.card k₀ : ℚ) ^ d)⁻¹ = 1 ∧
      ¬ (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
        (P i).map (Int.castRingHom ℚ)).IsRoot ((Nat.card k₀ : ℚ) ^ d)⁻¹) := by
  obtain ⟨hfact, hfe, hrh⟩ := isWeilFactorization_of_isIntegralFrobeniusFactor k₀ X d hP
  obtain ⟨h0, hlast, hd0, hdlast⟩ := endpoints_of_isIntegralFrobeniusFactor k₀ X d hP
  have hq : 1 < Nat.card k₀ := Finite.one_lt_card
  refine ⟨fun l _ _ i ↦ natDegree_eq_finrank_of_isIntegralFrobeniusFactor k₀ X (hP i) l,
    hfe.natDegree_rev, hd0, hdlast, h0, hlast, ?_, fun hd ↦ ?_⟩
  · refine hrh.pole_of_rootMultiplicity_eq_one hfact.coeff_zero_eq_one hq (j := 0) (by simp)
      (by simp) ?_
    rw [h0, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
    exact rootMultiplicity_one_sub_X
  · have hpos : (0 : ℝ) < Nat.card k₀ := by exact_mod_cast Nat.card_pos
    refine hrh.pole_of_rootMultiplicity_eq_one hfact.coeff_zero_eq_one hq (j := Fin.last _)
      (by simp) ?_ ?_
    · rw [Fin.val_last, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, Nat.cast_mul,
        Nat.cast_two, neg_div, mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_neg hpos.le,
        Real.rpow_natCast]
    · rw [hlast, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X, eq_intCast, Int.cast_pow, Int.cast_natCast]
      exact rootMultiplicity_one_sub_C_mul_X (pow_ne_zero _ (by exact_mod_cast hq.ne_bot))

end Scheme

end AlgebraicGeometry
