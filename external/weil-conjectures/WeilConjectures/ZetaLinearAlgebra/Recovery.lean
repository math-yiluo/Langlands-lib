/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.NormalizedGauss
public import WeilConjectures.ZetaLinearAlgebra.WeightStrata
public import WeilConjectures.ZetaLinearAlgebra.Weights

/-!
# Recovery of the pure factors from the reduced fraction

Let `P 0, …, P r` be complex polynomials with constant coefficient `1`, with `P i` universally
pure of weight `i`, and suppose the two parity products cross-multiply against a coprime
normalized rational fraction `A / B`:
`(∏_{i odd} P i) * B = (∏_{i even} P i) * A`.

The parity products are then `A` and `B` themselves, and each individual factor `P i` is
recovered from the rational data alone: it is the weight-`i` stratum of `A` for odd `i` and of
`B` for even `i`, in particular it is defined over `ℚ`. Since `A` and `B` are, in the situation
of interest, images of normalized integer polynomials, each `P i` is even the image of a
normalized integer polynomial — the integrality half of the Weil factorisation.

## Main results

- `Polynomial.parityPart` — the member `A` or `B` of the fraction that the weight-`w` factor is
  cut out of: the numerator `A` for odd `w`, the denominator `B` for even `w`.
- `Polynomial.eq_map_weightFactor` — each `P i` is the image of the weight-`i` stratum of
  `Polynomial.parityPart A B i`.
- `Polynomial.exists_int_weightFactor` — a weight stratum of the image of a normalized integer
  polynomial is again the image of a normalized integer polynomial.
- `Polynomial.exists_int_of_isUniversallyPure` — the whole family `P` comes from a family of
  normalized integer polynomials.
- `Polynomial.exists_int_norm_eq_of_isUniversallyPure` — the same family, together with the
  Riemann hypothesis statement: every complex root of the `i`-th member has absolute value
  `q ^ (-i / 2)`.
-/

@[expose] public section

open scoped Polynomial

namespace Polynomial

variable {q r : ℕ}

/-- The member of the reduced fraction `A / B` that the weight-`w` factor is cut out of: the
numerator `A` for odd `w`, the denominator `B` for even `w`. -/
def parityPart (A B : ℚ[X]) (w : ℕ) : ℚ[X] := if Odd w then A else B

theorem parityPart_of_odd {A B : ℚ[X]} {w : ℕ} (hw : Odd w) : parityPart A B w = A := ite_eq_left hw

theorem parityPart_of_even {A B : ℚ[X]} {w : ℕ} (hw : Even w) : parityPart A B w = B :=
  ite_eq_right (Nat.not_odd_iff_even.2 hw)

/-- **Recovery of an individual factor.** If the parity products of a family of universally pure
polynomials of distinct weights cross-multiply against a coprime normalized rational fraction
`A / B`, then each member `P i` of the family is the image of the weight-`i` stratum of `A`
(for odd `i`) or of `B` (for even `i`). In particular each `P i` is defined over `ℚ`. -/
theorem eq_map_weightFactor (hq : 1 < q) {P : Fin (r + 1) → ℂ[X]}
    (hP : ∀ i, (P i).IsUniversallyPureOfWeight q i.1) {A B : ℚ[X]} (hAB : IsCoprime A B)
    (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (h : (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P i) *
        B.map (algebraMap ℚ ℂ) =
      (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P i) * A.map (algebraMap ℚ ℂ))
    (i : Fin (r + 1)) :
    P i = ((parityPart A B i.1).weightFactor q i.1).map (algebraMap ℚ ℂ) := by
  have hP' : ∀ j, (P j).IsPureOfWeight q j.1 := fun j ↦ (hP j).isPureOfWeight
  obtain ⟨hO, hE⟩ := prod_odd_eq_map_and_prod_even_eq_map hq hP' hAB hA h
  have key : ∀ (s : Finset (Fin (r + 1))) (R : ℚ[X]), R.coeff 0 = 1 → i ∈ s →
      (∏ j ∈ s, P j) = R.map (algebraMap ℚ ℂ) →
      P i = (R.weightFactor q i.1).map (algebraMap ℚ ℂ) := by
    intro s R hR his hs
    have hT1 : (∏ j ∈ s.erase i, P j).coeff 0 = 1 :=
      coeff_zero_prod_eq_one (w := fun j : Fin (r + 1) ↦ j.1) fun j _ ↦ hP' j
    have hT0 : (∏ j ∈ s.erase i, P j) ≠ 0 := fun h0 ↦ by rw [h0] at hT1; simp at hT1
    refine eq_map_weightFactor_of_isUniversallyPure hR (P i) (∏ j ∈ s.erase i, P j)
      (hP i).1 hT1 ?_ (hP i).2 ?_
    · rw [Finset.mul_prod_erase _ _ his, hs]
    · intro z hz hcon
      rw [roots_prod _ _ hT0] at hz
      obtain ⟨j, hj, hzj⟩ := Multiset.mem_bind.1 hz
      exact Finset.ne_of_mem_erase hj
        (Fin.val_injective (((hP j).2 z hzj).weight_unique hq hcon))
  rcases Nat.even_or_odd i.1 with he | ho
  · rw [parityPart_of_even he]
    exact key _ B hB (by simpa using he) hE
  · rw [parityPart_of_odd ho]
    exact key _ A hA (by simpa using ho) hO

/-- **Integrality of a weight stratum.** A weight stratum of the image of a normalized integer
polynomial is again the image of a normalized integer polynomial. -/
theorem exists_int_weightFactor {a : ℤ[X]} (ha : a.coeff 0 = 1) {R : ℚ[X]}
    (haR : a.map (Int.castRingHom ℚ) = R) (q w : ℕ) :
    ∃ p : ℤ[X], p.coeff 0 = 1 ∧ p.map (Int.castRingHom ℚ) = R.weightFactor q w := by
  have hR : R.coeff 0 = 1 := by rw [← haR, coeff_map, ha, map_one]
  have hdvd : R.weightFactor q w ∣ a.map (Int.castRingHom ℚ) := by
    rw [haR]; exact weightFactor_dvd hR
  exact exists_int_of_coeff_zero_eq_one_of_dvd ha (coeff_zero_weightFactor hR) hdvd

/-- Each weight stratum of a reduced normalized fraction whose numerator and denominator are
images of normalized integer polynomials is itself the image of a normalized integer
polynomial. -/
theorem exists_int_weightFactor_parityPart {A B : ℚ[X]} {A₀ B₀ : ℤ[X]} (hA₀ : A₀.coeff 0 = 1)
    (hB₀ : B₀.coeff 0 = 1) (hA : A₀.map (Int.castRingHom ℚ) = A)
    (hB : B₀.map (Int.castRingHom ℚ) = B) (q w : ℕ) :
    ∃ p : ℤ[X], p.coeff 0 = 1 ∧
      p.map (Int.castRingHom ℚ) = (parityPart A B w).weightFactor q w := by
  rcases Nat.even_or_odd w with hw | hw
  · rw [parityPart_of_even hw]
    exact exists_int_weightFactor hB₀ hB q w
  · rw [parityPart_of_odd hw]
    exact exists_int_weightFactor hA₀ hA q w

/-- **The integer family.** If the parity products of a family of universally pure polynomials of
distinct weights cross-multiply against a coprime normalized fraction `A / B` whose numerator and
denominator are images of normalized integer polynomials, then the whole family comes from
normalized integer polynomials. -/
theorem exists_int_of_isUniversallyPure (hq : 1 < q) {P : Fin (r + 1) → ℂ[X]}
    (hP : ∀ i, (P i).IsUniversallyPureOfWeight q i.1) {A B : ℚ[X]} (hAB : IsCoprime A B)
    {A₀ B₀ : ℤ[X]} (hA₀ : A₀.coeff 0 = 1) (hB₀ : B₀.coeff 0 = 1)
    (hA : A₀.map (Int.castRingHom ℚ) = A) (hB : B₀.map (Int.castRingHom ℚ) = B)
    (h : (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P i) *
        B.map (algebraMap ℚ ℂ) =
      (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P i) * A.map (algebraMap ℚ ℂ)) :
    ∃ P' : Fin (r + 1) → ℤ[X], (∀ i, (P' i).coeff 0 = 1) ∧
      (∀ i, (P' i).map (Int.castRingHom ℂ) = P i) := by
  have hA1 : A.coeff 0 = 1 := by rw [← hA, coeff_map, hA₀, map_one]
  have hB1 : B.coeff 0 = 1 := by rw [← hB, coeff_map, hB₀, map_one]
  choose P' hP'1 hP'2 using fun i : Fin (r + 1) ↦
    exists_int_weightFactor_parityPart hA₀ hB₀ hA hB q i.1
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  refine ⟨P', hP'1, fun i ↦ ?_⟩
  rw [eq_map_weightFactor hq hP hAB hA1 hB1 h i, ← hP'2 i, map_map, hcomp]

/-- **The Riemann hypothesis for the recovered family.** In the situation of
`Polynomial.exists_int_of_isUniversallyPure`, every complex root of the `i`-th member of the
recovered integer family has absolute value `q ^ (-i / 2)`. -/
theorem exists_int_norm_eq_of_isUniversallyPure (hq : 1 < q) {P : Fin (r + 1) → ℂ[X]}
    (hP : ∀ i, (P i).IsUniversallyPureOfWeight q i.1) {A B : ℚ[X]} (hAB : IsCoprime A B)
    {A₀ B₀ : ℤ[X]} (hA₀ : A₀.coeff 0 = 1) (hB₀ : B₀.coeff 0 = 1)
    (hA : A₀.map (Int.castRingHom ℚ) = A) (hB : B₀.map (Int.castRingHom ℚ) = B)
    (h : (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Odd i.1, P i) *
        B.map (algebraMap ℚ ℂ) =
      (∏ i ∈ Finset.univ.filter fun i : Fin (r + 1) ↦ Even i.1, P i) * A.map (algebraMap ℚ ℂ)) :
    ∃ P' : Fin (r + 1) → ℤ[X], (∀ i, (P' i).coeff 0 = 1) ∧
      (∀ i, (P' i).map (Int.castRingHom ℂ) = P i) ∧
      ∀ i, ∀ z ∈ ((P' i).map (Int.castRingHom ℂ)).roots,
        ‖z‖ = (q : ℝ) ^ (-(i.1 : ℝ) / 2) := by
  obtain ⟨P', hP'1, hP'2⟩ := exists_int_of_isUniversallyPure hq hP hAB hA₀ hB₀ hA hB h
  exact ⟨P', hP'1, hP'2, fun i z hz ↦ (hP i).isPureOfWeight.2 z (hP'2 i ▸ hz)⟩

end Polynomial
