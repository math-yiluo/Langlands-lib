/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EulerProductAux
public import WeilConjectures.Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import WeilConjectures.Mathlib.Algebra.Polynomial.BigOperators
public import WeilConjectures.Mathlib.Data.Fin.Rev
public import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Derivative
public import WeilConjectures.ZetaFunction.CohomologicalFamily
public import WeilConjectures.ZetaFunction.DualityReciprocity
public import WeilConjectures.ZetaLinearAlgebra.AlternatingEulerProduct
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TracePow

/-!
# Corollaries of the trace formula: the zeta function and its functional equation

Let `X₀` be a separated scheme of finite type over `k₀ = 𝔽_q` and `ℓ ≠ p`. The trace formula for
the constant Weil sheaf `ℚ̄_ℓ` gives the cohomological expression of the zeta function

`Z(X₀, T) = ∏ᵢ det(1 - T F | H_cⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))^{(-1)^{i+1}}` in `ℚ̄_ℓ⟦T⟧`.

If the Frobenius eigenvalues satisfy the reciprocity given by Poincaré duality (for `X₀` smooth,
proper and geometrically connected of pure dimension `d`), this turns into the functional
equation

`Z(X₀, 1/(qᵈ T)) = (-1)^χ D T^χ Z(X₀, T) = ε q^{dχ/2} T^χ Z(X₀, T)`,

with `bᵢ = dim Hⁱ`, `χ = ∑ᵢ (-1)ⁱ bᵢ`, `D = ∏ᵢ det(Fᵢ)^{(-1)ⁱ}`, `D² = q^{dχ}` and `ε = ±1`. It
is stated as an identity of values of the rational function `∏ᵢ det(1 - t Fᵢ)^{(-1)^{i+1}}` at
every `t ≠ 0` of `ℚ̄_ℓ`, which is the identity of rational functions over the infinite field
`ℚ̄_ℓ`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.map_zetaSeries_eq_inv_alternatingCharpolyRevProd`: the
  cohomological product for the zeta function.
- `Polynomial.alternatingProdEval_inv_mul_inv_of_roots_eq_map_inv` and
  `Polynomial.prod_leadingCoeff_sq_of_roots_eq_map_inv`: the functional equation of an
  alternating product of polynomials whose roots are exchanged by `z ↦ (c z)⁻¹`.
- `AlgebraicGeometry.Scheme.functional_equation_frobeniusCharpolyRev`: the functional equation in
  terms of the Frobenius on the cohomology, with the
  duality inputs as hypotheses, supplied by the library's Poincaré duality
  (`AlgebraicGeometry.WeilSheaf.poincareDuality`, sorry-free).
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace WeilSheaf

variable (k₀) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `corollary-point-counting-zeta-function` (cohomological product): for a separated
scheme `X₀` of finite type over `k₀ = 𝔽_q` and `ℓ ≠ p`,

`Z(X₀, T) = ∏ᵢ det(1 - T F | H_cⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))^{(-1)^{i+1}}` in `ℚ̄_ℓ⟦T⟧`,

where `S` is any finite set of degrees outside of which `H_cⁱ` vanishes; the right hand side is
the inverse of the alternating determinant `LinearMap.alternatingCharpolyRevProd`. Both sides
have constant coefficient `1`, and their logarithmic derivatives are the generating series of
`#X₀(𝔽_{qᵐ})` and of `∑ᵢ (-1)ⁱ Tr(Fᵐ | H_cⁱ)`, which agree by the point-counting trace formula
`AlgebraicGeometry.WeilSheaf.pointCount_eq_finsum_trace_compactlySupportedCohomology`. -/
theorem map_zetaSeries_eq_inv_alternatingCharpolyRevProd {S : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton ((adicConstant k₀ l X).compactlySupportedCohomology i).carrier) :
    PowerSeries.map (algebraMap ℚ (PadicAlgCl l)) (X ↘ Spec (CommRingCat.of k₀)).zetaSeries =
      (LinearMap.alternatingCharpolyRevProd S
        (fun i ↦ ((adicConstant k₀ l X).compactlySupportedCohomology i).frobeniusEnd) 1)⁻¹ := by
  set f := X ↘ Spec (CommRingCat.of k₀)
  set φ := algebraMap ℚ (PadicAlgCl l)
  have hF : PowerSeries.X * PowerSeries.derivative (PowerSeries.map φ f.zetaSeries) =
      PowerSeries.map φ (PowerSeries.mk fun n ↦ if n = 0 then (0 : ℚ) else f.pointCount n) *
        PowerSeries.map φ f.zetaSeries := by
    rw [← PowerSeries.map_derivative, ← PowerSeries.map_X φ, ← map_mul,
      f.X_mul_derivative_zetaSeries, map_mul]
  have hG := LinearMap.X_mul_derivative_inv_alternatingCharpolyRevProd S
    (fun i ↦ ((adicConstant k₀ l X).compactlySupportedCohomology i).frobeniusEnd) one_ne_zero
  ext n
  refine PowerSeries.coeff_eq_of_X_mul_derivative_eq hF hG ?_ ?_ (m := n) ?_ n le_rfl
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, f.constantCoeff_zetaSeries, map_one,
      PowerSeries.constantCoeff_inv,
      LinearMap.constantCoeff_alternatingCharpolyRevProd _ _ one_ne_zero, inv_one]
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_mk, ite_eq_left rfl, map_zero]
  · intro i _
    rcases eq_or_ne i 0 with rfl | hi0
    · simp
    have hsupp : (Function.support fun j : ℤ ↦ (j.negOnePow : ℤ) •
        LinearMap.trace (PadicAlgCl l) _
          (((adicConstant k₀ l X).compactlySupportedCohomology j).frobeniusEnd ^ i)) ⊆ S := by
      intro j hj
      by_contra h
      have := hS j h
      have h0 : ((adicConstant k₀ l X).compactlySupportedCohomology j).frobeniusEnd ^ i = 0 :=
        LinearMap.ext fun _ ↦ Subsingleton.elim _ _
      rw [Function.mem_support, h0, map_zero, smul_zero] at hj
      exact hj rfl
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, ite_eq_right hi0,
      ite_eq_left ⟨hi0, one_dvd i⟩, Nat.cast_one, one_mul, Nat.div_one, map_natCast,
      pointCount_eq_finsum_trace_compactlySupportedCohomology k₀ l X
        (Nat.one_le_iff_ne_zero.2 hi0), finsum_eq_sum_of_support_subset _ hsupp]

end WeilSheaf

end AlgebraicGeometry

namespace Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K] {d : ℕ} {P : Fin (2 * d + 1) → K[X]} {c : K}

/-- If the roots of `P (2d - i)` are the `(c z)⁻¹` for the roots `z` of `P i`, the degrees of
`P i` and `P (2d - i)` agree. -/
theorem natDegree_rev_of_roots_eq_map_inv
    (h : ∀ i, (P i.rev).roots = (P i).roots.map fun z ↦ (c * z)⁻¹) (i : Fin (2 * d + 1)) :
    (P i.rev).natDegree = (P i).natDegree := by
  rw [← splits_iff_card_roots.1 (IsAlgClosed.splits (P i.rev)),
    ← splits_iff_card_roots.1 (IsAlgClosed.splits (P i)), h i, Multiset.card_map]

/-- **The square of the determinant scalar.** For polynomials `P 0, …, P (2d)` with constant
coefficient `1` whose roots are exchanged by `z ↦ (c z)⁻¹` between degrees `i` and `2d - i`, the
alternating product `Δ = ∏ᵢ Dᵢ^{(-1)ⁱ}` of the constants `Dᵢ = (-1)^{deg Pᵢ} lc Pᵢ` satisfies
`Δ² = c^χ`, `χ = ∑ᵢ (-1)ⁱ deg Pᵢ`. -/
theorem prod_leadingCoeff_sq_of_roots_eq_map_inv (h0 : ∀ i, (P i).coeff 0 = 1) (hc : c ≠ 0)
    (h : ∀ i, (P i.rev).roots = (P i).roots.map fun z ↦ (c * z)⁻¹) :
    (∏ i : Fin (2 * d + 1),
      ((-1) ^ (P i).natDegree * (P i).leadingCoeff) ^ ((-1 : ℤ) ^ (i : ℕ))) ^ 2 =
      c ^ alternatingNatDegreeSum P := by
  set D : Fin (2 * d + 1) → K := fun i ↦ (-1) ^ (P i).natDegree * (P i).leadingCoeff
  have hD : ∀ i, D i * D i.rev = c ^ (P i).natDegree := fun i ↦ by
    have h' := leadingCoeff_mul_leadingCoeff_of_roots_eq_map_inv (h0 i) (h0 i.rev) hc (h i)
    simp only [D, natDegree_rev_of_roots_eq_map_inv h i]
    rw [show ((-1 : K) ^ (P i).natDegree * (P i).leadingCoeff) *
        ((-1) ^ (P i).natDegree * (P i.rev).leadingCoeff) =
        ((-1) ^ (P i).natDegree * (-1) ^ (P i).natDegree) *
          ((P i).leadingCoeff * (P i.rev).leadingCoeff) by ring,
      ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, h']
  have hrev : ∏ i : Fin (2 * d + 1), D i ^ ((-1 : ℤ) ^ (i : ℕ)) =
      ∏ i : Fin (2 * d + 1), D i.rev ^ ((-1 : ℤ) ^ (i : ℕ)) := by
    conv_lhs => rw [← Equiv.prod_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, Fin.neg_one_pow_rev]
  rw [sq]
  nth_rewrite 2 [hrev]
  rw [← Finset.prod_mul_distrib, alternatingNatDegreeSum, zpow_sum₀ hc]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← mul_zpow, hD i, ← zpow_natCast, ← zpow_mul, mul_comm]

/-- **The functional equation of an alternating product.** For polynomials `P 0, …, P (2d)` with
constant coefficient `1` whose roots are exchanged by `z ↦ (c z)⁻¹` between degrees `i` and
`2d - i`, the alternating product `Z(t) = ∏ᵢ Pᵢ(t)^{(-1)^{i+1}}` satisfies

`Z((c t)⁻¹) = (-1)^χ t^χ (∏ᵢ Dᵢ^{(-1)ⁱ}) Z(t)`

at every `t ≠ 0`, where `χ = ∑ᵢ (-1)ⁱ deg Pᵢ` and `Dᵢ = (-1)^{deg Pᵢ} lc Pᵢ`. -/
theorem alternatingProdEval_inv_mul_inv_of_roots_eq_map_inv (h0 : ∀ i, (P i).coeff 0 = 1)
    (hc : c ≠ 0) (h : ∀ i, (P i.rev).roots = (P i).roots.map fun z ↦ (c * z)⁻¹) {t : K}
    (ht : t ≠ 0) :
    alternatingProdEval P (c⁻¹ * t⁻¹) =
      (-1) ^ alternatingNatDegreeSum P * t ^ alternatingNatDegreeSum P *
        (∏ i : Fin (2 * d + 1),
          ((-1) ^ (P i).natDegree * (P i).leadingCoeff) ^ ((-1 : ℤ) ^ (i : ℕ))) *
        alternatingProdEval P t := by
  have key : ∀ i : Fin (2 * d + 1),
      (P i.rev).eval (c⁻¹ * t⁻¹) ^ ((-1 : ℤ) ^ ((i.rev : ℕ) + 1)) =
        (-1) ^ ((-1 : ℤ) ^ (i : ℕ) * (P i).natDegree) *
          t ^ ((-1 : ℤ) ^ (i : ℕ) * (P i).natDegree) *
          ((-1) ^ (P i).natDegree * (P i).leadingCoeff) ^ ((-1 : ℤ) ^ (i : ℕ)) *
          (P i).eval t ^ ((-1 : ℤ) ^ ((i : ℕ) + 1)) := by
    intro i
    have e := eval_inv_mul_inv_of_roots_eq_map_inv (h0 i.rev) (h0 i) hc
      (by simpa only [Fin.rev_rev] using h i.rev) ht
    rw [e, natDegree_rev_of_roots_eq_map_inv h i, pow_succ, Fin.neg_one_pow_rev, ← pow_succ]
    have hl : (P i).leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero.2 fun h ↦ by simpa [h] using h0 i
    rcases neg_one_pow_eq_or ℤ (i : ℕ) with h | h <;>
      simp only [pow_succ, h, zpow_neg, zpow_one, neg_mul, one_mul, neg_neg, zpow_natCast,
        mul_inv, inv_inv] <;>
      field_simp <;>
      simp [← pow_mul]
  rw [alternatingProdEval, alternatingProdEval, ← Equiv.prod_comp Fin.revPerm]
  simp only [Fin.revPerm_apply]
  rw [Finset.prod_congr rfl fun i _ ↦ key i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, ← zpow_sum₀ (neg_ne_zero.2 one_ne_zero),
    ← zpow_sum₀ ht, alternatingNatDegreeSum]

end Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace Scheme

variable (k₀) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]

/-- If the eigenvalues of `F` on `H^j` are the `qᵈ / α` for the eigenvalues `α` of `F` on `Hⁱ`
(`i + j = 2d`), then the roots of `P_{2d-i}(T) = det(1 - T F | H^{2d-i})` are the `(qᵈ z)⁻¹` for
the roots `z` of `Pᵢ(T) = det(1 - T F | Hⁱ)`. -/
theorem roots_frobeniusCharpolyRev_rev (hdual : ∀ i j : ℤ, i + j = 2 * d →
      ((WeilSheaf.adicConstant k₀ l X).cohomology j).frobeniusEnd.charpoly.roots =
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.charpoly.roots.map
          fun α ↦ (Nat.card k₀ : PadicAlgCl l) ^ d / α)
    (i : Fin (2 * d + 1)) :
    (frobeniusCharpolyRev k₀ l X (i.rev : ℕ)).roots =
      (frobeniusCharpolyRev k₀ l X (i : ℕ)).roots.map
        fun z ↦ ((Nat.card k₀ : PadicAlgCl l) ^ d * z)⁻¹ := by
  have hsum : ((i : ℕ) : ℤ) + ((i.rev : ℕ) : ℤ) = 2 * d := by
    simp only [Fin.val_rev]
    omega
  have hr := hdual _ _ hsum
  rw [frobeniusCharpolyRev_def, frobeniusCharpolyRev_def, FrobeniusModule.localPolynomial,
    FrobeniusModule.localPolynomial,
    LinearMap.roots_charpolyRev ((WeilSheaf.adicConstant k₀ l X).cohomology _).frobeniusEnd
      (LinearEquiv.isUnit_det' _),
    LinearMap.roots_charpolyRev ((WeilSheaf.adicConstant k₀ l X).cohomology _).frobeniusEnd
      (LinearEquiv.isUnit_det' _), hr, Multiset.map_map,
    Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ ↦ ?_
  simp [div_eq_mul_inv]

/-- The functional equation `AlgebraicGeometry.Scheme.functional_equation_frobeniusCharpolyRev`
from its two duality inputs: the reciprocity of the Frobenius eigenvalues (`hdual`) and the
evenness of the middle Betti number for odd `d` (`hmid`). -/
private theorem functional_equation_frobeniusCharpolyRev_of_reciprocity
    (hdual : ∀ i j : ℤ, i + j = 2 * d →
      ((WeilSheaf.adicConstant k₀ l X).cohomology j).frobeniusEnd.charpoly.roots =
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.charpoly.roots.map
          fun α ↦ (Nat.card k₀ : PadicAlgCl l) ^ d / α)
    (hmid : Odd d → Even (Module.finrank (PadicAlgCl l)
      ((WeilSheaf.adicConstant k₀ l X).cohomology d).carrier)) :
    (∀ i : Fin (2 * d + 1),
      Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i.rev : ℕ)).carrier =
        Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier) ∧
    Even ((d : ℤ) * ∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) *
      (Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) ∧
    (∏ i : Fin (2 * d + 1), LinearMap.det
        ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
          ((-1 : ℤ) ^ (i : ℕ))) ^ 2 =
      (Nat.card k₀ : PadicAlgCl l) ^ ((d : ℤ) * ∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) *
        (Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) ∧
    (∀ t : PadicAlgCl l, t ≠ 0 →
      alternatingProdEval (fun i : Fin (2 * d + 1) ↦ frobeniusCharpolyRev k₀ l X (i : ℕ))
          (((Nat.card k₀ : PadicAlgCl l) ^ d * t)⁻¹) =
        (-1) ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
          (∏ i : Fin (2 * d + 1), LinearMap.det
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
              ((-1 : ℤ) ^ (i : ℕ))) *
          t ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
          alternatingProdEval (fun i : Fin (2 * d + 1) ↦ frobeniusCharpolyRev k₀ l X (i : ℕ))
            t) ∧
    ∃ m : ℤ, (d : ℤ) * (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) = 2 * m ∧
      ((-1) ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
          (∏ i : Fin (2 * d + 1), LinearMap.det
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
              ((-1 : ℤ) ^ (i : ℕ))) * (Nat.card k₀ : PadicAlgCl l) ^ (-m) = 1 ∨
        (-1) ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
          (∏ i : Fin (2 * d + 1), LinearMap.det
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
              ((-1 : ℤ) ^ (i : ℕ))) * (Nat.card k₀ : PadicAlgCl l) ^ (-m) = -1) ∧
      ∀ t : PadicAlgCl l, t ≠ 0 →
        alternatingProdEval (fun i : Fin (2 * d + 1) ↦ frobeniusCharpolyRev k₀ l X (i : ℕ))
            (((Nat.card k₀ : PadicAlgCl l) ^ d * t)⁻¹) =
          ((-1) ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
              ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
            (∏ i : Fin (2 * d + 1), LinearMap.det
              ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
                ((-1 : ℤ) ^ (i : ℕ))) * (Nat.card k₀ : PadicAlgCl l) ^ (-m)) *
            (Nat.card k₀ : PadicAlgCl l) ^ m *
            t ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
              ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
            alternatingProdEval (fun i : Fin (2 * d + 1) ↦ frobeniusCharpolyRev k₀ l X (i : ℕ))
              t := by
  set P : Fin (2 * d + 1) → (PadicAlgCl l)[X] := fun i ↦ frobeniusCharpolyRev k₀ l X (i : ℕ)
    with hP
  set H := WeilSheaf.adicConstant k₀ l X
  set q : PadicAlgCl l := (Nat.card k₀ : PadicAlgCl l)
  have hq : q ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hqd : q ^ d ≠ 0 := pow_ne_zero _ hq
  have h0 : ∀ i, (P i).coeff 0 = 1 := fun i ↦ coeff_zero_frobeniusCharpolyRev k₀ l X _
  have hroots : ∀ i, (P i.rev).roots = (P i).roots.map fun z ↦ (q ^ d * z)⁻¹ :=
    roots_frobeniusCharpolyRev_rev k₀ l X d hdual
  have hdeg : ∀ i, (P i).natDegree =
      Module.finrank (PadicAlgCl l) (H.cohomology (i : ℕ)).carrier :=
    fun i ↦ natDegree_frobeniusCharpolyRev k₀ l X _
  have hchi : alternatingNatDegreeSum P = ∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) *
      (Module.finrank (PadicAlgCl l) (H.cohomology (i : ℕ)).carrier : ℤ) := by
    simp only [alternatingNatDegreeSum, hdeg]
  have hdet : ∀ i, (-1) ^ (P i).natDegree * (P i).leadingCoeff =
      LinearMap.det (H.cohomology (i : ℕ)).frobeniusEnd := fun i ↦ by
    rw [leadingCoeff_frobeniusCharpolyRev, ← hdeg i, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_mul]
  have hD : ∏ i : Fin (2 * d + 1), LinearMap.det (H.cohomology (i : ℕ)).frobeniusEnd ^
      ((-1 : ℤ) ^ (i : ℕ)) = ∏ i : Fin (2 * d + 1),
        ((-1) ^ (P i).natDegree * (P i).leadingCoeff) ^ ((-1 : ℤ) ^ (i : ℕ)) := by
    simp only [hdet]
  -- Betti symmetry
  have hb : ∀ i : Fin (2 * d + 1),
      Module.finrank (PadicAlgCl l) (H.cohomology (i.rev : ℕ)).carrier =
        Module.finrank (PadicAlgCl l) (H.cohomology (i : ℕ)).carrier := fun i ↦ by
    rw [← hdeg, ← hdeg]
    exact natDegree_rev_of_roots_eq_map_inv hroots i
  -- `d χ` is even
  have heven : Even ((d : ℤ) * alternatingNatDegreeSum P) := by
    let m : Fin (2 * d + 1) := ⟨d, by omega⟩
    have hm : m.rev = m := Fin.ext (by simp only [Fin.val_rev, m]; omega)
    obtain ⟨k, hk⟩ := even_alternatingNatDegreeSum_sub_of_natDegree_rev
      (natDegree_rev_of_roots_eq_map_inv hroots) hm
    rcases Nat.even_or_odd d with hd | hd
    · obtain ⟨e, he⟩ := hd
      refine ⟨(e : ℤ) * alternatingNatDegreeSum P, ?_⟩
      rw [show (d : ℤ) = e + e by exact_mod_cast he]
      ring
    · obtain ⟨b, hb⟩ := hmid hd
      refine ⟨(d : ℤ) * k + (d : ℤ) * b, ?_⟩
      have hPm : ((P m).natDegree : ℤ) = b + b := by
        rw [hdeg m]
        exact_mod_cast hb
      have : alternatingNatDegreeSum P = k + k + b + b := by omega
      rw [this]
      ring
  have hsq := prod_leadingCoeff_sq_of_roots_eq_map_inv h0 hqd hroots
  have hfe : ∀ t : PadicAlgCl l, t ≠ 0 → alternatingProdEval P ((q ^ d * t)⁻¹) =
      (-1) ^ alternatingNatDegreeSum P * (∏ i : Fin (2 * d + 1),
        ((-1) ^ (P i).natDegree * (P i).leadingCoeff) ^ ((-1 : ℤ) ^ (i : ℕ))) *
        t ^ alternatingNatDegreeSum P * alternatingProdEval P t := fun t ht ↦ by
    rw [mul_inv, alternatingProdEval_inv_mul_inv_of_roots_eq_map_inv h0 hqd hroots ht]
    ring
  rw [← hchi, hD]
  obtain ⟨m, hm⟩ := heven
  have hm' : (d : ℤ) * alternatingNatDegreeSum P = 2 * m := by rw [hm]; ring
  have hsq' : (∏ i : Fin (2 * d + 1),
      ((-1) ^ (P i).natDegree * (P i).leadingCoeff) ^ ((-1 : ℤ) ^ (i : ℕ))) ^ 2 =
        q ^ ((d : ℤ) * alternatingNatDegreeSum P) := by
    rw [hsq, ← zpow_natCast, ← zpow_mul]
  refine ⟨hb, ⟨m, hm⟩, hsq', hfe, m, hm', ?_, fun t ht ↦ ?_⟩
  · refine mul_self_eq_one_iff.1 ?_
    have h1 : ((-1 : PadicAlgCl l) ^ alternatingNatDegreeSum P) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      norm_num
    have h2 : (q ^ (-m)) ^ 2 * q ^ ((d : ℤ) * alternatingNatDegreeSum P) = 1 := by
      rw [hm', ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq]
      ring_nf
      exact zpow_zero _
    rw [← sq, mul_pow, mul_pow, hsq', h1, one_mul, mul_comm, h2]
  · rw [hfe t ht]
    have hqm : q ^ (-m) * q ^ m = 1 := by rw [← zpow_add₀ hq]; simp
    linear_combination (-((-1) ^ alternatingNatDegreeSum P * (∏ i : Fin (2 * d + 1),
        ((-1) ^ (P i).natDegree * (P i).leadingCoeff) ^ ((-1 : ℤ) ^ (i : ℕ))) *
        t ^ alternatingNatDegreeSum P * alternatingProdEval P t)) * hqm

variable [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `corollary-functional-equation` (functional equation, cohomological form): let `X₀`
be smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, `ℓ ≠ p`,
`Hⁱ = Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` with Frobenius `Fᵢ`, `bᵢ = dim Hⁱ`, `χ = ∑ᵢ (-1)ⁱ bᵢ`,
`D = ∏ᵢ det(Fᵢ)^{(-1)ⁱ}` and `Z(t) = ∏ᵢ det(1 - t Fᵢ)^{(-1)^{i+1}}` (the products over
`0 ≤ i ≤ 2d`; `Z` is the rational function whose expansion is the zeta series,
`AlgebraicGeometry.Scheme.map_zetaSeries_mul_evenFrobeniusProduct`). Then

* `b_{2d-i} = bᵢ`;
* `d χ` is even;
* `D² = q^{dχ}`;
* `Z(1/(qᵈ t)) = (-1)^χ D t^χ Z(t)` for every `t ≠ 0` in `ℚ̄_ℓ`;
* writing `d χ = 2 m`, the sign `ε = (-1)^χ D q^{-m}` is `±1` and
  `Z(1/(qᵈ t)) = ε q^m t^χ Z(t)` for every `t ≠ 0`.

The identities at all `t ≠ 0` of the infinite field `ℚ̄_ℓ` are the identity of rational functions
of the blueprint (the value of a rational function at a pole being `0` on both sides). The two
inputs from Poincaré duality (`AlgebraicGeometry.WeilSheaf.poincareDuality`) are the reciprocity
of the Frobenius eigenvalues and, for odd `d`, the evenness of the middle Betti number
(`AlgebraicGeometry.Scheme.even_finrank_cohomology_middle`). -/
theorem functional_equation_frobeniusCharpolyRev :
    (∀ i : Fin (2 * d + 1),
      Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i.rev : ℕ)).carrier =
        Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier) ∧
    Even ((d : ℤ) * ∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) *
      (Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) ∧
    (∏ i : Fin (2 * d + 1), LinearMap.det
        ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
          ((-1 : ℤ) ^ (i : ℕ))) ^ 2 =
      (Nat.card k₀ : PadicAlgCl l) ^ ((d : ℤ) * ∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) *
        (Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) ∧
    (∀ t : PadicAlgCl l, t ≠ 0 →
      alternatingProdEval (fun i : Fin (2 * d + 1) ↦ frobeniusCharpolyRev k₀ l X (i : ℕ))
          (((Nat.card k₀ : PadicAlgCl l) ^ d * t)⁻¹) =
        (-1) ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
          (∏ i : Fin (2 * d + 1), LinearMap.det
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
              ((-1 : ℤ) ^ (i : ℕ))) *
          t ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
          alternatingProdEval (fun i : Fin (2 * d + 1) ↦ frobeniusCharpolyRev k₀ l X (i : ℕ))
            t) ∧
    ∃ m : ℤ, (d : ℤ) * (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) = 2 * m ∧
      ((-1) ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
          (∏ i : Fin (2 * d + 1), LinearMap.det
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
              ((-1 : ℤ) ^ (i : ℕ))) * (Nat.card k₀ : PadicAlgCl l) ^ (-m) = 1 ∨
        (-1) ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
          (∏ i : Fin (2 * d + 1), LinearMap.det
            ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
              ((-1 : ℤ) ^ (i : ℕ))) * (Nat.card k₀ : PadicAlgCl l) ^ (-m) = -1) ∧
      ∀ t : PadicAlgCl l, t ≠ 0 →
        alternatingProdEval (fun i : Fin (2 * d + 1) ↦ frobeniusCharpolyRev k₀ l X (i : ℕ))
            (((Nat.card k₀ : PadicAlgCl l) ^ d * t)⁻¹) =
          ((-1) ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
              ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
            (∏ i : Fin (2 * d + 1), LinearMap.det
              ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd ^
                ((-1 : ℤ) ^ (i : ℕ))) * (Nat.card k₀ : PadicAlgCl l) ^ (-m)) *
            (Nat.card k₀ : PadicAlgCl l) ^ m *
            t ^ (∑ i : Fin (2 * d + 1), (-1) ^ (i : ℕ) * (Module.finrank (PadicAlgCl l)
              ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier : ℤ)) *
            alternatingProdEval (fun i : Fin (2 * d + 1) ↦ frobeniusCharpolyRev k₀ l X (i : ℕ))
              t :=
  functional_equation_frobeniusCharpolyRev_of_reciprocity k₀ l X d
    (fun i j h ↦ ((WeilSheaf.poincareDuality k₀ l X d).choose_spec.2.2.2.2.2.2.1 i j h).2)
    (even_finrank_cohomology_middle k₀ X d l)

end Scheme

end AlgebraicGeometry

end
