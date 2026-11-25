/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Artin–Schreier polynomials with a simple pole over `k((t))`

For a field `k`, an integer `n ≥ 2` and `b ∈ kˣ`, the polynomial `Xⁿ - X - b t⁻¹` is irreducible
over the Laurent series field `k((t))`. In characteristic `p` with `n` a power of `p` this is the
Artin–Schreier extension `uⁿ - u = b / t`, the local equation at `t = 0` of the Artin–Schreier
cover `uⁿ - u = b x` of the affine line in the coordinate `t = 1 / x` at infinity.

The proof inverts the variable: if `u` is a root then `y = u⁻¹` is a root of
`Yⁿ + (t / b) (Yⁿ⁻¹ - 1)`, which is Eisenstein at `t` over `k[[t]]`, hence irreducible over
`k((t))` by Gauss's lemma. Thus `[k((t))(u) : k((t))] = n`.

When `k` contains a finite field `k₀` with `q` elements, the roots of `X^q - X - a t⁻¹`, `a ∈ k₀ˣ`,
are the translates `u + c`, `c ∈ k₀`, of one of them, so the Galois group of `k((t))` acts
transitively on them by translations.

## Main statements

- `LaurentSeries.irreducible_X_pow_sub_X_sub_C_single`: `Xⁿ - X - b t⁻¹` is irreducible over
  `k((t))`.
- `LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single`: the Galois group of
  `k((t))` acts transitively on the roots `u + c`, `c ∈ k₀`, of `X^q - X - a t⁻¹`.
-/

@[expose] public section

open Polynomial IntermediateField

variable {k : Type*} [Field k]

/-- The polynomial `Yⁿ + c t (Yⁿ⁻¹ - 1)` over `k[[t]]`, for `c ≠ 0` and `n ≥ 2`, is Eisenstein at
the maximal ideal `(t)`. -/
private theorem isEisensteinAt_X_pow_add_C_mul_X_pow_sub_one {c : k} (hc : c ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) :
    IsEisensteinAt (R := PowerSeries k) (X ^ n + C (PowerSeries.C c * PowerSeries.X) *
      (X ^ (n - 1) - 1)) (Ideal.span {PowerSeries.X}) := by
  set a : PowerSeries k := PowerSeries.C c * PowerSeries.X
  have hdeg : (C a * (X ^ (n - 1) - 1) : (PowerSeries k)[X]).degree < n := by
    refine (degree_le_of_natDegree_le (n := n - 1) ?_).trans_lt ?_
    · compute_degree
    · exact_mod_cast (by omega : n - 1 < n)
  have hmon := monic_X_pow_add hdeg
  have hnat : (X ^ n + C a * (X ^ (n - 1) - 1) : (PowerSeries k)[X]).natDegree = n := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  refine ⟨?_, fun {i} hi ↦ ?_, ?_⟩
  · rw [hmon.leadingCoeff, Ideal.mem_span_singleton]
    exact PowerSeries.X_prime.not_dvd_one
  · rw [hnat] at hi
    rw [Ideal.mem_span_singleton]
    have : (X ^ n : (PowerSeries k)[X]).coeff i = 0 := by rw [coeff_X_pow]; simp; omega
    rw [coeff_add, this, zero_add, coeff_C_mul]
    exact Dvd.dvd.mul_right (dvd_mul_left _ _) _
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have : (X ^ n + C a * (X ^ (n - 1) - 1) : (PowerSeries k)[X]).coeff 0 = -a := by
      simp [coeff_X_pow, coeff_one, show 0 ≠ n by omega, show 0 ≠ n - 1 by omega]
    rw [this, dvd_neg, pow_two]
    rintro h
    have := (mul_dvd_mul_iff_right PowerSeries.X_prime.ne_zero).1 h
    exact PowerSeries.X_prime.not_dvd_one (this.trans ⟨PowerSeries.C c⁻¹, by
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]⟩)

namespace LaurentSeries

/-- For `n ≥ 2` and `b ≠ 0`, the polynomial `Xⁿ - X - b t⁻¹` is irreducible over `k((t))`. In
characteristic `p`, for `n` a power of `p`, this says that the Artin–Schreier extension
`uⁿ - u = b / t` of `k((t))` has degree `n`: it is the step "the cover is totally ramified" of
the blueprint lemma `lemma-unramified-at-infinity-no-linear-characters--1`, where `k` is
algebraically closed and `t = 1 / x` is the coordinate at infinity.

The proof inverts the variable: `u⁻¹` is a root of the Eisenstein polynomial
`Yⁿ + (t / b) (Yⁿ⁻¹ - 1)` over `k[[t]]`. -/
theorem irreducible_X_pow_sub_X_sub_C_single {n : ℕ} (hn : 2 ≤ n) {b : k} (hb : b ≠ 0) :
    Irreducible (X ^ n - X - C (HahnSeries.single (-1 : ℤ) b) : (LaurentSeries k)[X]) := by
  set K := LaurentSeries k
  set s : K := HahnSeries.single (-1 : ℤ) b
  set f : K[X] := X ^ n - X - C s
  set a : PowerSeries k := PowerSeries.C b⁻¹ * PowerSeries.X
  set P : (PowerSeries k)[X] := X ^ n + C a * (X ^ (n - 1) - 1)
  have hdeg : (C a * (X ^ (n - 1) - 1) : (PowerSeries k)[X]).degree < n := by
    refine (degree_le_of_natDegree_le (n := n - 1) ?_).trans_lt ?_
    · compute_degree
    · exact_mod_cast (by omega : n - 1 < n)
  have hPmon : P.Monic := monic_X_pow_add hdeg
  have hPnat : P.natDegree = n := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hPirr : Irreducible (P.map (algebraMap (PowerSeries k) K)) :=
    (hPmon.irreducible_iff_irreducible_map_fraction_map).1
      ((isEisensteinAt_X_pow_add_C_mul_X_pow_sub_one (inv_ne_zero hb) hn).irreducible
        (Ideal.span_singleton_prime PowerSeries.X_prime.ne_zero |>.2 PowerSeries.X_prime)
        hPmon.isPrimitive (by rw [hPnat]; omega))
  have hfmon : f.Monic := by
    unfold f
    rw [sub_sub]
    exact monic_X_pow_sub (by compute_degree; exact_mod_cast (by omega : 1 < n))
  have hfnat : f.natDegree = n := by
    unfold f
    rw [sub_sub, natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow]
    exact (natDegree_add_le _ _).trans_lt (by simp; omega)
  have has : algebraMap (PowerSeries k) K a * s = 1 := by
    simp [a, s, K, LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X,
      HahnSeries.ofPowerSeries_C, HahnSeries.C, HahnSeries.single_mul_single, hb]
  -- a root `u` of `f` in an algebraic closure
  let L := AlgebraicClosure K
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_aeval_eq_zero L f (by
    rw [degree_eq_natDegree hfmon.ne_zero, hfnat]; exact_mod_cast (by omega : n ≠ 0))
  have hu' : u ^ n - u - algebraMap K L s = 0 := by simpa [f] using hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    have : s = 0 := by simpa [zero_pow (by omega : n ≠ 0)] using hu'
    exact hb (by simpa [s] using congrArg (fun x ↦ x.coeff (-1)) this)
  -- `u⁻¹` is a root of the Eisenstein polynomial
  have hy : aeval u⁻¹ (P.map (algebraMap (PowerSeries k) K)) = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have has' : algebraMap K L (algebraMap (PowerSeries k) K a) * algebraMap K L s = 1 := by
      rw [← map_mul, has, map_one]
    simp only [P, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
      Polynomial.map_sub, Polynomial.map_one, aeval_add, aeval_mul, aeval_X_pow, aeval_C,
      aeval_sub, aeval_one, Nat.add_sub_cancel]
    set τ := algebraMap K L (algebraMap (PowerSeries k) K a)
    have h1 : u⁻¹ ^ (m + 1) * u ^ (m + 1) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hu0, one_pow]
    have h2 : u⁻¹ ^ (m + 1) * u = u⁻¹ ^ m := by
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
    linear_combination (-τ * u⁻¹ ^ (m + 1)) * hu' + τ * h1 - τ * h2 - u⁻¹ ^ (m + 1) * has'
  -- hence `[K(u) : K] = [K(u⁻¹) : K] = n`, and `f` is the minimal polynomial of `u`
  have hmin : P.map (algebraMap (PowerSeries k) K) = minpoly K u⁻¹ :=
    minpoly.eq_of_irreducible_of_monic hPirr hy (hPmon.map _)
  have hadj : K⟮u⁻¹⟯ = K⟮u⟯ := le_antisymm
    (adjoin_simple_le_iff.2 (inv_mem (mem_adjoin_simple_self K u)))
    (adjoin_simple_le_iff.2 (by
      have := inv_mem (mem_adjoin_simple_self K u⁻¹)
      rwa [inv_inv] at this))
  have hint : ∀ x : L, IsIntegral K x := fun x ↦ Algebra.IsIntegral.isIntegral x
  have hdegu : (minpoly K u).natDegree = n := by
    rw [← adjoin.finrank (hint u), ← hadj, adjoin.finrank (hint _), ← hmin,
      hPmon.natDegree_map, hPnat]
  rw [eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hint u)) hfmon (minpoly.dvd K u hu)
    (by rw [hdegu, hfnat])]
  exact minpoly.irreducible (hint u)

/-- *The Galois group of an Artin–Schreier extension acts by all translations.* Let `k₀` be a
finite field with `q` elements, `k` a field over `k₀`, `a ∈ k₀ˣ` and `L` an algebraic closure of
`K = k((t))`. If `u ∈ L` is a root of `X^q - X - a t⁻¹`, then for every `c ∈ k₀` some
`σ ∈ Gal(L/K)` maps `u` to `u + c`.

Indeed `u + c` is again a root, as `c^q = c`, and the polynomial is irreducible
(`LaurentSeries.irreducible_X_pow_sub_X_sub_C_single`), so `u` and `u + c` are conjugate.

For `k` an algebraic closure of `k₀` and `t = 1 / x` the coordinate at `∞ ∈ ℙ¹`, `Gal(L/K)` is
the inertia group at infinity, and `u^q - u = a / t` is the Artin–Schreier cover `u^q - u = a x`
defining `ℒ_{ψ(a x)}`. An element `σ` with `σ u = u + c` acts on the geometric generic stalk of
`ℒ_{ψ(a x)}` by `ψ(±c)`, so for nontrivial `ψ` inertia at infinity acts nontrivially: a
nonzero linear Artin–Schreier sheaf is ramified at infinity.
(blueprint: `lemma-unramified-at-infinity-no-linear-characters--1`) -/
theorem exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single {k₀ : Type*} [Field k₀] [Finite k₀]
    [Algebra k₀ k] {a : k₀} (ha : a ≠ 0) (L : Type*) [Field L] [Algebra (LaurentSeries k) L]
    [IsAlgClosure (LaurentSeries k) L] {u : L}
    (hu : u ^ Nat.card k₀ - u =
      algebraMap (LaurentSeries k) L (HahnSeries.single (-1) (algebraMap k₀ k a)))
    (c : k₀) :
    ∃ σ : L ≃ₐ[LaurentSeries k] L,
      σ u = u + algebraMap (LaurentSeries k) L (HahnSeries.C (algebraMap k₀ k c)) := by
  set K := LaurentSeries k
  have := Fintype.ofFinite k₀
  set ι : k₀ →+* L := (algebraMap K L).comp (HahnSeries.C.comp (algebraMap k₀ k))
  set q := Nat.card k₀
  have hq : 2 ≤ q := Finite.one_lt_card
  set s : K := HahnSeries.single (-1 : ℤ) (algebraMap k₀ k a)
  set f : K[X] := X ^ q - X - C s
  have hfirr : Irreducible f := irreducible_X_pow_sub_X_sub_C_single hq
    ((map_ne_zero_iff _ (algebraMap k₀ k).injective).2 ha)
  have hfmon : f.Monic := by
    unfold f
    rw [sub_sub]
    exact monic_X_pow_sub (by compute_degree; exact_mod_cast (by omega : 1 < q))
  -- `u + ι c` is again a root of `f`, as `c ^ q = c`
  obtain ⟨p, hp⟩ := CharP.exists k₀
  have : Fact p.Prime := ⟨CharP.char_is_prime k₀ p⟩
  have : CharP L p := charP_of_injective_ringHom ι.injective p
  obtain ⟨m, -, hm⟩ := FiniteField.card k₀ p
  have hqc : q = Fintype.card k₀ := Nat.card_eq_fintype_card
  have hroot : (u + ι c) ^ q - (u + ι c) = algebraMap K L s := by
    rw [hqc, hm, add_pow_char_pow, ← hm, ← map_pow, FiniteField.pow_card, ← hqc, ← hu]
    ring
  have hmin : ∀ x : L, x ^ q - x = algebraMap K L s → f = minpoly K x := fun x hx ↦
    minpoly.eq_of_irreducible_of_monic hfirr (by simp [f, hx]) hfmon
  exact (Normal.minpoly_eq_iff_mem_orbit L).1 ((hmin _ hroot).symm.trans (hmin _ hu))

/-- The Galois group of `k((t))` acts on the roots of `X^q - X - b t⁻¹`, `q = #k₀`, `b ≠ 0`, by
all translations by `k₀`; this is
`LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single` for `b ∈ kˣ` arbitrary. -/
theorem exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single_of_ne_zero {k₀ : Type*} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {b : k} (hb : b ≠ 0) (L : Type*) [Field L]
    [Algebra (LaurentSeries k) L] [IsAlgClosure (LaurentSeries k) L] {u : L}
    (hu : u ^ Nat.card k₀ - u = algebraMap (LaurentSeries k) L (HahnSeries.single (-1) b))
    (c : k₀) :
    ∃ σ : L ≃ₐ[LaurentSeries k] L,
      σ u = u + algebraMap (LaurentSeries k) L (HahnSeries.C (algebraMap k₀ k c)) := by
  set K := LaurentSeries k
  have := Fintype.ofFinite k₀
  set ι : k₀ →+* L := (algebraMap K L).comp (HahnSeries.C.comp (algebraMap k₀ k))
  set q := Nat.card k₀
  have hq : 2 ≤ q := Finite.one_lt_card
  set s : K := HahnSeries.single (-1 : ℤ) b
  set f : K[X] := X ^ q - X - C s
  have hfirr : Irreducible f := irreducible_X_pow_sub_X_sub_C_single hq hb
  have hfmon : f.Monic := by
    unfold f
    rw [sub_sub]
    exact monic_X_pow_sub (by compute_degree; exact_mod_cast (by omega : 1 < q))
  obtain ⟨p, hp⟩ := CharP.exists k₀
  have : Fact p.Prime := ⟨CharP.char_is_prime k₀ p⟩
  have : CharP L p := charP_of_injective_ringHom ι.injective p
  obtain ⟨m, -, hm⟩ := FiniteField.card k₀ p
  have hqc : q = Fintype.card k₀ := Nat.card_eq_fintype_card
  have hroot : (u + ι c) ^ q - (u + ι c) = algebraMap K L s := by
    rw [hqc, hm, add_pow_char_pow, ← hm, ← map_pow, FiniteField.pow_card, ← hqc, ← hu]
    ring
  have hmin : ∀ x : L, x ^ q - x = algebraMap K L s → f = minpoly K x := fun x hx ↦
    minpoly.eq_of_irreducible_of_monic hfirr (by simp [f, hx]) hfmon
  exact (Normal.minpoly_eq_iff_mem_orbit L).1 ((hmin _ hroot).symm.trans (hmin _ hu))

/-- The uniformizer `t` of `k((t))` is transcendental over `k`. -/
theorem transcendental_single_one : Transcendental k (HahnSeries.single (1 : ℤ) (1 : k)) := by
  rintro ⟨p, hp, h⟩
  refine hp (Polynomial.coe_injective (R := k)
    (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k) ?_))
  have hC : (HahnSeries.ofPowerSeries ℤ k).comp PowerSeries.C = algebraMap k (LaurentSeries k) :=
    RingHom.ext fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  rw [← Polynomial.eval₂_C_X_eq_coe, Polynomial.hom_eval₂, hC, HahnSeries.ofPowerSeries_X,
    ← Polynomial.aeval_def, h, Polynomial.coe_zero, map_zero]

/-- The coordinate `1 / t` of `k((t))` is transcendental over `k`. -/
theorem transcendental_single_neg_one :
    Transcendental k (HahnSeries.single (-1 : ℤ) (1 : k)) := by
  have h : HahnSeries.single (-1 : ℤ) (1 : k) = (HahnSeries.single (1 : ℤ) (1 : k))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by
      rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, HahnSeries.single_zero_one])
  rw [h, Transcendental, IsAlgebraic.inv_iff]
  exact transcendental_single_one

end LaurentSeries
