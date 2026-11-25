/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Idempotents
import WeilConjectures.RingTheory.FiniteGabberSectionModel
import WeilConjectures.RingTheory.FiniteIdempotentFactorTransfer
import WeilConjectures.RingTheory.FiniteGabberPolynomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring

/-!
# Integral section factor from Gabber roots

Source: Stacks Project, Tag 09XI, proof of (5) implies (2), integral factor construction.
The finite-model lemma isolates the construction before any root is chosen; the
idempotent and its section extension are constructed in this file.
-/

@[expose] public section

universe u v

open Polynomial
open scoped BigOperators

namespace Algebra

/-- Gabber's root condition constructs an integral idempotent factor of an étale algebra,
with the prescribed section on the closed fibre. This stops before identifying that factor
with the base ring.

Source: Stacks Project, Tag 09XI, proof of (5) ⇒ (2), construction of the integral factor
(https://stacks.math.columbia.edu/tag/09XI).
(blueprint: lem-weil-pbc-gabber-root-criterion-integral-section-factor)

Proof:
1. Factor σ through B/IB. Étale base change and the étale-section idempotent splitting
produce an idempotent ε whose localization is A/I, with σ the first projection.
2. Apply the integral-closure finite-fibre localization theorem (09XH) to this finite
factor. It gives ε' in B'/IB', where B' is the integral closure, and a lift b with
B'_b ≅ B_b, compatibly with ε and the chosen section.
3. Choose finitely many numerators generating B'_b over A and finitely many elements
expressing b²-b in IB'. The subalgebra B'' they generate together with b is finite
because all its generators are integral. Then B''_b ≅ B'_b; the image of b in B''/IB''
is idempotent, and its first factor is A/I, since quotient commutes with localization.
4. The finite Gabber polynomial theorem (0EM0) gives a monic f annihilating b, of form
X^n(X-1) plus I-coefficients, with n ≥ 1. Choose the root α in 1+I using hroots.
Write f = (X-α)g. Modulo I, g = X^n, so g(α) and α lie in 1+I and are units.
Put E = g(α)⁻¹g. Since g(X)-g(α) is divisible by X-α, f divides E²-E and
(X-α)E. Thus d = E(b) in B' is idempotent and bd = αd. Modulo I, d is ε',
because E reduces to X^n and ε' is idempotent with n ≥ 1.
5. Let e be the image of d in B. On the d-factor, b equals the unit α, so the
isomorphism B'_b ≅ B_b restricts to B'_d ≅ B_e. Localization at an idempotent is
a quotient; therefore B'_d, and hence B_e, is integral over A.
6. The reduction of e is ε, so B_e/IB_e ≅ (B/IB)_ε ≅ A/I compatibly with the
structure map. This proves bijectivity of the quotient map in the conclusion.
Since σ(e)=1, σ extends uniquely over B_e by localization, giving ρ with the
stated equality on every x. No isomorphism A ≅ B_e is used in this construction. -/
theorem exists_gabber_integral_section_factor
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (hroots : ∀ (n : ℕ), 1 ≤ n → ∀ (a : Fin (n + 1) → A),
      (∀ j, a j ∈ I) → ∀ (f : A[X]), f.Monic →
        f = X ^ n * (X - 1) + ∑ j : Fin (n + 1), C (a j) * X ^ (j : ℕ) →
          ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α)
    (B : Type v) [CommRing B] [Algebra A B] [Etale A B] (σ : B →ₐ[A] A ⧸ I) :
    ∃ e : B, IsIdempotentElem e ∧
      (algebraMap A (Localization.Away e)).IsIntegral ∧
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap A (Localization.Away e)) I)
          (algebraMap A (Localization.Away e)) Ideal.le_comap_map) ∧
      ∃ ρ : Localization.Away e →ₐ[A] A ⧸ I,
        ∀ x : B, ρ (algebraMap B (Localization.Away e) x) = σ x := by
  classical
  obtain ⟨D, hD, C, hC, hAC, Φ, b, hΦ, hb, hσ, hloc⟩ :=
    exists_finite_gabber_section_model A I B σ
  let := hD
  let := hC
  let := hAC
  obtain ⟨n, a, f, hn, ha, hf, hzero, hform⟩ :=
    exists_monic_aeval_eq_zero_gabber_polynomial I hI (A ⧸ I) C Φ hΦ
      (fun x ↦ ⟨x, rfl⟩) b hb
  obtain ⟨α, hαI, hroot⟩ := hroots n hn a ha f hf hform
  have hα : IsUnit α := Ideal.isUnit_of_sub_one_mem_jacobson_bot α (hI hαI)
  let q := Ideal.Quotient.mk I
  let J := I.map (algebraMap A D)
  let π := Ideal.Quotient.mk J
  have hαbar : q α = 1 := (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr hαI
  have hcoeff : ∀ j, q (a j) = 0 := fun j ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (ha j)
  have hfbar : f.map q = X ^ n * (X - 1) := by
    rw [hform]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X,
      Polynomial.map_sub, Polynomial.map_one]
    rw [show Polynomial.map q (∑ j, Polynomial.C (a j) * X ^ (j : ℕ)) = 0 from ?_]
    · rw [add_zero]
    · change (Polynomial.mapRingHom q) _ = 0
      simp [hcoeff]
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr hroot
  have hgbar : g.map q = X ^ n := by
    apply (monic_X_sub_C (1 : A ⧸ I)).isRegular.left
    calc
      (X - Polynomial.C 1) * g.map q = f.map q := by
        rw [hg, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, hαbar]
      _ = (X - Polynomial.C 1) * X ^ n := by simpa [mul_comm] using hfbar
  have hgeval : q (g.eval α) = 1 := by
    rw [← eval_map_apply, hgbar, eval_pow, eval_X, hαbar, one_pow]
  have hgevalI : g.eval α - 1 ∈ I :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp hgeval
  obtain ⟨v, hv⟩ := Ideal.isUnit_of_sub_one_mem_jacobson_bot (g.eval α) (hI hgevalI)
  let u : A := ↑v⁻¹
  have hu : u * g.eval α = 1 := by
    rw [← hv]
    simp [u]
  have hubar : q u = 1 := by
    have h := congrArg q hu
    simpa [hgeval] using h
  obtain ⟨r, hr⟩ := X_sub_C_dvd_sub_C_eval (p := g) (a := α)
  have hbg : (b - algebraMap A D α) * aeval b g = 0 := by
    have h := congrArg (aeval b) hg
    simpa [hzero] using h.symm
  have hgr : aeval b g - algebraMap A D (g.eval α) =
      (b - algebraMap A D α) * aeval b r := by
    simpa using congrArg (aeval b) hr
  let d : D := algebraMap A D u * aeval b g
  have huD : algebraMap A D u * algebraMap A D (g.eval α) = 1 := by
    rw [← map_mul, hu, map_one]
  have hdminus : d - 1 =
      algebraMap A D u * (b - algebraMap A D α) * aeval b r := by
    calc
      d - 1 = algebraMap A D u *
          (aeval b g - algebraMap A D (g.eval α)) := by rw [mul_sub, huD]
      _ = _ := by rw [hgr]; ring
  have hdzero : d * (d - 1) = 0 := by
    rw [hdminus]
    calc
      d * (algebraMap A D u * (b - algebraMap A D α) * aeval b r) =
          (algebraMap A D u) ^ 2 * aeval b r *
            ((b - algebraMap A D α) * aeval b g) := by dsimp [d]; ring
      _ = 0 := by rw [hbg, mul_zero]
  have hd : IsIdempotentElem d := by
    change d * d = d
    exact sub_eq_zero.mp (by simpa only [mul_sub, mul_one] using hdzero)
  have hbd : b * d = algebraMap A D α * d := by
    apply sub_eq_zero.mp
    calc
      b * d - algebraMap A D α * d =
          algebraMap A D u * ((b - algebraMap A D α) * aeval b g) := by
        dsimp [d]; ring
      _ = 0 := by rw [hbg, mul_zero]
  have hbidem : IsIdempotentElem (π b) := by
    change π b * π b = π b
    apply Φ.injective
    simp only [map_mul]
    dsimp [π, J]
    rw [hb]
    simp
  let Q := Ideal.quotientMap J (algebraMap A D) Ideal.le_comap_map
  have hmapg : g.map (π.comp (algebraMap A D)) = X ^ n := by
    calc
      _ = (g.map q).map Q := by
        rw [Polynomial.map_map]
        congr 1
      _ = X ^ n := by rw [hgbar]; simp
  have hπg : π (aeval b g) = π b := by
    calc
      π (aeval b g) = π ((g.map (algebraMap A D)).eval b) := by
        rw [eval_map, aeval_def]
      _ = ((g.map (algebraMap A D)).map π).eval (π b) :=
        (eval_map_apply π b).symm
      _ = (π b) ^ n := by rw [Polynomial.map_map, hmapg]; simp
      _ = π b := hbidem.pow_eq (by omega)
  have hπu : π (algebraMap A D u) = 1 := by
    change Q (q u) = 1
    rw [hubar, map_one]
  have hπd : π d = π b := by
    dsimp [d]
    rw [map_mul, hπu, one_mul, hπg]
  have hΦd : Φ (π d) = (1, 0) := hπd ▸ hb
  obtain ⟨hint, hbij⟩ :=
    finite_idempotent_factor_transfer I D C Φ hΦ b d hd α hα hbd hloc hΦd
  have hσd : σ d.1 = 1 := by rw [← hσ d, hΦd]
  refine ⟨d.1, ?_, hint, hbij, ?_⟩
  · exact congrArg (fun x : D ↦ x.1) hd
  · refine ⟨IsLocalization.Away.liftAlgHom (S := Localization.Away d.1) d.1
      (hσd.symm ▸ isUnit_one), ?_⟩
    intro x
    exact IsLocalization.Away.lift_eq (g := σ.toRingHom) d.1
      (hσd.symm ▸ isUnit_one) x

end Algebra
