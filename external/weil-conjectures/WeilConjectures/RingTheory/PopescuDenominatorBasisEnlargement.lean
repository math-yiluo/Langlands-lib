/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.PopescuUnscaledUnitBasis
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas

/-!
# Differential basis enlargement after clearing denominators

Source: Stacks Project, proofs of Tags 07FH and 07FI; the denominator and differential
argument in steps 5–14 of lem-weil-pbc-popescu-quotient-basis-enlargement.
-/

@[expose] public section

set_option autoImplicit false
universe u v

namespace Algebra

/-- Frobenius turns a multiplicative inverse modulo nilpotents into an actual power
in the subring. The returned element is a p-th power of a unit. -/
private theorem capture_unit_power
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : ℕ) [CharP S p] [Fact p.Prime]
    (x : S) (Q : ℕ) (hQ : 1 ≤ Q) (z : Rˣ)
    (hz : IsNilpotent (f (z : R) * x ^ Q - 1)) :
    ∃ (N : ℕ) (_ : 1 ≤ N) (d : Rˣ), f ((d : R) ^ p) = x ^ N := by
  obtain ⟨r, hr⟩ := hz
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpow : r ≤ p ^ (r + 1) :=
    (Nat.le_succ r).trans (Nat.lt_pow_self hp).le
  have hzero : (f (z : R) * x ^ Q - 1) ^ (p ^ (r + 1)) = 0 :=
    pow_eq_zero_of_le hpow hr
  have hone : f (z : R) ^ (p ^ (r + 1)) * x ^ (Q * p ^ (r + 1)) = 1 := by
    have h := sub_pow_char_pow (f (z : R) * x ^ Q) 1 (p := p) (r + 1)
    rw [hzero, one_pow, mul_pow, ← pow_mul] at h
    exact (sub_eq_zero.mp h.symm)
  refine ⟨Q * p ^ (r + 1), Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hQ) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)),
    z⁻¹ ^ (p ^ r), ?_⟩
  have hinv : f ((z⁻¹ : Rˣ) : R) * f (z : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hcancel : f ((z⁻¹ : Rˣ) : R) ^ (p ^ (r + 1)) *
      f (z : R) ^ (p ^ (r + 1)) = 1 := by
    rw [← mul_pow, hinv, one_pow]
  calc
    f (((z⁻¹ ^ (p ^ r) : Rˣ) : R) ^ p) =
        f ((z⁻¹ : Rˣ) : R) ^ (p ^ (r + 1)) := by
      simp only [Units.val_pow_eq_pow_val, map_pow, ← pow_mul, pow_succ]
    _ = f ((z⁻¹ : Rˣ) : R) ^ (p ^ (r + 1)) *
        (f (z : R) ^ (p ^ (r + 1)) * x ^ (Q * p ^ (r + 1))) := by rw [hone, mul_one]
    _ = x ^ (Q * p ^ (r + 1)) := by rw [← mul_assoc, hcancel, one_mul]

/-- Given a residue differential basis whose lifts have a common denominator, enlarge the
admissible subalgebra so that it captures a positive power of that denominator and has a
residue differential basis lifted from the original ring. No ideal generators are chosen.
Source: Stacks Project, proofs of Tags 07FH and 07FI, and steps 5–14 of
lem-weil-pbc-popescu-quotient-basis-enlargement.
(blueprint: lem-weil-pbc-popescu-denominator-basis-enlargement).

Proof: Apply `exists_popescu_unscaled_unit_basis` to obtain an admissible A
containing A₀, a positive Q and a unit z of A such that z π(s)^Q - 1 is nilpotent,
and an unscaled residue differential basis. The basis has the original residue
differentials on its left summand and lifts of π(s) on its right summand.

For ε = z π(s)^Q - 1 choose r with ε^r = 0. Since p is prime, r ≤ p^(r+1).
Frobenius gives z^(p^(r+1)) π(s)^(Q p^(r+1)) = 1. Set N = Q p^(r+1) ≥ 1 and
c = (z⁻¹^(p^r))^p in A. Cancellation proves c = π(s)^N in the ambient ring.
This explicit c is a p-th power of a unit, so its residue γ is a nonzero unit and
dγ = 0. This Frobenius argument is proved in `capture_unit_power`.

For every original index j take a_j = inclusion(a₀ j) c and xs_j = μ_j s^(N-1).
The common-denominator equations and N ≥ 1 prove a_j = π(xs_j). The Leibniz rule
and dγ = 0 give d(residue a_j) = γ d(residue inclusion(a₀ j)). Scale the left
basis vectors by γ and leave the right basis vectors unchanged, using
`Module.Basis.isUnitSMul`. On the right use the supplied lifts of π(s) and take
xs_j = s. Reindex the resulting sum-indexed basis with `finSumFinEquiv`.
The construction permits either summand to be empty and also works for N = 1. -/
theorem exists_popescu_denominator_basis_enlargement
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (q : Ideal Λ) [q.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (A₀ : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))))
    (t₀ : ℕ) (a₀ : Fin t₀ → A₀)
    (b₀ : Module.Basis (Fin t₀) (IsLocalRing.ResidueField A₀)
      (KaehlerDifferential k (IsLocalRing.ResidueField A₀)))
    (hb₀ : ∀ j, b₀ j = KaehlerDifferential.D k (IsLocalRing.ResidueField A₀)
      (IsLocalRing.residue A₀ (a₀ j)))
    (s : Λ) (hs : s ∉ q) (μ : Fin t₀ → Λ)
    (hμ : ∀ j,
      Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
        (algebraMap Λ (Localization.AtPrime q) (μ j)) =
      (a₀ j : Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) *
        Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
          (algebraMap Λ (Localization.AtPrime q) s)) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A₀ ≤ A ∧
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      ∃ (N : ℕ) (_ : 1 ≤ N) (c : A),
        (c : Localization.AtPrime q ⧸
          (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
            (algebraMap Λ (Localization.AtPrime q) s)) ^ N ∧
        ∃ (t : ℕ) (xs : Fin t → Λ) (a : Fin t → A),
          (∀ j, (a j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (xs j))) ∧
          ∃ b : Module.Basis (Fin t) (IsLocalRing.ResidueField A)
              (KaehlerDifferential k (IsLocalRing.ResidueField A)),
            ∀ j, b j = KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (a j)) := by
  classical
  obtain ⟨A, hlocal, hle, hA, Q, hQ, z, hz, m, y, hy, b, hbL, hbR⟩ :=
    exists_popescu_unscaled_unit_basis k Λ p hp q n hn A₀ hA₀ t₀ a₀ b₀ hb₀ s hs
  let B := Localization.AtPrime q ⧸
    (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n
  let π : Λ →+* B :=
    (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)).comp
      (algebraMap Λ (Localization.AtPrime q))
  have : Nontrivial B :=
    (show Function.Injective (A.val : A → B) from Subtype.val_injective).nontrivial
  have : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero k hp.ne'⟩
  have : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
  have : CharP (IsLocalRing.ResidueField A) p :=
    charP_of_injective_algebraMap (algebraMap k (IsLocalRing.ResidueField A)).injective p
  obtain ⟨N, hN, d, hc⟩ := capture_unit_power A.val.toRingHom p (π s) Q hQ z hz
  let c : A := (d : A) ^ p
  have hcu : IsUnit c := (d.isUnit).pow p
  have hDc : KaehlerDifferential.D k (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A c) = 0 := by
    simp only [c, map_pow, Derivation.leibniz_pow,
      ← Nat.cast_smul_eq_nsmul (IsLocalRing.ResidueField A),
      CharP.cast_eq_zero (IsLocalRing.ResidueField A) p, zero_smul]
  let aL : Fin t₀ → A := fun j => Subalgebra.inclusion hle (a₀ j) * c
  have haL (j : Fin t₀) : (aL j : B) = π (μ j * s ^ (N - 1)) := by
    change (a₀ j : B) * (c : B) = _
    have hμ' : π (μ j) = (a₀ j : B) * π s := hμ j
    have hc' : (c : B) = π s ^ N := hc
    rw [hc', map_mul, map_pow, hμ']
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hN]
  let xs' : Fin t₀ ⊕ Fin m → Λ := Sum.elim (fun j => μ j * s ^ (N - 1)) (fun _ => s)
  let a' : Fin t₀ ⊕ Fin m → A := Sum.elim aL y
  have ha' (j : Fin t₀ ⊕ Fin m) : (a' j : B) = π (xs' j) := by
    cases j with
    | inl j => exact haL j
    | inr j => exact hy j
  let γ := IsLocalRing.residue A c
  have hγ : IsUnit γ := hcu.map (IsLocalRing.residue A)
  let w : Fin t₀ ⊕ Fin m → IsLocalRing.ResidueField A :=
    Sum.elim (fun _ => γ) (fun _ => 1)
  have hw (j : Fin t₀ ⊕ Fin m) : IsUnit (w j) := by
    cases j with
    | inl j => exact hγ
    | inr j => exact isUnit_one
  let b' := b.isUnitSMul hw
  have hb' (j : Fin t₀ ⊕ Fin m) : b' j =
      KaehlerDifferential.D k (IsLocalRing.ResidueField A) (IsLocalRing.residue A (a' j)) := by
    rw [Module.Basis.isUnitSMul_apply]
    cases j with
    | inl j =>
      rw [hbL]
      simp only [a', Sum.elim_inl, aL, map_mul, Derivation.leibniz, hDc,
        smul_zero]
      rfl
    | inr j =>
      simp only [w, Sum.elim_inr, one_smul, a']
      exact hbR j
  let e : Fin t₀ ⊕ Fin m ≃ Fin (t₀ + m) := finSumFinEquiv
  refine ⟨A, hlocal, hle, hA, N, hN, c, hc, t₀ + m,
    xs' ∘ e.symm, a' ∘ e.symm, ?_, b'.reindex e, ?_⟩
  · intro j
    exact ha' (e.symm j)
  · intro j
    simpa only [Module.Basis.reindex_apply, Function.comp_apply] using hb' (e.symm j)

end Algebra
