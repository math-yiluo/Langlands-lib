/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Dimension of a localized polynomial ring at a maximal ideal

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00OP
(lemma-dim-affine-space, line 27660) (blueprint:
lem-weil-pbc-polynomial-ring-maximal-localization-dimension).
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- Induction on the variables, using the polynomial height step over a Jacobson ring. -/
private theorem height_maximal_eq_numVariables {k : Type u} [Field k] (n : ℕ)
    (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal] : M.height = n := by
  induction n with
  | zero =>
    have h := M.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
    have hd : ringKrullDim (MvPolynomial (Fin 0) k) = 0 := by
      simp only [ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_fin, Nat.cast_zero, add_zero]
      exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
    rw [hd] at h
    simpa using h
  | succ n ih =>
    let e := (finSuccEquiv k n).toRingEquiv
    let P := M.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p := P.comap Polynomial.C
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver p := ⟨rfl⟩
    rw [← e.height_map M, Polynomial.height_eq_height_add_one p P, ih p]
    simp

/--
For a field `k`, the localization of `k[X₁, …, Xₙ]` at any maximal ideal has
Krull dimension `n`.
Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00OP
(lemma-dim-affine-space).
(blueprint: lem-weil-pbc-polynomial-ring-maximal-localization-dimension).

Proof by induction on the number of variables, using Mathlib's polynomial height theorem:
1. For zero variables the polynomial ring has dimension zero, since `k` is a field.
   The height of a maximal ideal is at most that dimension, hence is zero.
2. Identify the polynomial ring in `n + 1` variables with `(MvPolynomial (Fin n) k)[T]`
   using `finSuccEquiv`. Transport the maximal ideal through this ring equivalence;
   `RingEquiv.height_map` preserves its height.
3. The coefficient ring is Noetherian and Jacobson. By
   `Polynomial.isMaximal_comap_C_of_isJacobsonRing`, the contraction of the transported
   ideal is maximal. Apply the induction hypothesis to this contraction and then
   `Polynomial.height_eq_height_add_one` to obtain height `n + 1`.
4. Finally `IsLocalization.AtPrime.ringKrullDim_eq_height` identifies the dimension of
   the localization with the height just computed.

The height and contraction lemmas are in Mathlib.RingTheory.KrullDimension.Polynomial
and Mathlib.RingTheory.Jacobson.Ring, respectively. This avoids the explicit construction
of generators and prime chains in the source's proof of Tag 00OP.
-/
theorem ringKrullDim_localizationAtMaximal {k : Type u} [Field k] (n : ℕ)
    (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal] :
    ringKrullDim (Localization.AtPrime M) = (n : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M),
    height_maximal_eq_numVariables n M]
  rfl

end MvPolynomial
