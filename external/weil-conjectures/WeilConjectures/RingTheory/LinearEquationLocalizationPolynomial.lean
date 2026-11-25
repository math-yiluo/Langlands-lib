/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.LinearEquationLocalizationPolynomialCore
import WeilConjectures.RingTheory.LinearEquationLocalizationPolynomialFormula

/-!
# Localizing a polynomial algebra with one linear relation

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 16.2.8, Tag 07EU,
`lemma-final-solve` (blueprint: lem-weil-pbc-linear-equation-localization-polynomial).
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- Source: Stacks Project, Tag 07EU, proof of `lemma-final-solve`, the omitted computation
showing that `B` localized at `f i` is smooth over `A` localized at `f i`.
(blueprint: lem-weil-pbc-linear-equation-localization-polynomial)

Proof (the four steps of the node, given here for the omitted detail):
1. By the localization universal property
   [lem-weil-pbc-localization-away-universal-property], the map `A → B → Bf` induces
   `Af → Bf`, mapping each fraction to the same fraction. Polynomial evaluation
   [def-weil-pbc-mv-polynomial-ring] gives the map sending `y j` to the class of `x j`.
2. Set `z = (f i)⁻¹ * (1 - ∑ j ≠ i, f j * y j)`. Evaluate the original polynomial
   ring by sending `x i` to `z` and the other variables to `y j`. The defining relation
   maps to zero, since `f i * (f i)⁻¹ = 1`, so evaluation factors through `B`.
   The image of `f i` is a unit, hence the same localization universal property extends
   this map to `Bf`. On fractions it sends `b / (f i)^n` to the image of `b` times
   `(f i)⁻ⁿ`; this also proves `Af`-linearity and the stated inverse formulas.
3. The inverse composed with polynomial evaluation fixes every `y j`, so it is the
   identity by `MvPolynomial.algHom_ext` [def-weil-pbc-mv-polynomial-ring].
4. In the other order the composite fixes `x j` for `j ≠ i`. It fixes `x i` because the
   relation in `B` gives `1 - ∑ j ≠ i, f j * x j = f i * x i`. Polynomial uniqueness,
   surjectivity of the quotient map, and uniqueness for localization then show that
   this composite too is the identity.

The binder `i : Fin r` encodes the choice of one of the `r ≥ 1` variables.
The local algebra instance is the induced map on localizations, not extra data. -/
theorem linearEquationLocalizationPolynomial (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) (i : Fin r) :
    let I : Ideal (MvPolynomial (Fin r) A) :=
      Ideal.span {(∑ j : Fin r, C (f j) * X j) - 1}
    let B := MvPolynomial (Fin r) A ⧸ I
    let q := Ideal.Quotient.mk I
    let Af := Localization.Away (f i)
    let Bf := Localization.Away (algebraMap A B (f i))
    letI : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra
    let x : Fin r → Bf := fun j ↦ algebraMap B Bf (q (X j))
    ∃ e : MvPolynomial {j : Fin r // j ≠ i} Af ≃ₐ[Af] Bf,
      e.toAlgHom = aeval (fun j ↦ x j.1) ∧
      (∀ j : {j : Fin r // j ≠ i}, e.symm (x j.1) = X j) ∧
      e.symm (x i) =
        C (IsLocalization.Away.invSelf (S := Af) (f i)) *
          (1 - ∑ j : {j : Fin r // j ≠ i},
            C (algebraMap A Af (f j.1)) * X j) := by
  dsimp
  obtain ⟨e, he, hf⟩ := linearEquationLocalizationPolynomialCore A r f i
  refine ⟨e, he, hf, ?_⟩
  exact linearEquationLocalizationPolynomialFormula A r f i e he hf

end MvPolynomial
