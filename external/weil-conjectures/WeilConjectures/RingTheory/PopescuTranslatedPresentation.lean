/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
import WeilConjectures.RingTheory.PopescuTranslatedPresentationData
import WeilConjectures.RingTheory.PopescuTranslatedPresentationProperties

/-! # Translation of a strictly standard presentation

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR (lemma-desingularize),
from the choice of presentation through the constant Jacobian minor identity.
(blueprint: lem-weil-pbc-popescu-translated-presentation).
-/

@[expose] public section

universe u v w

namespace Algebra

open MvPolynomial

/-- Translate a strictly standard presentation so that its generators vanish under the
section modulo `π⁴`, and lift the resulting constant Jacobian minor identity to `R`.

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR (lemma-desingularize),
choice of presentation, replacement of `xᵢ` by `xᵢ-rᵢ`, and identity for `uπ`.
(blueprint: lem-weil-pbc-popescu-translated-presentation).

Proof: choose the finite presentation and initial relations from strict standardness.
Lift the section's value on every generator to `R`, and translate the polynomial ring
by these lifts. The translation is an automorphism, with inverse the opposite
translation; transport the presentation and its chosen lift along this automorphism.
Partial derivatives commute with translation, as follows by polynomial induction from
Leibniz and the identities on constants and variables. Thus the Jacobian minor identity
and the ideal-square condition persist. The composite of the new presentation map and
the section kills every variable, hence is constant evaluation modulo `π⁴`. Every
relation has constant coefficient `π⁴aⱼ`. Compatibility with `α` gives
`α(P.val i)=π⁴λᵢ`. Apply the section to the minor identity, lift the finitely many
coefficients, and use the kernel of `R→R/(π⁴)` to write the error as `π⁴t`. Consequently
`(1-π³t)π` is a linear combination of the constant minors. The transpose convention
below leaves determinants unchanged. No inverse matrix, substituted polynomials, or
smoothness assertion is constructed in this step. -/
theorem exists_popescu_translated_presentation
    (R : Type u) (Λ : Type v) (A : Type w)
    [CommRing R] [CommRing Λ] [CommRing A]
    [Algebra R Λ] [Algebra R A] [FinitePresentation R A]
    (π : R) (α : A →ₐ[R] Λ)
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π))
    (hρ : ∃ ρ :
      (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (R ⧸ Ideal.span {π ^ 4}),
      ∀ (a : A) (r : R),
        ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ r →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (algebraMap R Λ r)) :
    ∃ (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m)) (hc : c ≤ min n m)
      (lam : Fin n → Λ) (a : Fin m → R) (t : R),
      (∀ i, α (P.val i) = algebraMap R Λ π ^ 4 * lam i) ∧
      (∀ j, constantCoeff (P.relation j) = π ^ 4 * a j) ∧
      (1 - π ^ 3 * t) * π ∈ Ideal.span (Set.range
        (fun I : {I : Finset (Fin n) // I.card = c} ↦
          (Matrix.submatrix
            (fun i j ↦ constantCoeff
              (pderiv i (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j))))
            (I.val.orderEmbOfFin I.property) (fun j ↦ j)).det)) ∧
      (∀ j : Fin m, c ≤ j.val →
        P.σ (algebraMap R A π) * P.relation j ∈
          Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
            (Ideal.span (Set.range P.relation)) ^ 2) := by
  classical
  obtain ⟨ρ, hcompat⟩ := hρ
  obtain ⟨n, m, c, P, hc, b, hzero, hminor, hsq⟩ :=
    exists_popescu_translated_presentation_data R A π ρ hstandard
  have hgen (i : Fin n) : ∃ l : Λ, α (P.val i) = algebraMap R Λ π ^ 4 * l := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_zero] using hcompat (P.val i) 0 (by simpa using hzero i)
  choose lam hgen using hgen
  obtain ⟨a, t, hconst, hminor⟩ :=
    exists_popescu_translated_presentation_properties R A π ρ n m c P hc b hzero hminor
  exact ⟨n, m, c, P, hc, lam, a, t, hgen, hconst, hminor, hsq⟩

end Algebra
