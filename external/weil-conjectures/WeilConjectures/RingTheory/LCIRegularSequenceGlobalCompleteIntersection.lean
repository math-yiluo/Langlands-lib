/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.LocalCompleteIntersectionPresentation
import WeilConjectures.RingTheory.RegularSequenceDimensionAtPoint
import WeilConjectures.RingTheory.PrincipalNeighborhoodDimension

/-!
# Local regular sequences give global complete intersections

Source: literature/stacks-project/algebra.tex, Algebra, Lemma 00SC
(blueprint: lem-weil-pbc-lci-regular-sequence-global-complete-intersection).
-/

@[expose] public section

universe u

namespace Algebra

/-- (blueprint: lem-weil-pbc-lci-regular-sequence-global-complete-intersection)
Let `P = k[x₁, ..., xₙ]`, `S = P/I`, and let `q` be a prime of `S`.
If the extension of `I` to `P` localized at the inverse image of `q` is generated
by a regular sequence, then some principal localization of `S` is a global
complete intersection over `k`. This is Lemma 00SC of the Stacks Project,
implication (5) => (1). Proof outline (following the node proof steps): localize
at the inverse image prime and identify the quotient with `S_q`; dimension theory
for a regular sequence gives `e = ht(q') - ht(q)` and local dimension `n - e`.
Clear denominators to obtain generators in `I`, then choose elements away from
the prime so that one principal open has dimension `n - e`. Adjoining an inverse
variable presents that localization as a quotient of a polynomial ring in `n + 1`
variables by `e + 1` equations; its dimension is `(n + 1) - (e + 1)`, so the
definition of global complete intersection applies. (blueprint:
lem-weil-pbc-lci-regular-sequence-global-complete-intersection)
-/
theorem exists_globalCompleteIntersection_of_regularSequence
    (k : Type u) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Ideal (MvPolynomial (Fin n) k ⧸ I)) (hq : q.IsPrime)
    (e : ℕ) (h : Fin e → Localization.AtPrime (q.comap
      (Ideal.Quotient.mk I)))
    (hreg : RingTheory.Sequence.IsRegular
      (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))) (List.ofFn h))
    (hgen : Ideal.map
      (algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))) I =
      Ideal.span (Set.range h)) :
    ∃ g : (MvPolynomial (Fin n) k ⧸ I),
      g ∉ q ∧ Algebra.IsGlobalCompleteIntersection k
        (Localization.Away g) := by
  obtain ⟨he, hdimAt⟩ := regularSequence_dimensionAtPoint k n I q hq e h hreg hgen
  obtain ⟨a, ha, hpres⟩ :=
    exists_principal_localization_presentation_of_local_generators k n I q hq e h hgen
  obtain ⟨b, hb, hdim⟩ :=
    PrimeSpectrum.exists_mul_away_dimension_eq _ ⟨q, hq⟩ a ha
  obtain ⟨f, hf⟩ := hpres b
  refine ⟨a * b, (hq.mul_notMem ha hb), Or.inr ?_⟩
  refine ⟨n + 1, e + 1, f, Nat.add_le_add_right he 1, hf, ?_⟩
  simpa only [hdimAt, Nat.add_sub_add_right] using hdim

end Algebra
