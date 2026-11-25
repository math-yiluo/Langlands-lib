/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.PopescuWeakClearCore
import WeilConjectures.RingTheory.PopescuWeakClearRelations

/-!
# Clearing a local standard smooth presentation

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07F9,
`lemma-delocalize-weak`, the denominator-clearing paragraphs.
(blueprint: lem-weil-pbc-popescu-weak-clear-presentation)
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial

/-- Clear the coefficients and ideal-membership certificates of a submersive
presentation over `Rₚ`. This statement concerns only the base localization and its
polynomial presentation; it constructs neither a global factorization nor a singular ideal.
Source: Stacks Project, proof of Tag 07F9 (`lemma-delocalize-weak`), lines 2179–2188.
(blueprint: lem-weil-pbc-popescu-weak-clear-presentation)

Proof: View the polynomial ring over `Rₚ` as the localization of the polynomial
ring over `R` at the coefficient images of `R \ p`. Clear the finitely many
coefficients of each relation of `P`, obtaining `fⱼ` whose coefficient extension
is a scalar unit times the old relation. These generate the same localized ideal,
and their Jacobian determinant is the old one multiplied by the product of those
units, since the scalars have zero partial derivatives. Its image in `D` is a unit.
Lift an inverse to the localized polynomial ring and express `1` as its product
with the determinant plus a finite linear combination of the relations. Clear
all coefficients of this identity and kill its residual localization kernel by
one further scalar outside `p`. This gives `s₀ - h*det ∈ (f)`.
For each `gⱼ`, its vanishing in `D` puts its coefficient extension in the ideal
of the localized relations. Clear the coefficients in this finite ideal-membership
certificate and again kill the residual kernel by a scalar outside `p`, giving
`sⱼ₊₁*gⱼ ∈ (f)`. Products of the clearing scalars remain outside the prime.
The equations `fⱼ` still vanish on `P.val`, since they are scalar multiples of the
old relations. Empty relation families use the empty determinant `1`; all clearing
products of empty families are `1`. -/
theorem exists_cleared_submersive_presentation
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {D : Type v} [CommRing D] [Algebra (Localization.AtPrime p) D]
    [Algebra R D] [IsScalarTower R (Localization.AtPrime p) D]
    (n m c t : ℕ) (hc : c ≤ n + m)
    (P : SubmersivePresentation (Localization.AtPrime p) D (Fin (n + m)) (Fin c))
    (hmap : P.map = Fin.castLE hc)
    (g : Fin t → MvPolynomial (Fin n) R)
    (hg : ∀ j, aeval (fun i : Fin n ↦ P.val (Fin.castAdd m i)) (g j) = 0) :
    ∃ (f : Fin c → MvPolynomial (Fin (n + m)) R)
      (s : Fin (t + 1) → R) (h : MvPolynomial (Fin (n + m)) R),
      (∀ j, s j ∉ p) ∧
      (MvPolynomial.C (s 0) - h * Matrix.det
        (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j)) ∈
          Ideal.span (Set.range f)) ∧
      (∀ j : Fin t, MvPolynomial.C (s j.succ) *
        rename (Fin.castLE (Nat.le_add_right n m)) (g j) ∈ Ideal.span (Set.range f)) ∧
      (∀ j, aeval P.val (f j) = 0) := by
  classical
  obtain ⟨f, s0, h, hs0, hdet, hf, hkernel⟩ :=
    exists_cleared_submersive_presentation_core p n m c hc P hmap
  obtain ⟨sr, hsr, hgr⟩ :=
    exists_cleared_submersive_relations p n m c t P f hkernel g hg
  let s : Fin (t + 1) → R := Fin.cases s0 (fun j ↦ sr j)
  refine ⟨f, s, h, ?_, hdet, ?_, hf⟩
  · intro j
    exact Fin.cases hs0 (fun j ↦ hsr j) j
  · intro j
    exact hgr j

end Algebra
