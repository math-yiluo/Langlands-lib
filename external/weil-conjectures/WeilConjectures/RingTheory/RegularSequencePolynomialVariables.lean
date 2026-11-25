/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.OfFn
import WeilConjectures.RingTheory.RegularSequencePermutationsSubsequences
import WeilConjectures.RingTheory.RegularSequenceSubsequencesPolynomial

/-!
# Regular sequences multiplied by polynomial variables

Source: Stacks Project, Algebra, Lemma 10.68.10, Tag 07DW
(blueprint: lem-weil-pbc-regular-sequence-polynomial-variables).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- Source: Stacks Project, Algebra, Lemma 10.68.10, Tag 07DW
(blueprint: lem-weil-pbc-regular-sequence-polynomial-variables).
For a finite family generating a proper ideal, regularity of all permutations, regularity of
all order-preserving subsequences, and regularity after multiplying by distinct polynomial
variables are equivalent. `List.ofFn f` lists the family in increasing index order.

Proof: The proper-ideal hypothesis makes every subfamily ideal proper and the ring nonzero.
(1) implies (2): put the selected subsequence first in a permutation and take its initial
segment; both the injectivity and the nonzero-quotient conditions persist.
(2) implies (1): induct on the length. For a permutation whose last index is s, induction
makes its first r-1 terms regular. If s is the original last index, the full sequence supplies
the last nonzerodivisor condition. Otherwise pass to the quotient by all original terms
before the last one except f_s. Induction makes f_s a nonzerodivisor there, the full sequence
makes the original last term regular modulo f_s, and the subsequence omitting f_s makes that
last term a nonzerodivisor there. Apply lem-weil-pbc-regular-sequence-swap-two in this quotient:
the reversed pair is regular, giving the required last condition modulo all terms except f_s.

For (2) and (3), put J_i = (f_j X_j : j < i). By
lem-weil-pbc-polynomial-ideal-coefficients-monomial, a polynomial belongs to J_i exactly when
each coefficient of exponent E belongs to I_E = (f_j : j < i and E_j > 0). Multiplication
by f_i X_i shifts E by the i-th unit exponent and multiplies its coefficient by f_i;
I_E is unchanged by that shift. Thus this multiplication is injective modulo J_i exactly
when multiplication by f_i is injective modulo every I_E. The final quotient is nonzero:
the constant coefficient of 1 is not in I_0 = (0).
(3) implies (2): for each term of a chosen subsequence, choose E supported precisely on
its preceding selected indices. The criterion gives the required injectivity at that term;
properness of the subfamily ideal gives the nonzero final quotient.
(2) implies (3): for each i and E, append f_i to the increasing subsequence of indices
j < i with E_j > 0. Its regularity gives injectivity modulo I_E. Apply the coefficient
criterion for every i and the nonzero final quotient to obtain polynomial regularity. -/
theorem isRegular_permutations_subsequences_polynomial_iff
    {R : Type u} [CommRing R] (r : ℕ) (f : Fin r → R)
    (hproper : Ideal.ofList (List.ofFn f) ≠ ⊤) :
    ((∀ l : List R, (List.ofFn f).Perm l → IsRegular R l) ↔
      (∀ l : List R, l.Sublist (List.ofFn f) → IsRegular R l)) ∧
    ((∀ l : List R, l.Sublist (List.ofFn f) → IsRegular R l) ↔
      IsRegular (MvPolynomial (Fin r) R)
        (List.ofFn (fun i : Fin r ↦ MvPolynomial.C (f i) * MvPolynomial.X i))) := by
  exact ⟨isRegular_permutations_iff_subsequences r f hproper,
    isRegular_subsequences_iff_polynomial_variables r f hproper⟩

end RingTheory.Sequence
