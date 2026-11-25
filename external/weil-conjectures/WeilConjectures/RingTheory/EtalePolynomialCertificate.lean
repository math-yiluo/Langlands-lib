/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Operations

/-! # Finite polynomial certificates for an inverse conormal differential

Source: Stacks Project, Algebra, proof of Tag 07RI.
(blueprint: def-weil-pbc-etale-polynomial-certificate).
-/

@[expose] public section

universe u

namespace Algebra

/-- The finite polynomial conditions for an inverse to the conormal differential.
The first family expresses a right inverse modulo the relation ideal; the second
expresses a left inverse on its generating relation classes modulo the ideal square.
Source: Stacks Project, Algebra, proof of Tag 07RI, lines 47654-47662.
(blueprint: def-weil-pbc-etale-polynomial-certificate). -/
def EtalePolynomialCertificate {R : Type u} [CommRing R] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) R) : Prop :=
  ∃ c : Fin m → Fin n → MvPolynomial (Fin n) R,
    (∀ k l : Fin n,
      (∑ j, c j k * MvPolynomial.pderiv l (f j)) - (if k = l then 1 else 0) ∈
        Ideal.span (Set.range f)) ∧
    (∀ j : Fin m,
      (∑ k, MvPolynomial.pderiv k (f j) * ∑ j', c j' k * f j') - f j ∈
        (Ideal.span (Set.range f)) ^ 2)

end Algebra
