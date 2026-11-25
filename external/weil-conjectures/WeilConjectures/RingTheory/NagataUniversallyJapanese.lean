/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.RingTheory.PolynomialNagata
import WeilConjectures.RingTheory.NagataDomainN2

/-!
# Nagata rings are universally Japanese

Source: Stacks Project, Algebra, Proposition 10.162.15 (Tag 0334), implication
(1) ⇒ (3) (blueprint: lem-weil-pbc-nagata-universally-japanese).
-/

@[expose] public section

universe u

private theorem isNagataRing_of_surjective (A B : Type u) [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (hA : IsNagataRing A) :
    IsNagataRing B := by
  let : Algebra A B := f.toAlgebra
  let : Module.Finite A B := Module.Finite.of_surjective (Algebra.linearMap A B) hf
  exact (finite_over_nagata_is_nagata A B hA).1

private theorem isNagataRing_mvPolynomial (R : Type u) [CommRing R]
    (hR : IsNagataRing R) (n : ℕ) : IsNagataRing (MvPolynomial (Fin n) R) := by
  induction n with
  | zero =>
      exact isNagataRing_of_surjective R _
        (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm.toRingHom
        (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm.surjective hR
  | succ n ih =>
      exact isNagataRing_of_surjective (Polynomial (MvPolynomial (Fin n) R)) _
        (MvPolynomial.finSuccEquiv R n).symm.toRingHom
        (MvPolynomial.finSuccEquiv R n).symm.surjective
        (isNagataRing_polynomial _ ih)

/-- A Nagata ring is universally Japanese: every finite type domain algebra is N-2.

Source: Stacks Project, Algebra, Proposition 10.162.15 (Tag 0334), implication
(1) ⇒ (3) (blueprint: lem-weil-pbc-nagata-universally-japanese).

Proof: Present a finite type algebra `S` as a quotient of `MvPolynomial (Fin n) R`.
Induct on `n` to show that this polynomial ring is Nagata: the zero-variable ring
is isomorphic to `R`, and the successor ring is isomorphic to a one-variable
polynomial ring over the preceding ring. The one-variable assertion reduces
prime quotients to injective monogenic extensions of Nagata domains, whose
transcendental and algebraic cases are treated separately. Transporting Nagata
along the polynomial isomorphisms and the surjective presentation uses
`finite_over_nagata_is_nagata`, since a surjective ring map is finite. Thus `S`
is Nagata; when `S` is a domain, its zero prime quotient makes it N-2 by
`isN2_of_isNagataRing_domain`. This gives `IsUniversallyJapanese R`.
-/
theorem isUniversallyJapanese_of_isNagataRing (R : Type u) [CommRing R]
    (hR : IsNagataRing R) : IsUniversallyJapanese R := by
  intro S _ _ _ _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  have hS := isNagataRing_of_surjective (MvPolynomial (Fin n) R) S f.toRingHom hf
    (isNagataRing_mvPolynomial R hR n)
  exact isN2_of_isNagataRing_domain S hS
