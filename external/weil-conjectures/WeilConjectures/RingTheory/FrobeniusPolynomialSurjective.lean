/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.RingTheory.FrobeniusPolynomialSolution

/-!
# Surjectivity of the Frobenius polynomial solution scheme

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-frobenius-polynomial-surjective).
-/

@[expose] public section

set_option autoImplicit false

universe u

open MvPolynomial

namespace Algebra

/-- The spectrum of an inhomogeneous Frobenius polynomial solution algebra covers
the spectrum of the coefficient ring.

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-frobenius-polynomial-surjective).

Proof: at a prime of the coefficient ring, pass to an algebraic closure of its
residue field. The Frobenius polynomial solution theorem gives a homomorphism from
the solution algebra to this field over the coefficient ring. The inverse image of
the zero ideal is a prime of the solution algebra. Its contraction is the chosen
prime, because the residue-field map has exactly that kernel and the algebraic
closure inclusion is injective. The proof also covers rank zero.
-/
theorem frobenius_polynomial_surjective
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (n : ℕ) (a : Fin n → Fin n → R) (b : Fin n → R) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range
        (fun i : Fin n ↦ C (b i) + X i - ∑ j, C (a i j) * X j ^ p))))) := by
  intro q
  let k := q.asIdeal.ResidueField
  let K := AlgebraicClosure k
  have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast (algebraMap R K), CharP.cast_eq_zero R p, map_zero])
  obtain ⟨f⟩ := exists_frobenius_polynomial_solution R K p n a b
  refine ⟨PrimeSpectrum.comap f.toRingHom ⟨⊥, inferInstance⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R _) (Ideal.comap f.toRingHom ⊥) = q.asIdeal
  have hc : f.toRingHom.comp (algebraMap R _) = algebraMap R K := by
    ext c
    exact f.commutes c
  rw [Ideal.comap_comap, hc]
  rw [IsScalarTower.algebraMap_eq R k K, ← Ideal.comap_comap]
  have hker : Ideal.comap (algebraMap k K) ⊥ = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap k K).injective
  rw [hker, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end Algebra
