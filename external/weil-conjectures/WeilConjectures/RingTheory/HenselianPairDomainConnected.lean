/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Henselian
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Ring

@[expose] public section

universe u
namespace PrimeSpectrum

/-- Domain case of connectedness for spectra of quotients by henselian ideals.
Source: Stacks Project, More on Algebra, Lemma 15.11.16 (Tag 09Y6).
(blueprint: lem-weil-pbc-henselian-pair-prime-connected-domain)

The henselian Jacobson condition makes J proper, so B/J is nonzero. Given an
idempotent in B/J, choose a representative a₀ in B and apply simple-root lifting
to the monic polynomial X(X - 1). Its derivative modulo J is 2a₀ - 1, whose square
is 1, so it is a unit even in characteristic 2. The lifted root a satisfies
a(a - 1) = 0, and the domain condition forces a = 0 or a = 1. Thus every
idempotent of B/J is zero or one. The clopen-idempotent criterion makes its
spectrum connected. The continuous quotient-spectrum map has image exactly V(J),
so V(J) is connected and nonempty. -/
theorem connectedSpace_zeroLocus_of_henselian_domain {B : Type u} [CommRing B]
    [Nontrivial B] [NoZeroDivisors B] (J : Ideal B) [HenselianRing B J] :
    ConnectedSpace (zeroLocus (J : Set B)) := by
  have hJ : J ≠ ⊤ := by
    intro h
    have hj : Ideal.jacobson (⊥ : Ideal B) = ⊤ :=
      top_le_iff.mp (h ▸ HenselianRing.jac (R := B) (I := J))
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp hj)
  have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : ConnectedSpace (PrimeSpectrum (B ⧸ J)) := by
    apply connectedSpace_of_isIdempotentElem
    intro e he
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective e
    let f : Polynomial B := Polynomial.X * (Polynomial.X - 1)
    have hf : f.Monic := Polynomial.monic_X.mul (by
      simpa using Polynomial.monic_X_sub_C (1 : B))
    have hmem : f.eval a₀ ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp [f, mul_sub, he.eq]
    have hunit : IsUnit (Ideal.Quotient.mk J (f.derivative.eval a₀)) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨Ideal.Quotient.mk J (f.derivative.eval a₀), ?_⟩
      simp only [Polynomial.derivative_mul, Polynomial.derivative_X, one_mul,
        Polynomial.derivative_one, sub_zero, mul_one,
        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
        map_add, map_sub, map_one, f]
      calc
        _ = 4 * ((Ideal.Quotient.mk J a₀) * (Ideal.Quotient.mk J a₀) -
          Ideal.Quotient.mk J a₀) + 1 := by ring
        _ = 1 := by rw [he.eq]; ring
    obtain ⟨a, ha, hdiff⟩ := HenselianRing.is_henselian f hf a₀ hmem hunit
    have ha' : a * (a - 1) = 0 := by simpa [f] using ha
    have heq : Ideal.Quotient.mk J a = Ideal.Quotient.mk J a₀ :=
      Ideal.Quotient.eq.mpr hdiff
    rcases mul_eq_zero.mp ha' with hzero | hone
    · exact Or.inl (heq.symm.trans (by simp [hzero]))
    · exact Or.inr (heq.symm.trans (by simp [sub_eq_zero.mp hone]))
  apply isConnected_iff_connectedSpace.mp
  have h := isConnected_range (continuous_comap (Ideal.Quotient.mk J))
  simpa [range_comap_of_surjective (B ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, Ideal.mk_ker] using h

end PrimeSpectrum
