/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated

@[expose] public section

universe u
namespace AlgebraicGeometry.Scheme

/-- Positive depth from exclusion of the maximal associated prime.

Source: Stacks Project, Algebra, Tag 00LL, and the definition of depth (Tag 00LI).
(blueprint: stage3-depth-one-from-no-maximal-associated)

Proof: If the module is zero, its maximal-ideal multiple is the whole module,
so its depth is infinity. Otherwise Tag 00LL supplies an element of the maximal
ideal acting injectively. Its singleton is weakly regular and, by Nakayama for
finite nonzero modules, regular. This length-one sequence belongs to the set
whose supremum defines depth, giving the claimed lower bound. -/
theorem depth_one_of_finite_localized_module_of_no_maximal_associated
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : IsLocalRing.maximalIdeal R ∉ associatedPrimes R M) :
    (1 : ℕ∞) ≤ IsLocalRing.depth (R := R) M := by
  classical
  cases subsingleton_or_nontrivial M with
  | inl hM =>
    let := hM
    unfold IsLocalRing.depth Ideal.depth
    rw [ite_eq_left (Subsingleton.elim _ _)]
    exact le_top
  | inr hM =>
    let := hM
    obtain ⟨x, hx, hreg⟩ := exists_mem_maximalIdeal_smul_injective R M h
    unfold IsLocalRing.depth Ideal.depth
    split
    · exact le_top
    · apply le_sSup
      refine ⟨[x], ?_, ?_, by simp⟩
      · apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
        · simpa using hx
        · exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff M x).mpr hreg
      · simpa using hx

end AlgebraicGeometry.Scheme
