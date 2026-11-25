/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.LocalTensorQuotientComponentMap

/-!
# Detection of tensor quotients modulo the extended base ideal

Source: Stacks Project, Tag 07N9, quotient-product argument.
(blueprint: lem-weil-pbc-local-tensor-quotient-base-ideal-detection)
-/

@[expose] public section

universe u v w
open scoped TensorProduct
namespace AdicCompletion

/-- Local membership in the extended base-ideal power detects a tensor quotient.
Source: Stacks Project, Tag 07N9, with Tags 00JA and 00CT.
(blueprint: lem-weil-pbc-local-tensor-quotient-base-ideal-detection)

Proof: Set A = R_p, m = its maximal ideal, and B = A tensor_R S. Localization and
finite base change make B a finite Noetherian A-algebra. For n > 0, A/m^n is
Artinian: its maximal ideal is nilpotent and its successive quotients are finite
dimensional over A/m. Hence C = B/m^n B is Artinian. Integral-extension and
localization prime correspondence identify its primes with Q = p.primesOver S.
The product decomposition of an Artinian ring into its localizations identifies
C with the product of S_q/(m^n)S_q for q in Q; localization commutes with quotient.
Under this identification the class of a pure tensor r tensor s has q-component
the class of phi_q(r)*(s/1). The assumed membership kills the finite sum in every
component, so injectivity of the product map kills its class in C. The tensor
quotient equivalence identifies C with (A/m^n) tensor_R S, with exactly the pure
tensor formula in the conclusion. If Q is empty, C has no prime ideals and is
the zero ring, so this reasoning still applies. The empty sum is zero. -/
theorem local_tensor_quotient_base_ideal_detection
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (n : ℕ) (hn : 0 < n) :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    ∀ (ι : Type w) (t : Finset ι) (r : ι → A) (s : ι → S),
      (∀ q : p.primesOver S,
        (∑ i ∈ t, Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p)) (r i) *
          algebraMap S (Localization.AtPrime q.1) (s i)) ∈
            (m ^ n).map (Localization.localRingHom p q.1 (algebraMap R S)
              (Ideal.LiesOver.over (P := q.1) (p := p)))) →
      (∑ i ∈ t, (Ideal.Quotient.mk (m ^ n) (r i)) ⊗ₜ[R] s i) = 0 := by
  dsimp
  obtain ⟨φ, hφ, hpure⟩ := tensor_quotient_component_map R S p n hn
  intro ι t r s h
  apply hφ
  ext q
  rw [map_sum φ]
  simp only [Finset.sum_apply, map_zero]
  simp_rw [hpure]
  rw [← map_sum]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 (h q)

end AdicCompletion
