/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

universe u v

namespace RingHom

/-! # Dimension and maximal ideals under integral extensions

Source: Stacks Project, Algebra, Lemma Tag 00OJ (lemma-integral-dim-up),
with Lemmas Tags 00GT and 00OI (blueprint: proposition-proper-direct-image-constructible-complexes).
-/

/-- An integral ring map does not increase Krull dimension, and maximal ideals contract
 to maximal ideals. Source: Stacks Project, Algebra, Lemma Tag 00OJ
 (blueprint: proposition-proper-direct-image-constructible-complexes).

Proof: For a strict chain of prime ideals in the target, contract each prime along the
ring map. Integrality and incomparability make the contracted inclusions strict, so the
chain length is bounded by the Krull dimension of the source. For a maximal ideal in the
target, the integral-extension maximal-contraction theorem makes its contraction maximal.
-/
theorem IsIntegral.ringKrullDim_le_and_isMaximal_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R ∧
      ∀ (I : Ideal S), I.IsMaximal → (I.comap f).IsMaximal := by
  constructor
  · let _ : Algebra R S := f.toAlgebra
    have : Algebra.IsIntegral R S := ⟨hf⟩
    apply Order.krullDim_le_of_strictMono
      (fun I : PrimeSpectrum S ↦ (⟨I.asIdeal.comap f, inferInstance⟩ : PrimeSpectrum R))
    intro I J hIJ
    exact Ideal.IsIntegral.under_lt_under hIJ
  · intro I hI
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf I

end RingHom
