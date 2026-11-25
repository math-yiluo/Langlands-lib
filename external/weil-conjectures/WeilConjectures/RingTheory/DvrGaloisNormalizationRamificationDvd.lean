/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! # Divisibility of the ramification and residue degrees in a Galois normalization

Source: Stacks Project, Tag 09EB.
(blueprint: lem-sbc-dvr-galois-normalization-ramification-dvd) -/

@[expose] public section
universe u
namespace RingTheory

/-- The ramification and residue degrees at every closed normalization prime divide
any multiple of the Galois extension degree.

Source: Stacks Project, Tag 09EB.
(blueprint: lem-sbc-dvr-galois-normalization-ramification-dvd)

Proof: The integral closure C is finite over B by the separable trace-pairing
argument. It is a Dedekind domain, and its fraction field is E. The group
Gal(E/Frac(B)) acts on C, transitively on the primes over the maximal ideal
of B. Hence the ramification index e and residue degree f are constant there.
The Galois fundamental identity is r*(e*f)=[E:Frac(B)], where r is the number
of primes above the maximal ideal. Both e and f divide this product and thus
any multiple n of the extension degree. This includes the trivial extension;
no invertibility assumption on n is used. -/
theorem dvr_galois_normalization_ramification_dvd
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (n : ℕ)
    (hE : FiniteDimensional (FractionRing B) E ∧
      IsGalois (FractionRing B) E ∧ Module.finrank (FractionRing B) E ∣ n) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let C := integralClosure B E
    ∀ (R : Ideal C) (hR : R.IsPrime),
    letI := hR
    R.comap (algebraMap B C) = IsLocalRing.maximalIdeal B →
      R.ramificationIdx B ∣ n ∧ R.inertiaDeg B ∣ n := by
  dsimp only
  let K := FractionRing B
  let : Algebra B E := ((algebraMap K E).comp (algebraMap B K)).toAlgebra
  let : IsScalarTower B K E := IsScalarTower.of_algebraMap_eq' rfl
  let := hE.1
  let := hE.2.1
  let C := integralClosure B E
  let : Module.Finite B C := IsIntegralClosure.finite B K E C
  let : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain B K E C
  let : IsFractionRing C E := IsIntegralClosure.isFractionRing_of_finite_extension B K E C
  let : MulSemiringAction (E ≃ₐ[K] E) C := IsIntegralClosure.MulSemiringAction B K E C
  let : IsGaloisGroup (E ≃ₐ[K] E) B C := IsGaloisGroup.of_isFractionRing _ _ _ K E
  let : Module.IsTorsionFree B E :=
    Module.IsTorsionFree.trans K
  let : Module.Free B C := IsIntegralClosure.module_free B K E C
  intro R hR hc
  let := hR
  let : R.LiesOver (IsLocalRing.maximalIdeal B) := ⟨hc.symm⟩
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (IsLocalRing.maximalIdeal B) C (E ≃ₐ[K] E)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (IsLocalRing.maximalIdeal B) R (E ≃ₐ[K] E),
    Ideal.inertiaDegIn_eq_inertiaDeg (IsLocalRing.maximalIdeal B) R (E ≃ₐ[K] E),
    IsGalois.card_aut_eq_finrank K E] at h
  constructor
  · apply dvd_trans _ hE.2.2
    rw [← h]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  · apply dvd_trans _ hE.2.2
    rw [← h]
    exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

end RingTheory
