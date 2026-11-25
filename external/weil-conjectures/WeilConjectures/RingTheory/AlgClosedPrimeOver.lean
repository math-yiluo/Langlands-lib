/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Existence of an algebraically closed closed point above a prime, omitting the
differential-fibre comparison. Source: Stacks Project, Tag 00TT.
(blueprint: new-algclosed-prime-over).

Proof: Put κ = κ(q), and form K as the algebraic closure of ULift κ, lifting
κ into universe max u v. Compose the injective map κ → K with S → κ to get
f : S → K, and equip K with the k-algebra structure defined by f ∘ (k → S).
The tensor universal property gives φ : K ⊗[k] S → K, λ ⊗ s ↦ λ f(s).
It is surjective because φ(λ ⊗ 1) = λ, so ker φ is maximal. For s in S,
φ(1 ⊗ s) = 0 iff its image in κ is zero, since κ → K is injective.
The kernel of S → κ is q, so ker φ contracts to q. This constructs all
witnesses without selecting data from any unproved existence theorem.
-/
theorem exists_algClosed_prime_over
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S] [FiniteType k S]
    (q : PrimeSpectrum S) :
    ∃ (K : Type (max u v)) (_hK : Field K) (_hAk : Algebra k K) (_hCK : IsAlgClosed K)
      (qK : PrimeSpectrum (K ⊗[k] S)),
      qK.asIdeal.IsMaximal ∧
        PrimeSpectrum.comap
          (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK = q := by
  let κ := q.asIdeal.ResidueField
  let K := AlgebraicClosure (ULift.{u} κ)
  let ψ : κ →+* K := (algebraMap (ULift.{u} κ) K).comp ULift.ringEquiv.symm.toRingHom
  let f : S →+* K := ψ.comp (algebraMap S κ)
  let : Algebra k K := (f.comp (algebraMap k S)).toAlgebra
  let β : S →ₐ[k] K := ⟨f, fun _ ↦ rfl⟩
  let φ : K ⊗[k] S →ₐ[k] K :=
    TensorProduct.lift (AlgHom.id k K) β (fun _ _ ↦ Commute.all _ _)
  have hsurj : Function.Surjective φ := by
    intro x
    exact ⟨x ⊗ₜ[k] (1 : S), by simp [φ, TensorProduct.lift_tmul]⟩
  have hm : (RingHom.ker φ.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective φ.toRingHom hsurj
  let qK : PrimeSpectrum (K ⊗[k] S) := ⟨RingHom.ker φ.toRingHom, hm.isPrime⟩
  refine ⟨K, inferInstance, inferInstance, inferInstance, qK, hm, ?_⟩
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro s
  change φ (1 ⊗ₜ[k] s) = 0 ↔ s ∈ q.asIdeal
  simp only [φ, TensorProduct.lift_tmul, AlgHom.id_apply, one_mul]
  change ψ (algebraMap S κ s) = 0 ↔ s ∈ q.asIdeal
  rw [map_eq_zero_iff ψ ψ.injective]
  exact Ideal.algebraMap_residueField_eq_zero


end Algebra
