/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

@[expose] public section

universe u v

namespace RingHom

/-- A local homomorphism induces the coordinatewise homomorphism of maximal-ideal completions.
Source: Stacks Project, Tag 07ED, the induced map between completions.
(blueprint: lem-weil-pbc-fs-adic-completion-map-local)

Proof: Locality sends the source maximal ideal into the target maximal ideal and therefore
sends every power into the corresponding power. Lift the ring map to each quotient and
compose with the source completion's evaluation. These maps commute with quotient
projections; the inverse-limit universal property `AdicCompletion.liftRingHom` constructs
the completion map, and its evaluation formula gives the stated compatibility. -/
theorem exists_adicCompletion_map_of_local
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] :
    ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
        AdicCompletion (IsLocalRing.maximalIdeal B) B,
      ∀ (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) (a : A),
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a →
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) n (ψ x) =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B) ^ n) (φ a) := by
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  have hmap : mA.map φ ≤ mB :=
    Ideal.map_le_iff_le_comap.mpr (fun x hx => map_nonunit φ x hx)
  have hpow (n : ℕ) : (mA ^ n).map φ ≤ mB ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmap n
  let qmap (n : ℕ) : A ⧸ mA ^ n →+* B ⧸ mB ^ n :=
    Ideal.Quotient.lift (mA ^ n) ((Ideal.Quotient.mk (mB ^ n)).comp φ) (by
      intro x hx
      change Ideal.Quotient.mk (mB ^ n) (φ x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hpow n (Ideal.mem_map_of_mem φ hx))
  let f (n : ℕ) := (qmap n).comp (AdicCompletion.evalₐ mA n).toRingHom
  have hf {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow mB hmn).comp (f n) = f m := by
    ext x
    induction x using AdicCompletion.induction_on with
    | _ x =>
      simpa [f, qmap] using congrArg (qmap m) (AdicCompletion.Ideal.mk_eq_mk mA hmn x)
  let ψ := AdicCompletion.liftRingHom mB f (fun hmn => hf hmn)
  have heval (n : ℕ) :
      (AdicCompletion.evalₐ mB n).toRingHom.comp ψ = f n :=
    AdicCompletion.evalₐ_comp_liftRingHom mB f (fun hmn => hf hmn) n
  refine ⟨ψ, ?_⟩
  intro n x a hx
  have hx' := congrArg (fun g => g x) (heval n)
  dsimp [f, qmap] at hx'
  rw [hx] at hx'
  exact hx'

end RingHom
