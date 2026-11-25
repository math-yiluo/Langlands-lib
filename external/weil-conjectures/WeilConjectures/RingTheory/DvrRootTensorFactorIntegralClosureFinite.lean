/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Finiteness of the integral closure in a generic tensor factor

Source: Stacks Project, Tag 032L.
(blueprint: lem-sbc-dvr-root-tensor-factor-integral-closure-finite) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- The normalization of a generic field factor of a tame root algebra is finite.

Source: Stacks Project, Tag 032L.
(blueprint: lem-sbc-dvr-root-tensor-factor-integral-closure-finite)

Proof: Put K = Frac(B). F is finite-dimensional over K because A is finite over B
and E is finite-dimensional over K. The map A -> F is injective: its kernel
contracts to zero in B, because the field K maps injectively into F, and
integrality of A over B forces this kernel to be zero. Thus F has a compatible
Frac(A)-algebra structure and is finite-dimensional over Frac(A). There is a
surjection Frac(A) tensor_K E -> F: on pure tensors it multiplies the two
structural images, and every class of e tensor_B a is in its image. Finite
separability of E/K makes this tensor product formally unramified over
Frac(A); its field quotient F is consequently separable over Frac(A).
Apply the trace-pairing lattice theorem IsIntegralClosure.finite (Tag 032L)
to the Noetherian normal domain A. No DVR or degree-divisibility hypothesis
and no choice of a prime of the integral closure are needed. -/
theorem dvr_root_tensor_factor_integralClosure_finite
    (B : Type u) [CommRing B] [IsDomain B]
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] [Algebra B A] [Module.Finite B A] [FaithfulSMul B A]
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ Algebra.IsSeparable (FractionRing B) E) :
    let : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let D := E ⊗[B] A
    ∀ (P : Ideal D) (hP : P.IsMaximal),
    let := hP
    let F := D ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
    let := alpha.toAlgebra
    Module.Finite A (integralClosure A F) := by
  dsimp only
  let K := FractionRing B
  let : Algebra B E :=
    ((algebraMap K E).comp (algebraMap B K)).toAlgebra
  let : IsScalarTower B K E := IsScalarTower.of_algebraMap_eq' rfl
  let := hE.1
  let := hE.2
  let D := E ⊗[B] A
  intro P hP
  let := hP
  let F := D ⧸ P
  let : Field F := Ideal.Quotient.field P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
  let := alpha.toAlgebra
  let : Algebra K D := inferInstance
  let : IsScalarTower K E D := inferInstance
  let : IsScalarTower B E D := inferInstance
  let : IsScalarTower B K D := IsScalarTower.to₁₂₄ B K E D
  let : Algebra K F := inferInstanceAs (Algebra K (D ⧸ P))
  let : Algebra B F := inferInstanceAs (Algebra B (D ⧸ P))
  let : IsScalarTower B A F := by
    apply IsScalarTower.of_algebraMap_eq'
    ext b
    exact congrArg (Ideal.Quotient.mk P)
      ((Algebra.TensorProduct.includeRight : A →ₐ[B] D).commutes b).symm
  let : IsScalarTower K E F := inferInstance
  let : Module.Finite E D := inferInstance
  let : Module.Finite E F := inferInstance
  let : Module.Finite K F := Module.Finite.trans E F
  have halpha : Function.Injective alpha := by
    apply (RingHom.injective_iff_ker_eq_bot alpha).mpr
    apply Ideal.eq_bot_of_under_eq_bot (R := B)
    ext b
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    change algebraMap A F (algebraMap B A b) = 0 ↔ b = 0
    rw [← IsScalarTower.algebraMap_apply B A F]
    rw [IsScalarTower.algebraMap_apply B K F]
    exact ⟨fun hb ↦ IsFractionRing.injective B K
      ((algebraMap K F).injective (by simpa only [map_zero] using hb)),
      fun hb ↦ by simp [hb]⟩
  let : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr halpha
  let L := FractionRing A
  let : Algebra L F := FractionRing.liftAlgebra A F
  let : IsScalarTower A L F := FractionRing.isScalarTower_liftAlgebra A F
  let : Algebra K L := FractionRing.liftAlgebra B L
  let : IsScalarTower B K L := FractionRing.isScalarTower_liftAlgebra B L
  let : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq' (by
    apply IsFractionRing.ringHom_ext (A := B)
    intro b
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B K F,
      ← IsScalarTower.algebraMap_apply B K L,
      ← IsScalarTower.algebraMap_apply B L F])
  let : Module.Finite L F := Module.Finite.of_restrictScalars_finite K L F
  let : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_isSeparable K E
  let : Algebra.FormallyUnramified L F := by
    let φ : L ⊗[K] E →ₐ[L] F := Algebra.TensorProduct.lift
      (Algebra.ofId L F) (IsScalarTower.toAlgHom K E F) (fun _ _ ↦ Commute.all _ _)
    apply Algebra.FormallyUnramified.of_surjective φ
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction x using TensorProduct.inductionOn with
    | tmul e a =>
      refine ⟨algebraMap A L a ⊗ₜ[K] e, ?_⟩
      simp only [φ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
        ← IsScalarTower.algebraMap_apply A L F]
      change alpha a * Ideal.Quotient.mk P (e ⊗ₜ[B] (1 : A)) =
        Ideal.Quotient.mk P (e ⊗ₜ[B] a)
      change Ideal.Quotient.mk P (1 ⊗ₜ[B] a) *
        Ideal.Quotient.mk P (e ⊗ₜ[B] 1) = Ideal.Quotient.mk P (e ⊗ₜ[B] a)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩
  let : Algebra.IsSeparable L F := by
    exact Algebra.FormallyUnramified.isSeparable L F
  exact IsIntegralClosure.finite A L F (integralClosure A F)

end RingTheory
