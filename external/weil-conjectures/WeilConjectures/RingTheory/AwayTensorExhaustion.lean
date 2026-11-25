/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Base change to a localisation away from an element, elementwise

Let `S` be the localisation of `R` away from `x` and `A` an `R`-module. Then `S ⊗_R A` is the
colimit of `A --x--> A --x--> ⋯`, along the maps `a ↦ x⁻ⁿ ⊗ a`. Elementwise:

- every element of `S ⊗_R A` is `x⁻ⁿ ⊗ a`
  (`IsLocalization.Away.exists_eq_invSelf_pow_tmul`);
- `x⁻ⁿ ⊗ a = x⁻ⁿ ⊗ b` forces `xᵐ a = xᵐ b` for some `m`
  (`IsLocalization.Away.exists_pow_smul_eq_of_invSelf_pow_tmul_eq`).

Moreover, for a field extension `K ⊆ L` and a ring map `R → K`, the map
`K ⊗_R A → L ⊗_R A` is injective (`TensorProduct.rTensor_algebraMap_injective_of_field`).
-/

@[expose] public section

open TensorProduct

namespace IsLocalization.Away

variable {R : Type*} [CommRing R] (x : R) {S : Type*} [CommRing S] [Algebra R S]
  [IsLocalization.Away x S] {A : Type*} [AddCommGroup A] [Module R A]

lemma invSelf_pow_add_tmul_pow_smul (k j : ℕ) (c : A) :
    ((invSelf x : S) ^ (k + j)) ⊗ₜ[R] (x ^ j • c) = ((invSelf x : S) ^ k) ⊗ₜ[R] c := by
  rw [← smul_tmul, algebra_compatible_smul S, smul_eq_mul, pow_add, map_pow, mul_left_comm,
    ← mul_pow, mul_invSelf, one_pow, mul_one]

/-- Every element of `S ⊗_R A` is `x⁻ⁿ ⊗ a`. -/
lemma exists_eq_invSelf_pow_tmul (t : S ⊗[R] A) :
    ∃ (n : ℕ) (a : A), t = ((invSelf x : S) ^ n) ⊗ₜ[R] a := by
  induction t using TensorProduct.inductionOn with
  | tmul s a =>
    obtain ⟨n, r, h⟩ := surj x s
    refine ⟨n, r • a, ?_⟩
    have hs : s = (invSelf x : S) ^ n * algebraMap R S r := by
      rw [← h, mul_comm s, ← mul_assoc, ← mul_pow, mul_comm (invSelf x), mul_invSelf, one_pow,
        one_mul]
    rw [hs, ← smul_tmul, algebra_compatible_smul S r, smul_eq_mul, mul_comm]
  | add t t' ht ht' =>
    obtain ⟨n, a, rfl⟩ := ht
    obtain ⟨m, b, rfl⟩ := ht'
    refine ⟨n + m, x ^ m • a + x ^ n • b, ?_⟩
    rw [tmul_add, invSelf_pow_add_tmul_pow_smul, add_comm n m, invSelf_pow_add_tmul_pow_smul]

/-- `x⁻ⁿ ⊗ a = x⁻ⁿ ⊗ b` in `S ⊗_R A` forces `xᵐ a = xᵐ b` for some `m`. -/
lemma exists_pow_smul_eq_of_invSelf_pow_tmul_eq {n : ℕ} {a b : A}
    (h : ((invSelf x : S) ^ n) ⊗ₜ[R] a = ((invSelf x : S) ^ n) ⊗ₜ[R] b) :
    ∃ m : ℕ, x ^ m • a = x ^ m • b := by
  have h1 : (1 : S) ⊗ₜ[R] a = (1 : S) ⊗ₜ[R] b := by
    have e (c : A) : (1 : S) ⊗ₜ[R] c =
        (algebraMap R S x ^ n : S) • (((invSelf x : S) ^ n) ⊗ₜ[R] c) := by
      rw [smul_tmul', smul_eq_mul, ← mul_pow, mul_invSelf, one_pow]
    rw [e, e, h]
  have : IsLocalizedModule (Submonoid.powers x) (TensorProduct.mk R S A 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers x) S _).2
      (TensorProduct.isBaseChange R A S)
  obtain ⟨⟨c, m, rfl⟩, hc⟩ :=
    IsLocalizedModule.exists_of_eq (S := Submonoid.powers x) (f := TensorProduct.mk R S A 1) h1
  exact ⟨m, hc⟩

end IsLocalization.Away

namespace TensorProduct

/-- For a field extension `K ⊆ L` and a ring map `R → K`, the map `K ⊗_R A → L ⊗_R A` is
injective: it is `K ⊗_K (K ⊗_R A) → L ⊗_K (K ⊗_R A)`, and every `K`-module is flat. -/
lemma rTensor_algebraMap_injective_of_field {R K L : Type*} [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L] (A : Type*) [AddCommGroup A]
    [Module R A] :
    Function.Injective ((IsScalarTower.toAlgHom R K L).toLinearMap.rTensor A) := by
  have : Module.Flat K (K ⊗[R] A) := Module.Flat.of_free
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := K ⊗[R] A)
    (Algebra.linearMap K L) (algebraMap K L).injective
  have key : (IsScalarTower.toAlgHom R K L).toLinearMap.rTensor A =
      (AlgebraTensorModule.cancelBaseChange R K K L A).restrictScalars R ∘ₗ
        ((Algebra.linearMap K L).rTensor (K ⊗[R] A)).restrictScalars R ∘ₗ
          ((TensorProduct.lid K (K ⊗[R] A)).symm.restrictScalars R).toLinearMap := by
    ext k a
    simp [Algebra.algebraMap_eq_smul_one]
  rw [key, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.injective _).comp (hinj.comp (LinearEquiv.injective _))

end TensorProduct
