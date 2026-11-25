/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Bijectivity of a map out of `L ⊗_R A` from a filtered presentation

Let `R → L` be a map to a field, `x ∈ R` with nonzero image in `L` and `(Oᵢ)` a directed family
of `R`-subalgebras of `L` such that every element of `L` is `x⁻ⁿ o` with `o ∈ Oᵢ` for some `i`
and `n`; for instance `L = ℚ̄_ℓ`, `R = 𝒪_E`, `x = ℓ` and `Oᵢ = 𝒪_F` for the finite extensions
`F ⊇ E`. Then `L ⊗_R A` is the colimit of the groups `Oᵢ ⊗_R A` along the inclusions and
multiplication by `x`, through the maps `κᵢₙ : τ ↦ x⁻ⁿ τ`
(`Subalgebra.exists_eq_stageTensorMap`). Hence a map `T : L ⊗_R A → B` is bijective as soon as
`B` is the colimit of the same system, compatibly with `T`
(`Subalgebra.bijective_of_stageTensorMap`).
-/

@[expose] public section

open TensorProduct

namespace Subalgebra

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L] (x : R)
  {A : Type*} [AddCommGroup A] [Module R A] {ι : Type*} (O : ι → Subalgebra R L)

/-- The map `κᵢₙ : Oᵢ ⊗_R A → L ⊗_R A`, `τ ↦ x⁻ⁿ τ`. -/
noncomputable def stageTensorMap (i : ι) (n : ℕ) : O i ⊗[R] A →+ L ⊗[R] A where
  toFun τ := ((algebraMap R L x ^ n)⁻¹ : L) • (O i).val.toLinearMap.rTensor A τ
  map_zero' := by rw [map_zero, smul_zero]
  map_add' _ _ := by rw [map_add, smul_add]

lemma stageTensorMap_tmul (i : ι) (n : ℕ) (o : O i) (a : A) :
    stageTensorMap x O i n (o ⊗ₜ a) = (((algebraMap R L x ^ n)⁻¹ : L) * o) ⊗ₜ a := by
  simp [stageTensorMap, smul_tmul', smul_eq_mul]

/-- `κᵢₙ` is compatible with the inclusions `Oᵢ ⊆ Oⱼ`. -/
lemma stageTensorMap_inclusion {i j : ι} (h : O i ≤ O j) (n : ℕ) (τ : O i ⊗[R] A) :
    stageTensorMap x O j n ((Subalgebra.inclusion h).toLinearMap.rTensor A τ) =
      stageTensorMap x O i n τ := by
  simp only [stageTensorMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ← LinearMap.comp_apply,
    ← LinearMap.rTensor_comp]
  rfl

variable {x} in
/-- `κᵢₙ` is compatible with multiplication by `x`. -/
lemma stageTensorMap_pow_smul (hx : algebraMap R L x ≠ 0) (i : ι) (n m : ℕ)
    (τ : O i ⊗[R] A) : stageTensorMap x O i (n + m) (x ^ m • τ) = stageTensorMap x O i n τ := by
  simp only [stageTensorMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.map_smul,
    algebra_compatible_smul L (x ^ m), smul_smul, map_pow, pow_add]
  congr 1
  rw [mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hx), mul_one]

variable {x O}

/-- **`L ⊗_R A` is exhausted by the stages `x⁻ⁿ (Oᵢ ⊗_R A)`.** -/
lemma exists_eq_stageTensorMap [Nonempty ι] (hx : algebraMap R L x ≠ 0)
    (hdir : ∀ i j, ∃ k, O i ≤ O k ∧ O j ≤ O k)
    (hexh : ∀ c : L, ∃ (i : ι) (n : ℕ), algebraMap R L x ^ n * c ∈ O i) (t : L ⊗[R] A) :
    ∃ (i : ι) (n : ℕ) (τ : O i ⊗[R] A), stageTensorMap x O i n τ = t := by
  induction t using TensorProduct.inductionOn with
  | tmul c a =>
    obtain ⟨i, n, hc⟩ := hexh c
    refine ⟨i, n, ⟨_, hc⟩ ⊗ₜ a, ?_⟩
    rw [stageTensorMap_tmul]
    congr 1
    exact inv_mul_cancel_left₀ (pow_ne_zero n hx) c
  | add t t' ht ht' =>
    obtain ⟨i, n, τ, rfl⟩ := ht
    obtain ⟨j, n', τ', rfl⟩ := ht'
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, n + n', x ^ n' • (Subalgebra.inclusion hik).toLinearMap.rTensor A τ +
      x ^ n • (Subalgebra.inclusion hjk).toLinearMap.rTensor A τ', ?_⟩
    rw [map_add, stageTensorMap_pow_smul O hx, add_comm n n', stageTensorMap_pow_smul O hx,
      stageTensorMap_inclusion, stageTensorMap_inclusion]

/-- **Bijectivity criterion for a map out of `L ⊗_R A`.** Let `T : L ⊗_R A → B` be additive.
Suppose every element of `B` is `T(κᵢₙ τ)` for some `i`, `n` and `τ ∈ Oᵢ ⊗_R A`, and that
`T(κᵢₙ τ) = 0` forces `xᵐ τ` to vanish in `Oⱼ ⊗_R A` for some `Oⱼ ⊇ Oᵢ` and some `m`. Then `T`
is bijective. -/
theorem bijective_of_stageTensorMap [Nonempty ι] (hx : algebraMap R L x ≠ 0)
    (hdir : ∀ i j, ∃ k, O i ≤ O k ∧ O j ≤ O k)
    (hexh : ∀ c : L, ∃ (i : ι) (n : ℕ), algebraMap R L x ^ n * c ∈ O i)
    {B : Type*} [AddCommGroup B] (T : L ⊗[R] A →+ B)
    (hsurj : ∀ b : B, ∃ (i : ι) (n : ℕ) (τ : O i ⊗[R] A), T (stageTensorMap x O i n τ) = b)
    (hinj : ∀ (i : ι) (n : ℕ) (τ : O i ⊗[R] A), T (stageTensorMap x O i n τ) = 0 →
      ∃ (j : ι) (h : O i ≤ O j) (m : ℕ),
        x ^ m • (Subalgebra.inclusion h).toLinearMap.rTensor A τ = 0) :
    Function.Bijective T := by
  refine ⟨(injective_iff_map_eq_zero T).2 fun t ht ↦ ?_, fun b ↦ ?_⟩
  · obtain ⟨i, n, τ, rfl⟩ := exists_eq_stageTensorMap hx hdir hexh t
    obtain ⟨j, h, m, hm⟩ := hinj i n τ ht
    rw [← stageTensorMap_inclusion x O h, ← stageTensorMap_pow_smul O hx j n m, hm, map_zero]
  · obtain ⟨i, n, τ, rfl⟩ := hsurj b
    exact ⟨_, rfl⟩

end Subalgebra
