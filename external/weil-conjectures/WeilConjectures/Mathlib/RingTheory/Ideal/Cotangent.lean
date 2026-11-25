/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Tangent vectors at a rational point

Let `ε : A →ₐ[k] k` be a `k`-point of a `k`-algebra `A`, with ideal `I = ker ε`. A tangent vector
at `ε` is a linear form on the cotangent space `I / I²`. Equivalently it is a point of `A` with
values in the dual numbers `k[ε]` lifting `ε`, or a point derivation `A → k` at `ε`.

## Main definitions

- `AlgHom.cotangentDerivation`: the point derivation at `ε` of a linear form on `I / I²`.
- `AlgHom.toDualNumber`: the point `A → k[ε]` of a linear form on `I / I²`.
- `AlgHom.cotangentForm`: the linear form on `I / I²` of a point `A → k[ε]` lifting `ε`.

## Main results

- `AlgHom.toDualNumber_cotangentForm`, `AlgHom.cotangentForm_toDualNumber`: the two
  constructions are inverse to each other.
-/

@[expose] public section

open TrivSqZeroExt

namespace AlgHom

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k)

theorem sub_algebraMap_mem_ker (a : A) : a - algebraMap k A (ε a) ∈ RingHom.ker ε := by
  simp [RingHom.mem_ker]

/-- The point derivation `a ↦ φ (a - ε a)` at the `k`-point `ε` attached to a linear form `φ` on
the cotangent space at `ε`. -/
noncomputable def cotangentDerivation (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) : A →ₗ[k] k where
  toFun a := φ ((RingHom.ker ε).toCotangent ⟨_, ε.sub_algebraMap_mem_ker a⟩)
  map_add' a b := by
    rw [← map_add, ← map_add]
    congr 2
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' c a := by
    rw [RingHom.id_apply, ← map_smul, ← LinearMap.map_smul_of_tower]
    congr 2
    ext
    simp [Algebra.smul_def, mul_sub]

variable {ε}

theorem cotangentDerivation_apply (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) (a : A) :
    ε.cotangentDerivation φ a =
      φ ((RingHom.ker ε).toCotangent ⟨_, ε.sub_algebraMap_mem_ker a⟩) :=
  rfl

theorem cotangentDerivation_of_mem (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) {a : A}
    (ha : a ∈ RingHom.ker ε) :
    ε.cotangentDerivation φ a = φ ((RingHom.ker ε).toCotangent ⟨a, ha⟩) := by
  rw [cotangentDerivation_apply]
  congr 2
  ext
  simp [RingHom.mem_ker.1 ha]

/-- The point derivation of a linear form on the cotangent space satisfies the Leibniz rule at
`ε`. -/
theorem cotangentDerivation_mul (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) (a b : A) :
    ε.cotangentDerivation φ (a * b) =
      ε a * ε.cotangentDerivation φ b + ε b * ε.cotangentDerivation φ a := by
  have hmem := ε.sub_algebraMap_mem_ker
  have h : (RingHom.ker ε).toCotangent ⟨_, hmem (a * b)⟩ =
      ε a • (RingHom.ker ε).toCotangent ⟨_, hmem b⟩ +
        ε b • (RingHom.ker ε).toCotangent ⟨_, hmem a⟩ := by
    rw [← algebraMap_smul A (ε a), ← algebraMap_smul A (ε b), ← map_smul, ← map_smul, ← map_add,
      Ideal.toCotangent_eq]
    have h' : a * b - algebraMap k A (ε (a * b)) -
        (algebraMap k A (ε a) * (b - algebraMap k A (ε b)) +
          algebraMap k A (ε b) * (a - algebraMap k A (ε a))) =
        (a - algebraMap k A (ε a)) * (b - algebraMap k A (ε b)) := by
      simp only [map_mul]
      ring
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, h', pow_two]
    exact Ideal.mul_mem_mul (hmem a) (hmem b)
  simp only [cotangentDerivation_apply, h, map_add, map_smul, smul_eq_mul]

/-- The point `a ↦ ε a + φ (a - ε a) ε` of `A` with values in the dual numbers attached to a
linear form `φ` on the cotangent space at `ε`. -/
noncomputable def toDualNumber (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) :
    A →ₐ[k] DualNumber k :=
  AlgHom.ofLinearMap ((inlAlgHom k k k).toLinearMap ∘ₗ ε.toLinearMap +
      inrHom k k ∘ₗ ε.cotangentDerivation φ)
    (by
      have h : (⟨_, ε.sub_algebraMap_mem_ker 1⟩ : RingHom.ker ε) = 0 := Subtype.ext (by simp)
      ext
      · simp
      · simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, snd_add,
          snd_one, cotangentDerivation_apply, h, map_zero]
        simp)
    (fun a b ↦ by
      ext
      · simp
      · simp [cotangentDerivation_mul, mul_comm])

@[simp]
theorem fst_toDualNumber (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) (a : A) :
    (ε.toDualNumber φ a).fst = ε a := by
  simp [toDualNumber]

@[simp]
theorem snd_toDualNumber (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) (a : A) :
    (ε.toDualNumber φ a).snd = ε.cotangentDerivation φ a := by
  simp [toDualNumber]

theorem fstHom_comp_toDualNumber (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) :
    (fstHom k k k).comp (ε.toDualNumber φ) = ε :=
  AlgHom.ext fun a ↦ by simp

/-- The linear form `a ↦ (ψ a).snd` on the cotangent space at `ε` of a point `ψ` of `A` with
values in the dual numbers lifting `ε`. -/
noncomputable def cotangentForm (ψ : A →ₐ[k] DualNumber k)
    (hψ : (fstHom k k k).comp ψ = ε) : (RingHom.ker ε).Cotangent →ₗ[k] k :=
  have hfst (a : A) : (ψ a).fst = ε a := congrArg (· a) hψ
  let f : RingHom.ker ε →ₛₗ[ε.toRingHom] k :=
    { toFun x := (ψ x).snd
      map_add' x y := by simp
      map_smul' a x := by
        simp [snd_mul, hfst, RingHom.mem_ker.1 x.2] }
  have hf : (RingHom.ker ε • ⊤ : Submodule A (RingHom.ker ε)) ≤ LinearMap.ker f :=
    Submodule.smul_le.2 fun a ha x _ ↦ by simp [f, RingHom.mem_ker.1 ha]
  let g := Submodule.liftQ _ f hf
  { toFun := g
    map_add' := map_add g
    map_smul' c v := by
      rw [← algebraMap_smul A c v, g.map_smulₛₗ]
      simp }

@[simp]
theorem cotangentForm_toCotangent (ψ : A →ₐ[k] DualNumber k) (hψ : (fstHom k k k).comp ψ = ε)
    (x : RingHom.ker ε) : ε.cotangentForm ψ hψ ((RingHom.ker ε).toCotangent x) = (ψ x).snd :=
  rfl

theorem toDualNumber_cotangentForm (ψ : A →ₐ[k] DualNumber k)
    (hψ : (fstHom k k k).comp ψ = ε) : ε.toDualNumber (ε.cotangentForm ψ hψ) = ψ := by
  have hfst (a : A) : (ψ a).fst = ε a := congrArg (· a) hψ
  ext a
  · simp [hfst]
  · simp [cotangentDerivation_apply, TrivSqZeroExt.algebraMap_eq_inl]

theorem cotangentForm_toDualNumber (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) :
    ε.cotangentForm (ε.toDualNumber φ) (fstHom_comp_toDualNumber φ) = φ := by
  ext v
  obtain ⟨x, rfl⟩ := (RingHom.ker ε).toCotangent_surjective v
  rw [cotangentForm_toCotangent, snd_toDualNumber, cotangentDerivation_of_mem φ x.2]

theorem toDualNumber_injective : Function.Injective (ε.toDualNumber) := fun φ φ' h ↦ by
  rw [← cotangentForm_toDualNumber φ, ← cotangentForm_toDualNumber φ']
  ext v
  obtain ⟨x, rfl⟩ := (RingHom.ker ε).toCotangent_surjective v
  simp only [cotangentForm_toCotangent, h]

end AlgHom
