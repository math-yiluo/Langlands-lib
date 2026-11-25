/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Kähler differentials modulo a power of an ideal

Let `R → S` be a ring map, `I ⊆ S` an ideal and `n` a natural number. We show that the map
`S/Iⁿ ⊗[S] Ω[S⁄R] → S/Iⁿ ⊗[S/Iⁿ⁺¹] Ω[(S/Iⁿ⁺¹)⁄R]`, `t ⊗ ds ↦ t ⊗ d(s̄)`, is bijective
(Stacks, Lemma 02HQ).

More generally, for a surjection `S → S'` of `R`-algebras and an `S'`-algebra `Q` such that
`1 ⊗ da = 0` in `Q ⊗[S] Ω[S⁄R]` for all `a` in the kernel, the natural map
`Q ⊗[S] Ω[S⁄R] → Q ⊗[S'] Ω[S'⁄R]` is bijective.

## Main results

* `KaehlerDifferential.tensorMapBaseChange_bijective`: the general statement.
* `KaehlerDifferential.D_mem_pow_smul_top`: `d(Iⁿ⁺¹) ⊆ Iⁿ Ω[S⁄R]`.
* `KaehlerDifferential.tensorQuotPowMap_bijective`: Stacks, Lemma 02HQ.
-/

@[expose] public section

open TensorProduct

namespace KaehlerDifferential

section General

variable (R S S' Q : Type*) [CommRing R] [CommRing S] [CommRing S'] [CommRing Q]
  [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
  [Algebra S Q] [Algebra S' Q] [IsScalarTower S S' Q]

/-- For `R`-algebras `S → S'` and an `S'`-algebra `Q`, the `Q`-linear map
`Q ⊗[S] Ω[S⁄R] → Q ⊗[S'] Ω[S'⁄R]`, `q ⊗ ds ↦ q ⊗ d(s̄)`. -/
noncomputable def tensorMapBaseChange : Q ⊗[S] Ω[S⁄R] →ₗ[Q] Q ⊗[S'] Ω[S'⁄R] :=
  (mapBaseChange R S S').baseChange Q ∘ₗ
    (AlgebraTensorModule.cancelBaseChange S S' Q Q Ω[S⁄R]).symm.toLinearMap

@[simp]
lemma tensorMapBaseChange_tmul (q : Q) (x : Ω[S⁄R]) :
    tensorMapBaseChange R S S' Q (q ⊗ₜ x) = q ⊗ₜ map R R S S' x := by
  simp [tensorMapBaseChange]

lemma tensorMapBaseChange_tmul_D (q : Q) (s : S) :
    tensorMapBaseChange R S S' Q (q ⊗ₜ D R S s) = q ⊗ₜ D R S' (algebraMap S S' s) := by
  simp

/-- For a surjection of `R`-algebras `S → S'` and an `S'`-algebra `Q` such that `1 ⊗ da = 0` in
`Q ⊗[S] Ω[S⁄R]` for every `a` in the kernel of `S → S'`, the map
`Q ⊗[S] Ω[S⁄R] → Q ⊗[S'] Ω[S'⁄R]` is bijective. -/
theorem tensorMapBaseChange_bijective (h : Function.Surjective (algebraMap S S'))
    (hD : ∀ a ∈ RingHom.ker (algebraMap S S'), (1 : Q) ⊗ₜ[S] D R S a = 0) :
    Function.Bijective (tensorMapBaseChange R S S' Q) := by
  let e := AlgebraTensorModule.cancelBaseChange S S' Q Q Ω[S⁄R]
  have hf : Function.Exact (LinearMap.ker (mapBaseChange R S S')).subtype
      (mapBaseChange R S S') := LinearMap.exact_subtype_ker_map _
  have hsurj : Function.Surjective ((mapBaseChange R S S').lTensor Q) :=
    LinearMap.lTensor_surjective Q (mapBaseChange_surjective R S S' h)
  have hex := lTensor_exact (M := LinearMap.ker (mapBaseChange R S S')) Q hf
    (mapBaseChange_surjective R S S' h)
  have hzero : (LinearMap.ker (mapBaseChange R S S')).subtype.lTensor Q = 0 := by
    ext q k
    obtain ⟨k, hk⟩ := k
    obtain ⟨c, rfl⟩ : k ∈ LinearMap.range (kerCotangentToTensor R S S') := by
      rw [range_kerCotangentToTensor R S S' h]; exact hk
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ c
    apply e.injective
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.lTensor_tmul, Submodule.subtype_apply, kerCotangentToTensor_toCotangent,
      LinearMap.zero_apply, map_zero]
    rw [show e (q ⊗ₜ[S'] ((1 : S') ⊗ₜ[S] D R S a.1)) = q ⊗ₜ[S] D R S a.1 by simp [e]]
    rw [show q ⊗ₜ[S] D R S a.1 = q • ((1 : Q) ⊗ₜ[S] D R S a.1) by
      rw [smul_tmul', smul_eq_mul, mul_one], hD a.1 a.2, smul_zero]
  have key : ∀ x, tensorMapBaseChange R S S' Q x =
      (mapBaseChange R S S').lTensor Q (e.symm x) := fun x => by
    rw [tensorMapBaseChange, LinearMap.comp_apply, LinearMap.baseChange_eq_lTensor]
    rfl
  constructor
  · intro x y hxy
    have : (mapBaseChange R S S').lTensor Q (e.symm x - e.symm y) = 0 := by
      rw [map_sub, sub_eq_zero, ← key, ← key]; exact hxy
    obtain ⟨z, hz⟩ := (hex _).mp this
    rw [hzero, LinearMap.zero_apply, eq_comm, sub_eq_zero] at hz
    exact e.symm.injective hz
  · intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨e x, by rw [key, LinearEquiv.symm_apply_apply]⟩

end General
section PowIdeal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Leibniz rule: `d(Iⁿ⁺¹) ⊆ Iⁿ Ω[S⁄R]`. -/
theorem D_mem_pow_smul_top (I : Ideal S) (n : ℕ) {a : S} (ha : a ∈ I ^ (n + 1)) :
    D R S a ∈ I ^ n • (⊤ : Submodule S Ω[S⁄R]) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [Derivation.leibniz]
      refine add_mem (Submodule.smul_mem_smul hx trivial) ?_
      have := Submodule.smul_mem_smul hy (ih hx)
      rwa [← Submodule.mul_smul, ← pow_succ'] at this
    · rw [map_add]
      exact add_mem hx hy

variable (R) in
/-- **Kähler differentials modulo a power of an ideal** (Stacks, Lemma 02HQ). Let `R → S` be a
ring map, `I ⊆ S` an ideal, `n` a natural number and `S' = S ⧸ I ^ (n + 1)`. Then the
`S ⧸ I ^ n`-linear map `S/Iⁿ ⊗[S] Ω[S⁄R] → S/Iⁿ ⊗[S'] Ω[S'⁄R]`, `t ⊗ ds ↦ t ⊗ d(s̄)`, is
bijective (see `tensorMapBaseChange_tmul_D` for the formula). Here `S ⧸ I ^ n` carries its
(unique) `S'`-algebra structure compatible with `S`, given as instance arguments. The statement
holds for all `n` (the blueprint assumes `n ≥ 1`), and the tensor factors are written in the
order `S/Iⁿ ⊗ Ω` instead of `Ω ⊗ S/Iⁿ`.
(blueprint: `lem-weil-pbc-kahler-differentials-mod-power-ideal`) -/
theorem tensorQuotPowMap_bijective (I : Ideal S) (n : ℕ)
    [Algebra (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n)] [IsScalarTower S (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n)] :
    Function.Bijective (tensorMapBaseChange R S (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n)) := by
  refine tensorMapBaseChange_bijective _ _ _ _ Ideal.Quotient.mk_surjective (fun a ha => ?_)
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at ha
  refine Submodule.smul_induction_on (D_mem_pow_smul_top I n ha) (fun x hx m _ => ?_)
    (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_tmul]
  · rw [tmul_add, hx, hy, add_zero]

variable (R) in
/-- The isomorphism `S/Iⁿ ⊗[S] Ω[S⁄R] ≃ S/Iⁿ ⊗[S/Iⁿ⁺¹] Ω[(S/Iⁿ⁺¹)⁄R]` of
`tensorQuotPowMap_bijective`. -/
noncomputable def tensorQuotPowEquiv (I : Ideal S) (n : ℕ)
    [Algebra (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n)] [IsScalarTower S (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n)] :
    (S ⧸ I ^ n) ⊗[S] Ω[S⁄R] ≃ₗ[S ⧸ I ^ n] (S ⧸ I ^ n) ⊗[S ⧸ I ^ (n + 1)] Ω[(S ⧸ I ^ (n + 1))⁄R] :=
  LinearEquiv.ofBijective _ (tensorQuotPowMap_bijective R I n)

end PowIdeal

end KaehlerDifferential
