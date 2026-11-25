/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Frobenius forms of finite free extensions of principal ideal domains

Let `R ⟶ S` be a ring morphism of domains which makes `S` a finite free `R`-module,
with `S` a principal ideal domain. Then the `R`-linear dual `Hom_R(S, R)`, an `S`-module through
`(s • λ)(x) = λ(s * x)`, is free of rank one over `S`. A generator `λ` is a *Frobenius form*:
every `R`-linear form on `S` is `λ(s * -)` for a unique `s ∈ S`
(`Module.exists_bijective_comp_mulLeft`).

This is the input that makes extension and coextension of scalars along `R ⟶ S` isomorphic,
for instance for the inclusion `𝒪_E ⟶ 𝒪_L` of rings of integers of finite extensions of `ℚ_ℓ`.

## Proof

The dual `Hom_R(S, R)` is a finitely generated `S`-module, and it is torsion free: if
`λ(s * -) = 0` with `s ≠ 0`, some nonzero `r ∈ R` is a multiple `r = s * t` (`S` is integral
over `R`), so `r * λ(x) = λ(s * t * x) = 0` for all `x`. Over the principal ideal domain `S`
it is therefore free, and comparing ranks over `R` in the tower `R ⟶ S ⟶ Hom_R(S, R)` gives
`rank_R S * rank_S Hom_R(S, R) = rank_R Hom_R(S, R) = rank_R S`, so its rank over `S` is one.
-/

@[expose] public section

namespace Module

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

namespace FrobeniusForm

/-- The action of `S` on the `R`-linear forms on `S`: `(s • λ)(x) = λ(s * x)`. -/
@[instance_reducible]
noncomputable def dualModule : Module S (S →ₗ[R] R) where
  smul s φ := φ ∘ₗ LinearMap.mulLeft R s
  one_smul φ := LinearMap.ext fun x ↦ by
    change φ (1 * x) = φ x
    rw [one_mul]
  mul_smul s t φ := LinearMap.ext fun x ↦ by
    change φ (s * t * x) = φ (t * (s * x))
    rw [mul_left_comm, mul_assoc]
  smul_zero s := rfl
  smul_add s φ ψ := rfl
  add_smul s t φ := LinearMap.ext fun x ↦ by
    change φ ((s + t) * x) = φ (s * x) + φ (t * x)
    rw [add_mul, map_add]
  zero_smul φ := LinearMap.ext fun x ↦ by
    change φ (0 * x) = 0
    rw [zero_mul, map_zero]

attribute [local instance] dualModule

lemma smul_apply (s : S) (φ : S →ₗ[R] R) (x : S) : (s • φ) x = φ (s * x) := rfl

instance : IsScalarTower R S (S →ₗ[R] R) where
  smul_assoc r s φ := LinearMap.ext fun x ↦ by
    change φ ((r • s) * x) = r • φ (s * x)
    rw [smul_mul_assoc, map_smul]

variable {R S} [IsDomain R] [IsDomain S] [Module.Finite R S]

/-- The `R`-linear dual of `S` is a torsion free `S`-module. -/
lemma isTorsionFree_dual : IsTorsionFree S (S →ₗ[R] R) := by
  refine .of_smul_eq_zero fun s φ h ↦ or_iff_not_imp_left.2 fun hs ↦ ?_
  have hne := Ideal.under_ne_bot_of_integral_mem hs (Ideal.mem_span_singleton_self s)
    (Algebra.IsIntegral.isIntegral (R := R) s)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hr)
  refine LinearMap.ext fun x ↦ ?_
  have h' : r • φ x = 0 := by
    rw [← map_smul, Algebra.smul_def, ← ht, mul_comm t, mul_assoc, ← smul_apply, h,
      LinearMap.zero_apply]
  exact (smul_eq_zero.1 h').resolve_left hr0

variable [IsPrincipalIdealRing S] [Module.Free R S]

/-- The `R`-linear dual of `S` is free of rank one over `S`. -/
lemma finrank_dual : finrank S (S →ₗ[R] R) = 1 := by
  have := isTorsionFree_dual (R := R) (S := S)
  have : Module.Finite S (S →ₗ[R] R) := Module.Finite.of_restrictScalars_finite R S _
  have h := Module.finrank_mul_finrank R S (S →ₗ[R] R)
  rw [Module.finrank_linearMap_self] at h
  have hpos : 0 < finrank R S := Module.finrank_pos
  exact (Nat.mul_eq_left hpos.ne').1 h

end FrobeniusForm

open FrobeniusForm in
/-- **Existence of a Frobenius form.** Let `R ⟶ S` be a morphism of domains making `S` a
finite free `R`-module, with `S` a principal ideal domain. Then there is an `R`-linear form
`λ : S → R` such that every `R`-linear form on `S` is `λ(s * -)` for a unique `s ∈ S`. -/
theorem exists_bijective_comp_mulLeft [IsDomain R] [IsDomain S] [IsPrincipalIdealRing S]
    [Module.Finite R S] [Module.Free R S] :
    ∃ φ : S →ₗ[R] R, Function.Bijective fun s : S ↦ φ ∘ₗ LinearMap.mulLeft R s := by
  let := dualModule R S
  have := isTorsionFree_dual (R := R) (S := S)
  have : Module.Finite S (S →ₗ[R] R) := Module.Finite.of_restrictScalars_finite R S _
  let b : Basis (Fin 1) S (S →ₗ[R] R) := Module.finBasisOfFinrankEq S _ finrank_dual
  refine ⟨b 0, fun s t hst ↦ ?_, fun φ ↦ ⟨b.repr φ 0, ?_⟩⟩
  · have hst' : s • b 0 = t • b 0 := hst
    exact smul_left_injective S (b.ne_zero 0) hst'
  · change b.repr φ 0 • b 0 = φ
    conv_rhs => rw [← b.sum_repr φ]
    rw [Fin.sum_univ_one]

end Module
