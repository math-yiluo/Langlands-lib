/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Locally principal ideals are invertible

## Main results

- `Ideal.invertible_of_forall_isMaximal`: an ideal `I` of a domain `A` which is locally principal,
  in the sense that for every maximal ideal `𝔮` there are `0 ≠ a ∈ I` and `s ∉ 𝔮` with
  `s • I ⊆ (a)`, is an invertible `A`-module.
- `Module.Invertible.of_isLocalized_span`: a finitely presented module which is free of rank one
  locally on a family generating the unit ideal is invertible.
- `Module.Invertible.exists_mem_bijective_smul`: if the localization `R_S` is a unique
  factorization domain, an invertible `R`-module becomes free of rank one after inverting a
  single element of `S` (as `Pic(R_S)` is trivial, Stacks 0BCH).
-/

@[expose] public section

/-- Let `I` be an ideal of a domain `A` which is locally principal: for every maximal ideal `𝔮`
there are `0 ≠ a ∈ I` and `s ∉ 𝔮` such that `a ∣ s * b` for all `b ∈ I`. Then `I` is an invertible
`A`-module. Indeed, viewing `I` as a submodule of the fraction field, `I * (1 / I) = 1` since
`s = a * (s / a)` lies in `I * (1 / I)`. -/
theorem Ideal.invertible_of_forall_isMaximal {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A)
    (h : ∀ 𝔮 : Ideal A, 𝔮.IsMaximal → ∃ a ∈ I, a ≠ 0 ∧ ∃ s ∉ 𝔮, ∀ b ∈ I, a ∣ s * b) :
    Module.Invertible A I := by
  let K := FractionRing A
  have inj := IsFractionRing.injective A K
  let I' : Submodule A K := Submodule.map (Algebra.linearMap A K) I
  have hle : I' * (1 / I') ≤ 1 := by
    rw [mul_comm, ← Submodule.le_div_iff_mul_le]
  have hge : 1 ≤ I' * (1 / I') := by
    rw [Submodule.one_le]
    let L : Ideal A := (I' * (1 / I')).comap (Algebra.linearMap A K)
    suffices L = ⊤ by
      have h1 : (1 : A) ∈ L := this ▸ Submodule.mem_top
      simpa [L] using h1
    by_contra hL
    obtain ⟨𝔮, h𝔮, hL𝔮⟩ := Ideal.exists_le_maximal L hL
    obtain ⟨a, haI, ha0, s, hs𝔮, hs⟩ := h 𝔮 h𝔮
    have ha0' : algebraMap A K a ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap A K)]
      exact inj.ne ha0
    refine hs𝔮 (hL𝔮 ?_)
    have hk : algebraMap A K s / algebraMap A K a ∈ 1 / I' := by
      rw [Submodule.mem_div_iff_forall_mul_mem]
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc⟩ := hs b hb
      rw [Submodule.mem_one]
      refine ⟨c, ?_⟩
      rw [Algebra.linearMap_apply, div_mul_eq_mul_div, ← map_mul, hc, map_mul,
        mul_div_cancel_left₀ _ ha0']
    have := Submodule.mul_mem_mul (Submodule.mem_map_of_mem (f := Algebra.linearMap A K) haI) hk
    rwa [Algebra.linearMap_apply, mul_div_cancel₀ _ ha0'] at this
  have hu : IsUnit I' := .of_mul_eq_one (1 / I') (le_antisymm hle hge)
  exact .congr ((LinearEquiv.ofEq _ _ hu.unit_spec).trans
    (Submodule.equivMapOfInjective _ inj I).symm)

open TensorProduct in
/-- **Invertibility is a local property.** A finitely presented `R`-module `M` such that for each
`r` in a family `s` generating the unit ideal the localization `M_r` is free of rank one over
`R_r` is invertible. -/
theorem Module.Invertible.of_isLocalized_span {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.FinitePresentation R M] (s : Set R) (spn : Ideal.span s = ⊤)
    (Rₚ : s → Type*) [∀ r, CommRing (Rₚ r)] [∀ r, Algebra R (Rₚ r)]
    [∀ r, IsLocalization.Away r.1 (Rₚ r)]
    (Mₚ : s → Type*) [∀ r, AddCommGroup (Mₚ r)] [∀ r, Module R (Mₚ r)]
    [∀ r, Module (Rₚ r) (Mₚ r)] [∀ r, IsScalarTower R (Rₚ r) (Mₚ r)]
    (f : ∀ r, M →ₗ[R] Mₚ r) [∀ r, IsLocalizedModule.Away r.1 (f r)]
    (H : ∀ r, Nonempty (Mₚ r ≃ₗ[Rₚ r] Rₚ r)) : Module.Invertible R M := by
  let dl (r : s) : Module.Dual R M →ₗ[R] Module.Dual (Rₚ r) (Mₚ r) :=
    IsLocalizedModule.mapExtendScalars (.powers r.1) (f r) (Algebra.linearMap R (Rₚ r)) (Rₚ r)
  let e (r : s) := IsLocalization.moduleTensorEquiv (.powers r.1) (Rₚ r)
    (Module.Dual (Rₚ r) (Mₚ r)) (Mₚ r)
  refine ⟨bijective_of_isLocalized_span s spn
    (fun r ↦ Module.Dual (Rₚ r) (Mₚ r) ⊗[R] Mₚ r) (fun r ↦ map (dl r) (f r))
    Rₚ (fun r ↦ Algebra.linearMap R (Rₚ r)) _ fun r ↦ ?_⟩
  have : Module.Invertible (Rₚ r) (Mₚ r) := .congr (H r).some.symm
  have hmap : IsLocalizedModule.map (.powers r.1) (map (dl r) (f r))
      (Algebra.linearMap R (Rₚ r)) (contractLeft R M) =
      ((contractLeft (Rₚ r) (Mₚ r)).restrictScalars R) ∘ₗ
        ((e r).symm.restrictScalars R).toLinearMap := by
    refine IsLocalizedModule.linearMap_ext (.powers r.1) (map (dl r) (f r))
      (Algebra.linearMap R (Rₚ r)) ?_
    rw [IsLocalizedModule.map_comp]
    ext φ m
    exact (IsLocalizedModule.map_apply (.powers r.1) (f r)
      (Algebra.linearMap R (Rₚ r)) φ m).symm
  rw [hmap]
  exact (Module.Invertible.bijective (R := Rₚ r) (M := Mₚ r)).comp (e r).symm.bijective

/-- The localization of the map `r ↦ r • m` is the map `a ↦ a • f m`. -/
theorem IsLocalizedModule.map_toSpanSingleton {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f] (m : M) :
    IsLocalizedModule.map S (Algebra.linearMap R Rₛ) f (LinearMap.toSpanSingleton R M m) =
      (LinearMap.toSpanSingleton Rₛ Mₛ (f m)).restrictScalars R := by
  refine IsLocalizedModule.linearMap_ext S (Algebra.linearMap R Rₛ) f ?_
  rw [IsLocalizedModule.map_comp]
  ext
  simp

/-- **Spreading out the triviality of an invertible module.** Let `S` be a submonoid of `R` such
that the localization `R_S` is a unique factorization domain, so that every invertible
`R_S`-module is free (Stacks 0BCH). Then an invertible `R`-module `M` becomes free of rank one
after inverting a single element `s ∈ S`: there is `m ∈ M` such that `r ↦ r • m` is a bijection
`R_s ≃ M_s`, for any localizations `R_s` of `R` and `M_s` of `M` at the powers of `s`. -/
theorem Module.Invertible.exists_mem_bijective_smul {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Invertible R M] (S : Submonoid R) [IsDomain (Localization S)]
    [UniqueFactorizationMonoid (Localization S)] :
    ∃ s ∈ S, ∃ m : M, ∀ (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization.Away s Rₛ]
      (Mₛ : Type*) [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
      (f : M →ₗ[R] Mₛ) [IsLocalizedModule.Away s f], Function.Bijective fun r : Rₛ ↦ r • f m := by
  have : IsGCDMonoid (Localization S) := ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
  have := Module.finitePresentation_of_projective R M
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free (Localization S) (LocalizedModule S M))
  obtain ⟨m, t, hx⟩ : ∃ m t, LocalizedModule.mk m t = e.symm 1 := by
    induction e.symm 1 using LocalizedModule.induction_on with
    | h m t => exact ⟨m, t, rfl⟩
  have hsurj : Function.Surjective
      (LinearMap.toSpanSingleton (Localization S) _ (LocalizedModule.mk m (1 : S))) := by
    intro z
    refine ⟨e z * Localization.mk 1 t, ?_⟩
    rw [LinearMap.toSpanSingleton_apply, mul_smul, LocalizedModule.mk_smul_mk, one_smul, mul_one,
      hx, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  obtain ⟨s, hs, H⟩ := exists_bijective_map_powers S (Algebra.linearMap R (Localization S))
    (LocalizedModule.mkLinearMap S M) (LinearMap.toSpanSingleton R M m) (by
      rw [IsLocalizedModule.map_toSpanSingleton]
      exact Module.Invertible.bijective_of_surjective (R := Localization S) hsurj)
  refine ⟨s, hs, m, fun Rₛ _ _ _ Mₛ _ _ _ _ f _ ↦ ?_⟩
  have := (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Algebra.linearMap R Rₛ) f).mpr (H s dvd_rfl)
  rwa [IsLocalizedModule.map_toSpanSingleton] at this
