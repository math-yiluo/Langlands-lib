/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Away
import WeilConjectures.Mathlib.Algebra.Algebra.Basic

/-! # Semilinear base change to localized coefficients

For a ring map `φ : R →+* S`, elements `t : R`, `b : S`, a ring map
`c : R[1/t] →+* S[1/b]` extending `φ`, and an additive `φ`-semilinear map `u : M →+ N`,
the formula `a ⊗ m ↦ c a ⊗ u m` defines an additive map
`R[1/t] ⊗[R] M →+ S[1/b] ⊗[S] N` (`Localization.Away.semilinearTensorMap`). It is
bijective when `u` is bijective and `b ∣ φ t`
(`Localization.Away.semilinearTensorMap_bijective`).
-/

@[expose] public noncomputable section

open TensorProduct

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] {t : R} {b : S} {φ : R →+* S}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The additive map `Loc_t ⊗[R] M → Loc_b ⊗[S] N`, `a ⊗ m ↦ c a ⊗ u m`, induced by an
additive `φ`-semilinear map `u` and a ring map `c` of localizations extending `φ`. -/
noncomputable def Localization.Away.semilinearTensorMap
    (c : Localization.Away t →+* Localization.Away b)
    (hc : ∀ r : R, c (algebraMap R _ r) = algebraMap S _ (φ r))
    (u : M →+ N) (hu : ∀ (r : R) (m : M), u (r • m) = φ r • u m) :
    Localization.Away t ⊗[R] M →+ Localization.Away b ⊗[S] N :=
  TensorProduct.liftAddHom
    { toFun := fun a ↦ (TensorProduct.mk S (Localization.Away b) N (c a)).toAddMonoidHom.comp u
      map_zero' := by
        ext m
        simp
      map_add' := by
        intro a a'
        ext m
        simp }
    (fun r a m ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_comp,
        LinearMap.toAddMonoidHom_coe, Function.comp_apply, TensorProduct.mk_apply]
      rw [Algebra.smul_def, map_mul, hc, hu, ← Algebra.smul_def, TensorProduct.smul_tmul])

/-- The defining formula of `Localization.Away.semilinearTensorMap` on pure tensors. -/
@[simp] theorem Localization.Away.semilinearTensorMap_tmul
    (c : Localization.Away t →+* Localization.Away b)
    (hc : ∀ r : R, c (algebraMap R _ r) = algebraMap S _ (φ r))
    (u : M →+ N) (hu : ∀ (r : R) (m : M), u (r • m) = φ r • u m)
    (a : Localization.Away t) (m : M) :
    Localization.Away.semilinearTensorMap c hc u hu (a ⊗ₜ m) = c a ⊗ₜ u m :=
  TensorProduct.liftAddHom_tmul _ _ a m

/-- `Localization.Away.semilinearTensorMap` is `φ`-semilinear. -/
theorem Localization.Away.semilinearTensorMap_smul
    (c : Localization.Away t →+* Localization.Away b)
    (hc : ∀ r : R, c (algebraMap R _ r) = algebraMap S _ (φ r))
    (u : M →+ N) (hu : ∀ (r : R) (m : M), u (r • m) = φ r • u m)
    (r : R) (x : Localization.Away t ⊗[R] M) :
    Localization.Away.semilinearTensorMap c hc u hu (r • x) =
      φ r • Localization.Away.semilinearTensorMap c hc u hu x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [TensorProduct.smul_tmul', semilinearTensorMap_tmul, semilinearTensorMap_tmul,
      TensorProduct.smul_tmul', Algebra.smul_def, map_mul, hc, ← Algebra.smul_def]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- If `b ∣ φ t` and `u` is a bijective additive `φ`-semilinear map, then the induced map
`Loc_t ⊗[R] M → Loc_b ⊗[S] N` is bijective: inverting `t` inverts `b` on `S`-modules. -/
theorem Localization.Away.semilinearTensorMap_bijective
    (c : Localization.Away t →+* Localization.Away b)
    (hc : ∀ r : R, c (algebraMap R _ r) = algebraMap S _ (φ r))
    (u : M →+ N) (hu : ∀ (r : R) (m : M), u (r • m) = φ r • u m)
    (hd : b ∣ φ t) (hbij : Function.Bijective u) :
    Function.Bijective (Localization.Away.semilinearTensorMap c hc u hu) := by
  obtain ⟨s, hs⟩ := hd
  have ht (n : ℕ) : IsUnit (algebraMap R (Localization.Away t) (t ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit t).pow n
  have hb (n : ℕ) : IsUnit (algebraMap S (Localization.Away b) (b ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit b).pow n
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj
      (TensorProduct.mk R (Localization.Away t) M 1) t x
    have h1 : (1 : Localization.Away b) ⊗ₜ[S] u m = 0 := by
      have := semilinearTensorMap_tmul c hc u hu 1 m
      rw [map_one, ← TensorProduct.mk_apply, ← hm, semilinearTensorMap_smul, hx,
        smul_zero] at this
      exact this.symm
    rw [← TensorProduct.mk_apply, ← map_zero (TensorProduct.mk S (Localization.Away b) N 1)]
      at h1
    obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (r := b) h1
    rw [smul_zero] at hk
    have hmk : t ^ k • m = 0 := by
      apply hbij.1
      rw [hu, map_zero, map_pow, hs, mul_pow, mul_comm, mul_smul, hk, smul_zero]
    apply eq_zero_of_smul_eq_zero_of_isUnit_algebraMap (ht n)
    rw [hm, TensorProduct.mk_apply]
    apply eq_zero_of_smul_eq_zero_of_isUnit_algebraMap (ht k)
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hmk, TensorProduct.tmul_zero]
  · obtain ⟨n, z, hz⟩ := IsLocalizedModule.Away.surj
      (TensorProduct.mk S (Localization.Away b) N 1) b y
    obtain ⟨m, hm⟩ := hbij.2 (s ^ n • z)
    refine ⟨((IsLocalization.Away.invSelf (S := Localization.Away t) t) ^ n) ⊗ₜ m, ?_⟩
    rw [semilinearTensorMap_tmul, hm, ← sub_eq_zero]
    apply eq_zero_of_smul_eq_zero_of_isUnit_algebraMap (hb n)
    rw [smul_sub, hz, sub_eq_zero, TensorProduct.mk_apply, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul, ← mul_smul, ← mul_pow, ← hs, ← map_pow, ← TensorProduct.smul_tmul,
      Algebra.smul_def, ← hc, ← map_mul, map_pow (algebraMap R (Localization.Away t)), ← mul_pow,
      IsLocalization.Away.mul_invSelf, one_pow, map_one]

