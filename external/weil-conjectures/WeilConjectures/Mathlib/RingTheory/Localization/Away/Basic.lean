/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Automorphisms and nilpotent kernels of localizations away from an element

- `Localization.awayAlgEquiv`: the automorphism of `C[1/s]` induced by an automorphism of `C`
  fixing `s`.
- `IsLocalization.Away.ker_mapₐ_le_nilradical`: the map `C[1/a] ⟶ D[1/f(a)]` induced by a map
  `f : C ⟶ D` with nilpotent kernel has nilpotent kernel.
-/

@[expose] public section

namespace Localization

variable {k C : Type*} [CommRing k] [CommRing C] [Algebra k C]

/-- The automorphism of `C[1/s]` induced by an automorphism `e` of `C` fixing `s`. -/
noncomputable def awayAlgEquiv (e : C ≃ₐ[k] C) (s : C) (hs : e s = s) :
    Localization.Away s ≃ₐ[k] Localization.Away s :=
  AlgEquiv.ofRingEquiv (f := IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers s)
    (T := Submonoid.powers s) (Localization.Away s) (Localization.Away s) e.toRingEquiv (by
      rw [Submonoid.map_powers]; exact congrArg _ hs)) (fun r ↦ by
    rw [IsScalarTower.algebraMap_apply k C, IsLocalization.ringEquivOfRingEquiv_eq]
    simp)

@[simp]
lemma awayAlgEquiv_algebraMap (e : C ≃ₐ[k] C) (s : C) (hs : e s = s) (x : C) :
    awayAlgEquiv e s hs (algebraMap C _ x) = algebraMap C _ (e x) :=
  IsLocalization.ringEquivOfRingEquiv_eq (M := Submonoid.powers s) (T := Submonoid.powers s)
    (by rw [Submonoid.map_powers]; exact congrArg _ hs) x

end Localization

namespace IsLocalization.Away

/-- The localization of a map with nilpotent kernel has nilpotent kernel. -/
lemma ker_mapₐ_le_nilradical {R C D Cₚ Dₚ : Type*} [CommRing R] [CommRing C] [CommRing D]
    [CommRing Cₚ] [CommRing Dₚ] [Algebra R C] [Algebra R D] [Algebra R Cₚ] [Algebra R Dₚ]
    [Algebra C Cₚ] [Algebra D Dₚ] [IsScalarTower R C Cₚ] [IsScalarTower R D Dₚ] (f : C →ₐ[R] D)
    (hf : RingHom.ker f ≤ nilradical C) (a : C) [IsLocalization.Away a Cₚ]
    [IsLocalization.Away (f a) Dₚ] :
    RingHom.ker (mapₐ Cₚ Dₚ f a) ≤ nilradical Cₚ := by
  intro x hx
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) x
  rw [RingHom.mem_ker, mapₐ_apply, map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx
  have hy : IsNilpotent (a ^ n * y) := mem_nilradical.1 (hf (by
    rw [RingHom.mem_ker, map_mul, map_pow]; exact hn))
  have h₁ : IsNilpotent (algebraMap C Cₚ (a ^ n * y) * IsLocalization.mk' Cₚ 1 s) :=
    Commute.isNilpotent_mul_right (Commute.all _ _) (hy.map _)
  have h₂ : IsLocalization.mk' Cₚ y s = (algebraMap C Cₚ (a ^ n * y) *
      IsLocalization.mk' Cₚ 1 s) * (invSelf a) ^ n := by
    have hu : algebraMap C Cₚ a ^ n * invSelf a ^ n = 1 := by
      rw [← mul_pow, mul_invSelf, one_pow]
    calc IsLocalization.mk' Cₚ y s = algebraMap C Cₚ y * IsLocalization.mk' Cₚ 1 s :=
          IsLocalization.mk'_eq_mul_mk'_one _ _
      _ = algebraMap C Cₚ y * IsLocalization.mk' Cₚ 1 s *
          (algebraMap C Cₚ a ^ n * invSelf a ^ n) := by rw [hu, mul_one]
      _ = _ := by rw [map_mul, map_pow]; ring
  change IsNilpotent (IsLocalization.mk' Cₚ y s)
  rw [h₂]
  exact Commute.isNilpotent_mul_right (Commute.all _ _) h₁

end IsLocalization.Away
