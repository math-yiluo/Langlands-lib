/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHomConstantTensor

/-!
# The derived hom on `Dctf` commutes with tensoring by a finite constant coefficient

For `K, M ∈ Dctf(X_ét, Λ)`, `X` of finite type over a field, `Λ` finite and `N` a finitely
generated `Λ`-module, the canonical map `RHom(K, M) ⊗ᴸ N_X ⟶ RHom(K, M ⊗ᴸ N_X)` is an
isomorphism (`AlgebraicGeometry.Etale.isIso_derivedHomTensorMap_constantSingle`), by the way-out
argument along the first syzygies from the free modules of finite rank
(`WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHomConstantTensor`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

variable [Finite Λ] {k : Type u} [Field k]

/-- For `K, M ∈ Dctf(X_ét, Λ)`, `X` of finite type over a field and `Λ` finite, and a finitely
generated `Λ`-module `N`, the canonical map `RHom(K, M) ⊗ᴸ N_X ⟶ RHom(K, M ⊗ᴸ N_X)` is an
isomorphism. -/
theorem isIso_derivedHomTensorMap_constantSingle (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] {K M}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) (N : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ N] :
    IsIso (derivedHomTensorMap K M (constantSingle (ModuleCat.{u + 1} Λ) X N)) := by
  rw [← derivedHomTensorNatTrans_app]
  obtain ⟨B, hB⟩ := derivedHomBoundedAmplitude_of_constructibleFiniteTor aX hK
  obtain ⟨-, c, d, hMt⟩ := hM
  have hMc := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hMt
  have : ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj M).IsLE (d + B) := hB c d M hMc
  refine _root_.DerivedCategory.isIso_app_of_exists_distTriang
    (derivedHomTensorNatTrans K M)
    (fun Z ↦ ∃ (N : ModuleCat.{u + 1} Λ) (_ : Module.Finite Λ N),
      Z = constantSingle (ModuleCat.{u + 1} Λ) X N)
    (d + B) ?_ ?_ _ ⟨N, inferInstance, rfl⟩
  · rintro _ ⟨N, _, rfl⟩
    have h₁ := isLE_derivedTensor_obj (ModuleCat.{u + 1} Λ) X
      ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj M) (constantSingle (ModuleCat.{u + 1} Λ) X N)
      (d + B) 0
    rw [add_zero] at h₁
    refine ⟨h₁, hB c d _ ?_⟩
    exact (torAmplitudeIn_iff_forall_derivedTensor _ X c d M).1 hMt
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)
  · rintro _ ⟨N, _, rfl⟩
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' Λ N
    let S := ModuleCat.shortComplexOfCompEqZero (LinearMap.ker p).subtype p (by ext; simp)
    have hS : S.ShortExact :=
      ModuleCat.shortComplex_shortExact S p.exact_subtype_ker_map Subtype.val_injective hp
    exact ⟨_, (hS.map_of_exact
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).singleTriangle_distinguished,
      rfl, ⟨ModuleCat.of Λ (LinearMap.ker p), inferInstance, rfl⟩,
      isIso_derivedHomTensorNatTrans_app_constantSingle_pi K M n⟩

end Etale

end AlgebraicGeometry
