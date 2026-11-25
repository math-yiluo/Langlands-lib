/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Filtration

/-! # Artin--Rees bound for images of reduced kernels

Source: Stacks Project, Lemma 087X, proof of claim (a).
(blueprint: new-adic-kernel-image-bound).
-/

@[expose] public section

universe u v w

namespace LinearMap

/-- The image of the preimage of a high ideal power in a fixed quotient is the image
of the actual kernel, with a bound uniform in the quotient level.

Source: Stacks Project, Lemma 087X, proof of claim (a), and Algebra, Lemma 00IN.
(blueprint: new-adic-kernel-image-bound).

Proof: Apply Artin--Rees to the range of f in N and obtain c. If f(x) belongs to
I^(l+1)N, it belongs to I^(l+1-c) range(f), hence has a lift y in I^(l+1-c)M.
For l >= m+c this lift is in I^(m+1)M. Thus x-y is in ker(f) and has the same
class as x in M/I^(m+1)M. Conversely every kernel element maps into every ideal
power. The two inclusions prove the asserted equality. This also treats zero
modules and the zero and unit ideals, without any nontriviality hypothesis. -/
theorem adic_kernel_image_bound {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    ∃ c : ℕ, ∀ (l m : ℕ), m + c ≤ l →
      ((I ^ (l + 1) • (⊤ : Submodule R N)).comap f).map
          (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ =
        f.ker.map (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul f.range
  refine ⟨c, fun l m h ↦ ?_⟩
  apply le_antisymm
  · rintro z ⟨x, hx, rfl⟩
    have hx' : f x ∈ I ^ (l + 1) • (⊤ : Submodule R N) ⊓ f.range :=
      ⟨hx, ⟨x, rfl⟩⟩
    rw [hc (l + 1) (by omega)] at hx'
    have hy' : f x ∈ (I ^ (l + 1 - c) • (⊤ : Submodule R M)).map f := by
      rw [Submodule.map_smul'', Submodule.map_top]
      have hle : I ^ (l + 1 - c) •
          (I ^ c • (⊤ : Submodule R N) ⊓ f.range) ≤ I ^ (l + 1 - c) • f.range :=
        smul_mono_right _ inf_le_right
      exact hle hx'
    obtain ⟨y, hy, hfy⟩ := hy'
    have hym : y ∈ I ^ (m + 1) • (⊤ : Submodule R M) :=
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) hy
    refine ⟨x - y, ?_, ?_⟩
    · change f (x - y) = 0
      rw [map_sub, hfy, sub_self]
    · rw [map_sub]
      have hy0 : (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ y = 0 := by
        exact (Submodule.Quotient.mk_eq_zero _).mpr hym
      rw [hy0, sub_zero]
  · apply Submodule.map_mono
    intro x hx
    change f x ∈ I ^ (l + 1) • (⊤ : Submodule R N)
    rw [LinearMap.mem_ker.mp hx]
    exact Submodule.zero_mem _

end LinearMap
