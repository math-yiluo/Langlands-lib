/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Descending a map to a local ring through a surjection

If `π : P →+* K` is surjective and `ρ : P →+* V` maps `RingHom.ker π` into the maximal
ideal of a local ring `V`, then the residue map of `ρ` factors through `π`
(`IsLocalRing.exists_comp_eq_residue_comp`).
-/

@[expose] public section

namespace IsLocalRing

/-- If `π : P →+* K` is surjective and `ρ : P →+* V` carries `RingHom.ker π` into the
maximal ideal of the local ring `V`, then `residue V ∘ ρ` factors through `π`. -/
theorem exists_comp_eq_residue_comp {P K V : Type*} [CommRing P] [CommRing K] [CommRing V]
    [IsLocalRing V] {π : P →+* K} (hπ : Function.Surjective π) (ρ : P →+* V)
    (hker : ∀ a ∈ RingHom.ker π, ρ a ∈ maximalIdeal V) :
    ∃ τ : K →+* ResidueField V, τ.comp π = (residue V).comp ρ := by
  refine ⟨(Ideal.Quotient.lift (RingHom.ker π) ((residue V).comp ρ) fun a ha ↦
      Ideal.Quotient.eq_zero_iff_mem.mpr (hker a ha)).comp
    ((RingHom.quotientKerEquivOfSurjective hπ).symm : K →+* P ⧸ RingHom.ker π), ?_⟩
  refine RingHom.ext fun a ↦ ?_
  have hmk : ((RingHom.quotientKerEquivOfSurjective hπ).symm : K →+* P ⧸ RingHom.ker π) (π a) =
      Ideal.Quotient.mk (RingHom.ker π) a := by
    apply (RingHom.quotientKerEquivOfSurjective hπ).injective
    rw [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact (RingHom.kerLift_mk π a).symm
  simp only [RingHom.comp_apply]
  rw [hmk, Ideal.Quotient.lift_mk, RingHom.comp_apply]

end IsLocalRing
