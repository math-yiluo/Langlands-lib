/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
import WeilConjectures.RingTheory.SingularIdealMapEquiv

@[expose] public section

universe u v w

namespace Algebra

/-- Precomposition with an algebra equivalence preserves the extended singular ideal.
Source: Stacks Project, Smoothing Ring Maps, Situation 07F7
(blueprint: lem-weil-pbc-popescu-ideal-comp-equiv).
Proof: Applying singularIdeal_map_equiv_le to the equivalence and its inverse gives
equality of the transported singular ideals. Ideal maps compose, so their images in
the target agree; taking radicals proves the result. -/
theorem popescuIdeal_comp_equiv
    {R : Type u} {A : Type v} {B : Type w} {Λ : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing Λ]
    [Algebra R A] [Algebra R B] [Algebra R Λ]
    (α : A →ₐ[R] Λ) (e : B ≃ₐ[R] A) : popescuIdeal (α.comp e.toAlgHom) =
      popescuIdeal α := by
  have hsing : Ideal.map e.toRingHom (singularIdeal R B) = singularIdeal R A := by
    apply le_antisymm (singularIdeal_map_equiv_le e)
    have h := Ideal.map_mono (f := e.toRingHom) (singularIdeal_map_equiv_le e.symm)
    have hid : e.toRingHom.comp e.symm.toRingHom = RingHom.id A := by
      apply RingHom.ext
      intro x
      exact e.apply_symm_apply x
    simpa only [Ideal.map_map, hid, Ideal.map_id] using h
  unfold popescuIdeal
  change (Ideal.map (α.toRingHom.comp e.toRingHom) (singularIdeal R B)).radical = _
  rw [← Ideal.map_map, hsing]

end Algebra
