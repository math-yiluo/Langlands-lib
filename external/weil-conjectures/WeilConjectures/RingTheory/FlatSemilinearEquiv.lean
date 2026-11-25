/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat

/-! # Flatness under a simultaneous change of rings and modules -/

@[expose] public section

namespace Module.Flat

/-- Flatness is invariant under compatible ring and additive equivalences.
Source: transport of the tensor-injectivity definition of flatness;
Stacks Project, Algebra, Tag 02JO, localized comparison in the first proof paragraph.
(blueprint: lem-pc-flat-semilinear-equiv)
Proof: Regard N as an R-module by restricting along eR. The supplied additive
map becomes an R-linear equivalence, so flatness is preserved by
Module.Flat.equiv_iff. A ring equivalence and its inverse are flat ring maps.
Composition of flat modules in each direction identifies flatness of N over R
with flatness over S; the inverse identities give the required scalar towers. -/
theorem semilinearEquiv_iff
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (eR : R ≃+* S) (eM : M ≃+ N)
    (h : ∀ r m, eM (r • m) = eR r • eM m) : Flat R M ↔ Flat S N := by
  let : Algebra R S := eR.toRingHom.toAlgebra
  let : Module R N := Module.compHom N eR.toRingHom
  let e : M ≃ₗ[R] N := { eM with map_smul' := h }
  rw [equiv_iff e]
  constructor
  · intro hN
    let : Algebra S R := eR.symm.toRingHom.toAlgebra
    let : Flat R N := hN
    let : Flat S R := RingHom.Flat.of_bijective eR.symm.bijective
    let : IsScalarTower S R N := ⟨fun s r n ↦ by
      change eR (eR.symm s * r) • n = s • (eR r • n)
      rw [map_mul, eR.apply_symm_apply, mul_smul]⟩
    exact trans S R N
  · intro hN
    let : Flat S N := hN
    let : Flat R S := RingHom.Flat.of_bijective eR.bijective
    let : IsScalarTower R S N := ⟨fun r s n ↦ by
      change (eR r * s) • n = eR r • (s • n)
      exact mul_smul _ _ _⟩
    exact trans R S N

end Module.Flat
