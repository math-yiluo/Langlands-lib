/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness over a base ring survives algebra-module localization

Source: Stacks Project, Algebra, Lemma 10.39.18 (Tag 00HT), part (6), localization
argument (blueprint: lem-pc-affine-flat-module-localization-preserves-flatness).
-/

@[expose] public section

namespace Module.Flat

/-- (blueprint: lem-pc-affine-flat-module-localization-preserves-flatness)
Let `R → A` be a map of commutative rings, `M` an `A`-module flat over `R`, and `S` a
submonoid of `A`. Then `S⁻¹M`, regarded as an `R`-module through `A → S⁻¹A`, is flat over
`R` (Stacks Project, Algebra, Tag 00HT, part (6)).

For an injective map of `R`-modules `N₁ → N₂`, flatness of `M` makes
`M ⊗[R] N₁ → M ⊗[R] N₂` injective. This map is `A`-linear through `M`.
Localization at `S` preserves injectivity by exactness of module localization
(blueprint: lem-weil-pbc-localization-module-exact). The natural localization-tensor
identification (blueprint: lem-weil-pbc-localization-tensor-over-base) identifies this
localized map with `S⁻¹M ⊗[R] N₁ → S⁻¹M ⊗[R] N₂`. Thus tensoring with `S⁻¹M`
preserves every injective `R`-linear map, which is flatness by
(blueprint: def-weil-pbc-flat-ring-map). -/
theorem localizedModule_of_algebra {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] (S : Submonoid A) (hM : Module.Flat R M) :
    Module.Flat R (LocalizedModule S M) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  let g : M →ₗ[A] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  have hinj : Function.Injective (LinearMap.lTensor M N.subtype) :=
    hM.lTensor_preserves_injective_linearMap N.subtype N.subtype_injective
  have hinjA : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) := by
    simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hinj
  have hloc := IsLocalizedModule.map_injective S
    (TensorProduct.AlgebraTensorModule.rTensor R N g)
    (TensorProduct.AlgebraTensorModule.rTensor R P g)
    (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) hinjA
  rw [IsLocalizedModule.map_lTensor] at hloc
  simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hloc

end Module.Flat
