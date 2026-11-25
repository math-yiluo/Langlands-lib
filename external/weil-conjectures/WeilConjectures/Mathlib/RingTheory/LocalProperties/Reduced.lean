/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Reducedness of tensor products with a localization

If `S` is a localization of `R`, then `K ⊗[k] S` is a localization of `K ⊗[k] R`, so it is
reduced as soon as `K ⊗[k] R` is.

## Main results

- `isReduced_tensorProduct_of_isLocalization`
-/

@[expose] public section

open TensorProduct

/-- If `S` is a localization of the `k`-algebra `R` and `K ⊗[k] R` is reduced, then so is
`K ⊗[k] S`, being a localization of `K ⊗[k] R`. -/
theorem isReduced_tensorProduct_of_isLocalization {k K R S : Type*} [CommRing k] [CommRing K]
    [CommRing R] [CommRing S] [Algebra k K] [Algebra k R] [Algebra k S] [Algebra R S]
    [IsScalarTower k R S] (M : Submonoid R) [IsLocalization M S] [IsReduced (K ⊗[k] R)] :
    IsReduced (K ⊗[k] S) := by
  let f : K ⊗[k] R →ₐ[K] K ⊗[k] S :=
    Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom k R S)
  let : Algebra (K ⊗[k] R) (K ⊗[k] S) := f.toRingHom.toAlgebra
  have : IsScalarTower K (K ⊗[k] R) (K ⊗[k] S) := .of_algebraMap_eq' f.comp_algebraMap.symm
  have := IsLocalization.tensorProduct_tensorProduct_right k K M S (by
    ext x
    simp [RingHom.algebraMap_toAlgebra, f])
  let M' : Submonoid (K ⊗[k] R) := M.map (Algebra.TensorProduct.includeRight (R := k) (A := K))
  exact isReduced_of_injective (IsLocalization.algEquiv M' (Localization M') (K ⊗[k] S)).symm
    (AlgEquiv.injective _)
