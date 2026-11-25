/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Tensor products of families of representations

For a family of representations `ρs i` of a monoid `G` on `k`-modules `V i`, the representation
`Representation.piTprod ρs` of `G` on the tensor product `⨂ i, V i` acts diagonally,
`g (⊗ᵢ vᵢ) = ⊗ᵢ g vᵢ`.

## Main definitions

- `Representation.piTprod`: the tensor product of a family of representations.
- `Representation.Equiv.piTprodCongr`: tensor products of equivalent families are equivalent.
- `Representation.piTprodSuccEquiv`: the tensor product over `Fin (t + 1)` is the tensor product
  over `Fin t` tensored with the last factor.
-/

@[expose] public section

open PiTensorProduct
open scoped TensorProduct

namespace Representation

variable {k G ι : Type*} [CommSemiring k] [Monoid G] {V V' : ι → Type*}
  [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)] [∀ i, AddCommMonoid (V' i)]
  [∀ i, Module k (V' i)]

/-- The tensor product `⨂ i, V i` of a family of representations, with the diagonal action
`g (⊗ᵢ vᵢ) = ⊗ᵢ g vᵢ`. -/
noncomputable def piTprod (ρs : ∀ i, Representation k G (V i)) :
    Representation k G (⨂[k] i, V i) where
  toFun g := PiTensorProduct.map fun i ↦ ρs i g
  map_one' := by
    simp only [map_one]
    exact PiTensorProduct.map_one
  map_mul' g h := by
    simp only [map_mul]
    exact PiTensorProduct.map_mul _ _

@[simp]
theorem piTprod_apply_tprod (ρs : ∀ i, Representation k G (V i)) (g : G) (f : ∀ i, V i) :
    piTprod ρs g (⨂ₜ[k] i, f i) = ⨂ₜ[k] i, ρs i g (f i) :=
  PiTensorProduct.map_tprod _ _

variable {ρs : ∀ i, Representation k G (V i)} {σs : ∀ i, Representation k G (V' i)}

/-- Tensor products of equivalent families of representations are equivalent. -/
noncomputable def Equiv.piTprodCongr (e : ∀ i, (ρs i).Equiv (σs i)) :
    (piTprod ρs).Equiv (piTprod σs) :=
  .mk (PiTensorProduct.congr fun i ↦ (e i).toLinearEquiv) fun g ↦ by
    refine PiTensorProduct.ext (MultilinearMap.ext fun f ↦ ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, piTprod_apply_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    exact LinearMap.congr_fun ((e i).isIntertwining' g) (f i)

end Representation

namespace Representation

variable {k G : Type*} [CommSemiring k] [Monoid G] {t : ℕ} {V : Fin (t + 1) → Type*}
  [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]

/-- The tensor product of a family of representations indexed by `Fin (t + 1)` is the tensor
product of the first `t` of them, tensored with the last one. -/
noncomputable def piTprodSuccEquiv (ρs : ∀ i, Representation k G (V i)) :
    (piTprod ρs).Equiv ((piTprod fun i : Fin t ↦ ρs i.castSucc).tprod (ρs (Fin.last t))) :=
  .mk ((reindex k V finSumFinEquiv.symm).trans ((tmulEquivDep k
    (fun j ↦ V (finSumFinEquiv j))).symm.trans
      (TensorProduct.congr (LinearEquiv.refl k _) (subsingletonEquiv (0 : Fin 1))))) fun g ↦ by
    refine PiTensorProduct.ext (MultilinearMap.ext fun f ↦ ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, piTprod_apply_tprod, LinearEquiv.trans_apply]
    rw [reindex_tprod, reindex_tprod]
    erw [tmulEquivDep_symm_apply, tmulEquivDep_symm_apply]
    rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul, tprod_apply, TensorProduct.map_tmul]
    congr 1
    · exact (piTprod_apply_tprod (fun i : Fin t ↦ ρs i.castSucc) g _).symm
    · exact (subsingletonEquiv_apply_tprod (ι := Fin 1) _ _).trans
        (congrArg (ρs (Fin.last t) g) (subsingletonEquiv_apply_tprod (ι := Fin 1) _ _)).symm

end Representation

namespace Representation

variable {k G ι : Type*} [CommSemiring k] [Monoid G] [IsEmpty ι] {V : ι → Type*}
  [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]

/-- The tensor product of an empty family of representations is the trivial representation on
`k`. -/
noncomputable def piTprodIsEmptyEquiv (ρs : ∀ i, Representation k G (V i)) :
    (piTprod ρs).Equiv (trivial k G k) :=
  .mk (isEmptyEquiv ι) fun g ↦ by
    refine PiTensorProduct.ext (MultilinearMap.ext fun f ↦ ?_)
    simp

end Representation
