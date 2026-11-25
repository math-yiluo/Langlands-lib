/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Prescribed bases persist under a further principal localization

Source: Stacks Project, Algebra, Section 10.9 (localization of modules), and Tag 07C6.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Module.Basis

/-- A basis represented by specified original module elements persists on D(a*t).
Source: Stacks Project, Algebra, Section 10.9 (localization of modules), and Tag 07C6.
(blueprint: lem-weil-pbc-prescribed-basis-further-localization)

Proof: Give A[1/(a*t)] its A[1/a]-algebra structure, since a is a unit after
inverting a*t. Base change the given basis. Associativity of tensor products and
the localization-tensor equivalence identify this base change with
LocalizedModule.Away (a*t) M. The resulting basis vectors are m i divided by one,
as follows on elementary tensors. No finiteness, projectivity, smoothness or prime
hypothesis is needed. If a or t is nilpotent, the resulting zero ring and zero
module still admit the base changed basis. The empty index type is also covered. -/
theorem exists_prescribed_basis_away_mul
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type*} (a t : A) (m : ι → M)
    (b : Module.Basis ι (Localization.Away a) (LocalizedModule.Away a M))
    (hb : ∀ i, b i = LocalizedModule.mkLinearMap (Submonoid.powers a) M (m i)) :
    ∃ b' : Module.Basis ι (Localization.Away (a * t))
        (LocalizedModule.Away (a * t) M),
      ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers (a * t)) M (m i) :=
  by
  classical
  let B := Localization.Away a
  let C := Localization.Away (a * t)
  let : Algebra B C :=
    (IsLocalization.Away.awayToAwayRight (S := B) (P := C) a t).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' <| by
    ext x
    exact (IsLocalization.Away.awayToAwayRight_eq (S := B) (P := C) a t x).symm
  let e : (C ⊗[B] LocalizedModule.Away a M) ≃ₗ[C]
      LocalizedModule.Away (a * t) M :=
    (LinearEquiv.baseChange B C _ _ (LocalizedModule.equivTensorProduct
      (Submonoid.powers a) M)).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M).trans
        (LocalizedModule.equivTensorProduct (Submonoid.powers (a * t)) M).symm)
  refine ⟨(b.baseChange C).map e, ?_⟩
  intro i
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb]
  apply (LocalizedModule.equivTensorProduct (Submonoid.powers (a * t)) M).injective
  dsimp only [e]
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.baseChange_tmul, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.equivTensorProduct_apply_mk,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Localization.mk_one]
  rw [one_smul, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.equivTensorProduct_apply_mk, Localization.mk_one]

end Module.Basis
