/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Ab

/-!
# The forgetful functor from modules to abelian groups is lax monoidal

For a commutative ring `R`, the forgetful functor `ModuleCat R ⥤ Ab` is lax monoidal for the
tensor product `⊗[ℤ]` of abelian groups (`AddCommGrpCat.monoidalCategory`): the tensorator is
the canonical surjection `M ⊗[ℤ] N → M ⊗[R] N` and the unit is `ℤ → R`, `n ↦ n • 1`.
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory TensorProduct

namespace ModuleCat

variable (R : Type v) [CommRing R]

/-- The canonical map `M ⊗[ℤ] N → M ⊗[R] N`. -/
noncomputable def intTensorToTensor (M N : ModuleCat.{v} R) :
    (forget₂ (ModuleCat.{v} R) Ab.{v}).obj M ⊗ (forget₂ (ModuleCat.{v} R) Ab.{v}).obj N ⟶
      (forget₂ (ModuleCat.{v} R) Ab.{v}).obj (M ⊗ N) :=
  AddCommGrpCat.ofHom (TensorProduct.lift
    (((TensorProduct.mk R M N).restrictScalars₁₂ ℤ ℤ))).toAddMonoidHom

@[simp]
lemma intTensorToTensor_tmul (M N : ModuleCat.{v} R) (m : M) (n : N) :
    (intTensorToTensor R M N).hom (m ⊗ₜ[ℤ] n) = m ⊗ₜ[R] n :=
  rfl

/-- The unit `ℤ → R`, `n ↦ n • 1`. -/
noncomputable def intToUnit :
    𝟙_ Ab.{v} ⟶ (forget₂ (ModuleCat.{v} R) Ab.{v}).obj (𝟙_ (ModuleCat.{v} R)) :=
  AddCommGrpCat.ofHom ((zmultiplesHom R 1).comp AddEquiv.ulift.toAddMonoidHom)

/-- The forgetful functor `ModuleCat R ⥤ Ab` is lax monoidal. -/
noncomputable instance laxMonoidalForget₂Ab :
    (forget₂ (ModuleCat.{v} R) Ab.{v}).LaxMonoidal where
  ε := intToUnit R
  μ := intTensorToTensor R
  μ_natural_left _ _ := AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)
  μ_natural_right _ _ := AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)
  associativity _ _ _ := AddCommGrpCat.hom_ext_toIntLinearMap
    (TensorProduct.ext_threefold fun _ _ _ ↦ rfl)
  left_unitality X := AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun n (x : X) ↦
    (rfl : _ = n.down • x).trans (smul_one_smul R n.down x).symm)
  right_unitality X := AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun (x : X) n ↦
    (rfl : _ = n.down • x).trans (smul_one_smul R n.down x).symm)

end ModuleCat
