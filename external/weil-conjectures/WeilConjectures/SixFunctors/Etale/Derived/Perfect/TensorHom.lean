/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual

/-!
# Internal hom out of a dualizable étale complex

Let `P` be a dualizable object of `D(X_ét)`, the rendering of "perfect over `Λ_X`" in this
repository (see `WeilConjectures.SixFunctors.Etale.Derived.Perfect`); a finite projective
`Λ_X`-module placed in degree `0` is the basic example. For every `N` the canonical map

`P^∨ ⊗ᴸ N ⟶ RHom(P, N)`

of the tensor–internal-hom adjunction is an isomorphism, natural in `P` and `N`, and the canonical
biduality map `P ⟶ P^∨∨` is an isomorphism. This is blueprint
`theorem-poincare-duality--5`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.coefficientDualTensorToDerivedHom`: the canonical map
  `P^∨ ⊗ᴸ N ⟶ RHom(P, N)`.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isIso_coefficientDualTensorToDerivedHom`
  (`theorem-poincare-duality--5`): it is an isomorphism for dualizable `P`.
- `AlgebraicGeometry.Etale.DerivedCategory.coefficientDualTensorToDerivedHom_naturality_left`,
  `AlgebraicGeometry.Etale.DerivedCategory.coefficientDualTensorToDerivedHom_naturality_right`
  (`theorem-poincare-duality--5`): it is natural in `P` and `N`.
- `AlgebraicGeometry.Etale.DerivedCategory.isIso_toIhomIhomUnit_of_isDualizable`
  (`theorem-poincare-duality--5`): the biduality map `P ⟶ P^∨∨` is an isomorphism.

## Implementation notes

The biduality map `P ⟶ P^∨∨` is built from a braiding
(`CategoryTheory.MonoidalClosed.toIhomIhomUnit`), and `D(X_ét)` only carries one up to
`Nonempty` (`DerivedCategory.nonempty_braidedCategory`); as for perfect point complexes
(`DerivedCategory.IsPerfect.isIso_toIhomIhomUnit`) the statement is made for an arbitrary
braiding. At the level of sheaves, biduality of a finite locally free module is
`SheafOfModules.isIso_bidual`.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace CategoryTheory.MonoidalClosed

/-- The comparison map `[X, 𝟙_ C] ⊗ Z ⟶ [X, Z]` is natural in `Z`. -/
lemma whiskerLeft_comp_ihomUnitTensorToIhom {C : Type*} [Category* C] [MonoidalCategory C]
    [MonoidalClosed C] (X : C) {Z Z' : C} (f : Z ⟶ Z') :
    (ihom X).obj (𝟙_ C) ◁ f ≫ ihomUnitTensorToIhom X Z' =
      ihomUnitTensorToIhom X Z ≫ (ihom X).map f := by
  rw [ihomUnitTensorToIhom, ihomUnitTensorToIhom, ← curry_natural_left, ← curry_natural_right]
  congr 1
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  simp

end CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X : Scheme.{u}}

namespace Etale.DerivedCategory

/-- The canonical map `P^∨ ⊗ᴸ N ⟶ RHom(P, N)` of the tensor–internal-hom adjunction: the
transpose of `P ⊗ᴸ (P^∨ ⊗ᴸ N) ≅ (P ⊗ᴸ P^∨) ⊗ᴸ N ⟶ Λ_X ⊗ᴸ N ≅ N`, built from the evaluation
(`CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`). -/
noncomputable def coefficientDualTensorToDerivedHom
    (P N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj ((coefficientDual A X).obj (op P))).obj N ⟶
      (RHom(X)[A].obj (op P)).obj N :=
  ihomUnitTensorToIhom P N

/-- Blueprint `theorem-poincare-duality--5`: Internal Hom with a finite projective
module.

For a dualizable `P` (perfect over `Λ_X`, e.g. a finite projective `Λ_X`-module) and every `N`,
the canonical map `P^∨ ⊗ᴸ N ⟶ RHom(P, N)` is an isomorphism. -/
theorem isIso_coefficientDualTensorToDerivedHom
    {P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hP : IsDualizable P)
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (coefficientDualTensorToDerivedHom P N) := by
  obtain ⟨_⟩ := hP
  obtain ⟨_⟩ := nonempty_exactPairing_swap P Pᘁ
  exact isIso_ihomUnitTensorToIhom Pᘁ P N

/-- Blueprint `theorem-poincare-duality--5`: Internal Hom with a finite projective
module, naturality in `N`. -/
theorem coefficientDualTensorToDerivedHom_naturality_right
    (P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {N N' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : N ⟶ N') :
    ((derivedTensor A X).obj ((coefficientDual A X).obj (op P))).map f ≫
        coefficientDualTensorToDerivedHom P N' =
      coefficientDualTensorToDerivedHom P N ≫ (RHom(X)[A].obj (op P)).map f := by
  exact whiskerLeft_comp_ihomUnitTensorToIhom P f

/-- Blueprint `theorem-poincare-duality--5`: Internal Hom with a finite projective
module, naturality in `P`. -/
theorem coefficientDualTensorToDerivedHom_naturality_left
    {P P' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (g : P ⟶ P')
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).map ((coefficientDual A X).map g.op)).app N ≫
        coefficientDualTensorToDerivedHom P N =
      coefficientDualTensorToDerivedHom P' N ≫ (RHom(X)[A].map g.op).app N := by
  change (pre g).app _ ▷ N ≫ curry _ = curry _ ≫ (pre g).app N
  rw [← curry_natural_left, curry_pre_app]
  congr 1
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    id_tensor_pre_app_comp_ev, comp_whiskerRight_assoc, associator_inv_naturality_left_assoc]

/-- Blueprint `theorem-poincare-duality--5`: Internal Hom with a finite projective
module, biduality.

For a dualizable `P` and any braiding of `D(X_ét)`, the canonical biduality map
`P ⟶ P^∨∨ = RHom(RHom(P, Λ_X), Λ_X)` is an isomorphism. -/
theorem isIso_toIhomIhomUnit_of_isDualizable
    [BraidedCategory (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))]
    {P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hP : IsDualizable P) :
    IsIso (toIhomIhomUnit P) := by
  obtain ⟨_⟩ := hP
  exact isIso_toIhomIhomUnit P

end Etale.DerivedCategory

end AlgebraicGeometry
