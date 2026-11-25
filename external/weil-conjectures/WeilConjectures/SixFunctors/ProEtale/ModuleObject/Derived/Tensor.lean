/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!

# The derived tensor product of module objects over `Λ`

Let `Λ` be a commutative condensed ring and `X` a scheme. The category `Mod_{Λ_X}` of
module objects over the coefficient ring object `Λ_X = p_X^* Λ` of abelian pro-étale
sheaves on `X` is a closed symmetric monoidal Grothendieck abelian category for the relative
tensor product `⊗_{Λ_X}` (`WeilConjectures.CategoryTheory.ModuleObjects`), so its derived
category `D(Mod_{Λ_X})` carries the *derived tensor product* `- ⊗ᴸ_{Λ_X} -`, the total
left derived functor of `⊗_{Λ_X}` in two variables, computed on K-flat resolutions
(`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`).

## Main definitions

- `AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor` : the derived tensor product
  `- ⊗ᴸ_{Λ_X} - : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X})`, with scoped notation
  `-⊗ᴸ-(X)⟦Λ⟧`.

## Main results

- `AlgebraicGeometry.ProEtale.CondensedRing.isLeftDerivedFunctor₂_derivedTensor` : the
  derived tensor product is the total left derived functor of the relative tensor product of
  module objects, in two variables.

- `AlgebraicGeometry.ProEtale.CondensedRing.laxMonoidal_Q` : the localization functor
  `Q : C(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X})` is lax monoidal.

## Implementation notes

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`. The monoidal structure
on `D(Mod_{Λ_X})` is the instance `Mod.derivedMonoidalCategory`, which rests on the
inputs of `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` and
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`; the *type* of
`derivedTensor` does not mention it.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (X : Scheme.{u})

/-- The derived tensor product
`- ⊗ᴸ_{Λ_X} - : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X})` on the unbounded derived
category of module objects over the coefficient ring object `Λ_X`: the tensor product of the
monoidal structure on `D(Mod_{Λ_X})` obtained from the K-flat left derivability structure. -/
@[implicit_reducible]
noncomputable def derivedTensor :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  curriedTensor _

@[inherit_doc derivedTensor]
scoped notation "-⊗ᴸ-(" X ")⟦" Λ "⟧" => derivedTensor Λ X

noncomputable instance laxMonoidal_Q :
    (DerivedCategory.Q (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))).LaxMonoidal :=
  Mod.laxMonoidalQ

noncomputable instance laxMonoidal_Qh :
    (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))).LaxMonoidal :=
  inferInstance

/-- The derived tensor product of module objects over `Λ_X` is the total left derived
functor of the relative tensor product `⊗_{Λ_X}` of complexes of module objects, in two
variables. -/
instance isLeftDerivedFunctor₂_derivedTensor :
    -⊗ᴸ-(X)⟦Λ⟧.IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) (ComplexShape.up ℤ)) :=
  Mod.isLeftDerivedFunctor₂_curriedTensor

end AlgebraicGeometry.ProEtale.CondensedRing
