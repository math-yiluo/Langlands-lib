/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!

# Nearby cycles of a model

Let `S` be a trait with geometric generic point `η̄` and special point `s`. A *model* of a scheme
`X` with special fibre `X'` (`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel`) is a
scheme `𝒳` over `S` (the *total space*) together with
* the inclusion `j : 𝒳_η̄ ⟶ 𝒳` of its geometric generic fibre,
* the inclusion `i : X' ⟶ 𝒳` of its special fibre,
* a morphism `ε : 𝒳_η̄ ⟶ X` identifying the geometric generic fibre with the base change of `X`.

The *nearby cycles* of the model are the functor
```
Ψ = i^* Rj_* ε^* : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_{X'}})
```
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCycles`); for the constant
model `ε = 𝟙` they are the geometric nearby cycles `RΨ = ī^* Rj̄_*` of SGA 7 XIII, precomposed
with the pullback to the geometric generic fibre.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- A *model* of a scheme `X` with special fibre `X'` over a trait: a total space `𝒳` with the
inclusions `j : 𝒳_η̄ ⟶ 𝒳` of the geometric generic fibre and `i : X' ⟶ 𝒳` of the special fibre,
and the identification `ε : 𝒳_η̄ ⟶ X` of the geometric generic fibre with the base change
of `X`. -/
structure NearbyCyclesModel (X X' : Scheme.{u}) where
  /-- the total space `𝒳` over the trait. -/
  total : Scheme.{u}
  /-- the geometric generic fibre `𝒳_η̄`. -/
  generic : Scheme.{u}
  /-- the inclusion `j : 𝒳_η̄ ⟶ 𝒳` of the geometric generic fibre. -/
  j : generic ⟶ total
  /-- the inclusion `i : X' ⟶ 𝒳` of the special fibre. -/
  i : X' ⟶ total
  /-- the identification `ε : 𝒳_η̄ ⟶ X` of the geometric generic fibre with the base change of
  `X`. -/
  ε : generic ⟶ X

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

/-- The *nearby cycles* `Ψ = i^* Rj_* ε^*` of a model, on the unbounded derived categories of
module objects. -/
noncomputable def nearbyCycles :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
        (condensedRingObj Λ X')) :=
  L((M.ε)^*⟦Λ⟧) ⋙ R((M.j)_*⟦Λ⟧) ⋙ L((M.i)^*⟦Λ⟧)

variable {M} {Y Y' : Scheme.{u}}

/-- A *morphism of models* `M ⟶ N` over `f : X ⟶ Y` and `f' : X' ⟶ Y'`: morphisms of the total
spaces and of the geometric generic fibres compatible with `j`, `i` and `ε`. -/
structure Hom (M : NearbyCyclesModel X X') (N : NearbyCyclesModel Y Y') (f : X ⟶ Y)
    (f' : X' ⟶ Y') where
  /-- the morphism of total spaces. -/
  total : M.total ⟶ N.total
  /-- the morphism of geometric generic fibres. -/
  generic : M.generic ⟶ N.generic
  comm_j : generic ≫ N.j = M.j ≫ total
  comm_i : f' ≫ N.i = M.i ≫ total
  comm_ε : generic ≫ N.ε = M.ε ≫ f

/-- The identity morphism of a model, over the identities. -/
@[simps]
def Hom.id (M : NearbyCyclesModel X X') : M.Hom M (𝟙 X) (𝟙 X') where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by rw [Category.id_comp, Category.comp_id]
  comm_i := by rw [Category.id_comp, Category.comp_id]
  comm_ε := by rw [Category.id_comp, Category.comp_id]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
