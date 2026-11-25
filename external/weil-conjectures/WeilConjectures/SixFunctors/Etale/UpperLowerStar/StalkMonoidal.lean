/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!

# Stalks of étale sheaves commute with the tensor product

Let `A` be a closed braided monoidal Grothendieck abelian category, for example
`ModuleCat Λ` for a commutative ring `Λ`, and let `s : Spec Ω ⟶ X` be a geometric point of a
scheme `X`. The stalk functor at `s` on `A`-valued étale sheaves is strong monoidal: the stalk
of a tensor product of sheaves is the tensor product of the stalks, `(F ⊗ G)_s ≅ F_s ⊗ G_s`,
naturally in `F` and `G`, and the stalk of the unit sheaf is the unit of `A`.

The site-general input is Mathlib's monoidal instance on
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` (in
`Mathlib.CategoryTheory.Sites.Point.Monoidal`): the presheaf fibre is a filtered colimit, the
tensor product of `A` commutes with colimits in each variable (tensoring is a left adjoint,
as `A` is closed and braided), and the fibre of the sheafification of a presheaf is the
presheaf fibre. That instance is stated for `CategoryTheory.Sheaf.monoidalCategory`, which is
what the project's global monoidal structure `AlgebraicGeometry.Etale.sheafMonoidalCategory`
of `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs` unfolds to, so it
applies to that structure directly. We use the universe-lifted point
`(pointSmallEtale s).ulift`, the form of the stalk used with
`AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso` and with the conservative family
`isConservativeFamilyOfPoints_ulift_pointSmallEtale`.

## Main results

- `AlgebraicGeometry.Etale.sheafFiberTensorIso`: `(F ⊗ G)_s ≅ F_s ⊗ G_s`.
- `AlgebraicGeometry.Etale.sheafFiberTensorIso_hom_naturality`: its naturality in `F` and `G`.
- `AlgebraicGeometry.Etale.sheafFiberUnitIso`: `(𝟙_)_s ≅ 𝟙_`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

namespace Etale

/-- The stalk of a tensor product of `A`-valued étale sheaves at a geometric point `s` is the
tensor product of the stalks: `(F ⊗ G)_s ≅ F_s ⊗ G_s`. This is the inverse of the tensorator of
the monoidal functor `CategoryTheory.GrothendieckTopology.Point.sheafFiber`. -/
noncomputable def sheafFiberTensorIso (F G : Sheaf X.smallEtaleTopology A) :
    (pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj (F ⊗ G) ≅
      (pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj F ⊗
        (pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj G :=
  (Functor.Monoidal.μIso _ F G).symm

@[simp]
lemma sheafFiberTensorIso_hom (F G : Sheaf X.smallEtaleTopology A) :
    (sheafFiberTensorIso s F G).hom =
      Functor.OplaxMonoidal.δ (pointSmallEtale s).ulift.{u + 1}.sheafFiber F G :=
  rfl

@[simp]
lemma sheafFiberTensorIso_inv (F G : Sheaf X.smallEtaleTopology A) :
    (sheafFiberTensorIso s F G).inv =
      Functor.LaxMonoidal.μ (pointSmallEtale s).ulift.{u + 1}.sheafFiber F G :=
  rfl

/-- Naturality of `sheafFiberTensorIso` in both variables:
```
  (F ⊗ G)_s ---(f ⊗ g)_s---> (F' ⊗ G')_s
     |                            |
   iso.hom                    iso.hom
     v                            v
  F_s ⊗ G_s ---f_s ⊗ g_s---> F'_s ⊗ G'_s
```
-/
@[reassoc]
lemma sheafFiberTensorIso_hom_naturality {F F' G G' : Sheaf X.smallEtaleTopology A}
    (f : F ⟶ F') (g : G ⟶ G') :
    (pointSmallEtale s).ulift.{u + 1}.sheafFiber.map (f ⊗ₘ g) ≫
        (sheafFiberTensorIso s F' G').hom =
      (sheafFiberTensorIso s F G).hom ≫
        ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.map f ⊗ₘ
          (pointSmallEtale s).ulift.{u + 1}.sheafFiber.map g) := by
  simp

variable (A) in
/-- The stalk of the unit `A`-valued étale sheaf at a geometric point is the unit of `A`. -/
noncomputable def sheafFiberUnitIso :
    (pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj (𝟙_ (Sheaf X.smallEtaleTopology A)) ≅
      𝟙_ A :=
  (Functor.Monoidal.εIso _).symm

@[simp]
lemma sheafFiberUnitIso_hom :
    (sheafFiberUnitIso A s).hom =
      Functor.OplaxMonoidal.η ((pointSmallEtale s).ulift.{u + 1}.sheafFiber (A := A)) :=
  rfl

@[simp]
lemma sheafFiberUnitIso_inv :
    (sheafFiberUnitIso A s).inv =
      Functor.LaxMonoidal.ε ((pointSmallEtale s).ulift.{u + 1}.sheafFiber (A := A)) :=
  rfl

end Etale

end AlgebraicGeometry
