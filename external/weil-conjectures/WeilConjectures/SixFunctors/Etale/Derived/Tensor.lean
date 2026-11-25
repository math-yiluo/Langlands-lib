/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-!

# The derived tensor product of étale sheaves

Let `A` be a monoidal Grothendieck abelian coefficient category and let `X` be a scheme.
The category `Sheaf X.smallEtaleTopology A` of `A`-valued étale sheaves on `X` is then a
monoidal Grothendieck abelian category, so it has a derived category `D(X_ét)`, and the
K-flat machinery migrated from mathlib PR #25848 equips `D(X_ét)` with the *derived tensor
product* `- ⊗ᴸ -`, the total left derived functor of `- ⊗ -` in two variables.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensor` : the derived tensor product
  `- ⊗ᴸ - : D(X_ét) ⥤ D(X_ét) ⥤ D(X_ét)`, with scoped notation `(X)⊗ᴸ[A]`.
- `AlgebraicGeometry.Etale.derivedTensorRight` : tensoring on the right with a fixed
  complex, `K ↦ K ⊗ᴸ N`, and `AlgebraicGeometry.Etale.derivedTensorRightFunctor`, the same
  construction read as a functor of `N`.
- `AlgebraicGeometry.Etale.derivedTensorHom` : the tensor product `f ⊗ g` of two morphisms.

## Main results

- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor` : the derived tensor product
  really is the total left derived functor of the tensor product of étale sheaves, in two
  variables.

- `AlgebraicGeometry.Etale.additive_derivedTensor_obj`,
  `AlgebraicGeometry.Etale.additive_derivedTensor_flip_obj`,
  `AlgebraicGeometry.Etale.linear_derivedTensor_obj` and
  `AlgebraicGeometry.Etale.linear_derivedTensor_flip_obj` : the derived tensor product is
  additive and `Λ`-linear in each variable, by `DerivedCategory.monoidalPreadditive` and
  `DerivedCategory.monoidalLinear`.

- `AlgebraicGeometry.Etale.laxMonoidal_Q` : the localization functor
  `Q : C(X_ét) ⥤ D(X_ét)` is lax monoidal.

## Implementation notes

The monoidal structure on `Sheaf X.smallEtaleTopology A` is `Sheaf.monoidalCategory`, which
is a `local instance` in mathlib rather than a global one (it is only available once
`(J.W).IsMonoidal` holds). It is therefore activated by `attribute [local instance]` here, as
in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`. Note that the *type* of
`derivedTensor` does not mention the monoidal structure, so downstream files may use it
without re-activating the local instance.

That `D(X_ét)` is monoidal at all comes from
`DerivedCategory.hasDerivedMonoidalCategory` in
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`, which is why
the hypotheses below are exactly the ones that instance asks of the category of étale
sheaves: monoidal closed (so that tensoring preserves colimits) and admitting functorial
flat resolutions.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]

variable (X : Scheme.{u})

variable [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

namespace Etale

/-- The derived tensor product `- ⊗ᴸ - : D(X_ét) ⥤ D(X_ét) ⥤ D(X_ét)` on the unbounded
derived category of `A`-valued étale sheaves on `X`: the tensor product of the monoidal
structure on `D(X_ét)` obtained from the K-flat left derivability structure. -/
@[implicit_reducible]
noncomputable def derivedTensor :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  curriedTensor _

@[inherit_doc derivedTensor]
scoped notation "-⊗ᴸ-(" X ")[" A "]" => derivedTensor A X

/-- Tensoring on the right with a fixed complex `N` on `X`: the functor `K ↦ K ⊗ᴸ N` on
`D(X_ét)`. -/
noncomputable def derivedTensorRight
    (N : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (-⊗ᴸ-(X)[A]).flip.obj N

/-- `AlgebraicGeometry.Etale.derivedTensorRight` as a functor of the fixed complex: it sends
`N` to `K ↦ K ⊗ᴸ N`. -/
noncomputable def derivedTensorRightFunctor :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (-⊗ᴸ-(X)[A]).flip

@[simp]
lemma derivedTensorRightFunctor_obj (N : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedTensorRightFunctor A X).obj N = derivedTensorRight A X N :=
  rfl

/-- The derived tensor product acts on a morphism in its first variable by whiskering. -/
lemma derivedTensor_map_app {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K')
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).map f).app M = f ▷ M :=
  rfl

/-- The derived tensor product acts on a morphism in its second variable by whiskering. -/
lemma derivedTensor_obj_map (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : M ⟶ M') :
    ((derivedTensor A X).obj K).map f = K ◁ f :=
  rfl

noncomputable instance laxMonoidal_Q :
    (DerivedCategory.Q (C := Sheaf X.smallEtaleTopology A)).LaxMonoidal :=
  DerivedCategory.laxMonoidalQ (Sheaf X.smallEtaleTopology A)

noncomputable instance laxMonoidal_Qh :
    (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology A)).LaxMonoidal :=
  DerivedCategory.laxMonoidalQh (Sheaf X.smallEtaleTopology A)

instance isLeftDerivedFunctor₂_derivedTensor :
    -⊗ᴸ-(X)[A].IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)) :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor (Sheaf X.smallEtaleTopology A)

variable {X} in
/-- The tensor product `f ⊗ g` of two morphisms of `D(X_ét)`. -/
noncomputable def derivedTensorHom
    {K K₁ M M₁ : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K₁) (g : M ⟶ M₁) :
    ((derivedTensor A X).obj K).obj M ⟶ ((derivedTensor A X).obj K₁).obj M₁ :=
  ((derivedTensor A X).map f).app M ≫ ((derivedTensor A X).obj K₁).map g

variable {A X} in
/-- Composition of tensor products of morphisms. -/
@[reassoc]
lemma derivedTensorHom_comp
    {K K₁ K₂ M M₁ M₂ : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (f : K ⟶ K₁) (g : M ⟶ M₁) (f' : K₁ ⟶ K₂) (g' : M₁ ⟶ M₂) :
    derivedTensorHom A f g ≫ derivedTensorHom A f' g' = derivedTensorHom A (f ≫ f') (g ≫ g') := by
  simp only [derivedTensorHom, Category.assoc, Functor.map_comp, NatTrans.comp_app]
  rw [((derivedTensor A X).map f').naturality_assoc g]

variable {A X} in
/-- Tensor product of identities. -/
@[simp]
lemma derivedTensorHom_id (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    derivedTensorHom A (𝟙 K) (𝟙 M) = 𝟙 _ := by
  simp [derivedTensorHom]

section Linear

variable {A X} (K : DerivedCategory (Sheaf X.smallEtaleTopology A))

/-- Tensoring with a fixed object `K` of `D(X_ét)`, `M ↦ K ⊗ᴸ M`, is additive. -/
instance additive_derivedTensor_obj : ((derivedTensor A X).obj K).Additive :=
  inferInstanceAs (tensorLeft K).Additive

/-- Tensoring with a fixed object `K` of `D(X_ét)`, `M ↦ M ⊗ᴸ K`, is additive. -/
instance additive_derivedTensor_flip_obj : ((derivedTensor A X).flip.obj K).Additive :=
  inferInstanceAs (tensorRight K).Additive

variable (Λ : Type*) [Ring Λ] [Linear Λ A] [MonoidalLinear Λ A]

/-- If the tensor product of `A` is `Λ`-linear, tensoring with a fixed object `K` of `D(X_ét)`,
`M ↦ K ⊗ᴸ M`, is `Λ`-linear. -/
instance linear_derivedTensor_obj : ((derivedTensor A X).obj K).Linear Λ :=
  inferInstanceAs ((tensorLeft K).Linear Λ)

/-- If the tensor product of `A` is `Λ`-linear, tensoring with a fixed object `K` of `D(X_ét)`,
`M ↦ M ⊗ᴸ K`, is `Λ`-linear. -/
instance linear_derivedTensor_flip_obj : ((derivedTensor A X).flip.obj K).Linear Λ :=
  inferInstanceAs ((tensorRight K).Linear Λ)

end Linear

end Etale

end AlgebraicGeometry
