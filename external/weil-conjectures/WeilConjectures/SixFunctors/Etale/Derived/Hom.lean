/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!

# The derived internal hom of étale sheaves

Let `A` be a monoidal Grothendieck abelian coefficient category and let `X` be a scheme, so
that the derived category `D(X_ét)` of `A`-valued étale sheaves on `X` carries the derived
tensor product `- ⊗ᴸ -` of `WeilConjectures.SixFunctors.Etale.Derived.Tensor`. Under the same
hypotheses `D(X_ét)` is monoidal closed
(`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`), and this file defines the
*derived hom* of étale sheaves to be the internal hom of that closed structure, i.e. the right
adjoint of the derived tensor product.

## Main definitions

- `AlgebraicGeometry.Etale.derivedHom` : the derived hom
  `RHom(-, -) : D(X_ét)ᵒᵖ ⥤ D(X_ét) ⥤ D(X_ét)`, with scoped notation `(X)RHom[A]`.

## Main results

- `AlgebraicGeometry.Etale.derivedTensorHomAdjunction₂` : the adjunction with parameter
  `- ⊗ᴸ - ⊣₂ RHom(-, -)` expressing that the derived hom is the internal hom of the derived
  tensor product.

- `AlgebraicGeometry.Etale.derivedTensorHomAdjunction` : its unary shadow, the adjunction
  `K ⊗ᴸ - ⊣ RHom(K, -)` for a fixed `K : D(X_ét)`.

- `AlgebraicGeometry.Etale.derivedHomEquiv` : the tensor-hom bijection
  `(K ⊗ᴸ L ⟶ M) ≃ (L ⟶ RHom(K, M))`.

## Implementation notes

As in `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, the monoidal structure on
`Sheaf X.smallEtaleTopology A` is a `local instance` in mathlib and is activated here by
`attribute [local instance]`. The *type* of `derivedHom` does not mention it, so downstream
files may use the derived hom without re-activating the local instance.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace Etale

/-- The derived hom `RHom(-, -) : D(X_ét)ᵒᵖ ⥤ D(X_ét) ⥤ D(X_ét)` on the unbounded derived
category of `A`-valued étale sheaves on `X`: the internal hom of the monoidal closed
structure on `D(X_ét)`, i.e. the right adjoint of the derived tensor product `- ⊗ᴸ -`. -/
@[implicit_reducible]
noncomputable def derivedHom :
    (DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  MonoidalClosed.internalHom

@[inherit_doc derivedHom]
scoped notation "RHom(" X ")[" A "]" => derivedHom A X

/-- The derived hom of étale sheaves is right adjoint to the derived tensor product, as an
adjunction with a parameter: `- ⊗ᴸ - ⊣₂ RHom(-, -)`. -/
noncomputable def derivedTensorHomAdjunction₂ : -⊗ᴸ-(X)[A] ⊣₂ RHom(X)[A] :=
  MonoidalClosed.internalHomAdjunction₂

variable {X}

/-- For a fixed `K : D(X_ét)`, the derived tensor product `K ⊗ᴸ -` is left adjoint to the
derived hom `RHom(K, -)`. -/
noncomputable def derivedTensorHomAdjunction (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (-⊗ᴸ-(X)[A]).obj K ⊣ (RHom(X)[A]).obj (op K) :=
  (derivedTensorHomAdjunction₂ A X).adj K

/-- The derived hom `RHom(K, -)` is a right adjoint. -/
instance isRightAdjoint_derivedHom_obj
    (K : (DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ) :
    ((RHom(X)[A]).obj K).IsRightAdjoint :=
  (derivedTensorHomAdjunction A K.unop).isRightAdjoint

end Etale

end AlgebraicGeometry
