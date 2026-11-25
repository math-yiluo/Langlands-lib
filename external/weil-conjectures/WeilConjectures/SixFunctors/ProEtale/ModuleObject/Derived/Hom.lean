/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

/-!

# The derived internal hom of module objects over `Λ`

Let `Λ` be a commutative condensed ring and `X` a scheme, so that the derived category
`D(Mod_{Λ_X})` of module objects over the coefficient ring object `Λ_X = p_X^* Λ` carries
the derived tensor product `- ⊗ᴸ_{Λ_X} -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`. Under the
same hypotheses `D(Mod_{Λ_X})` is monoidal closed
(`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`), and this file defines the
*derived hom* `RHom_{Λ_X}(-, -)` of module objects to be the internal hom of that closed
structure, i.e. the right adjoint of the derived tensor product.

## Main definitions

- `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom` : the derived hom
  `RHom_{Λ_X}(-, -) : D(Mod_{Λ_X})ᵒᵖ ⥤ D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X})`, with scoped
  notation `RHom(X)⟦Λ⟧`.

## Main results

- `AlgebraicGeometry.ProEtale.CondensedRing.derivedTensorHomAdjunction₂` : the adjunction
  with parameter `- ⊗ᴸ_{Λ_X} - ⊣₂ RHom_{Λ_X}(-, -)`.

- `AlgebraicGeometry.ProEtale.CondensedRing.derivedTensorHomAdjunction` : its unary shadow,
  the adjunction `K ⊗ᴸ_{Λ_X} - ⊣ RHom_{Λ_X}(K, -)` for a fixed `K : D(Mod_{Λ_X})`.

## Implementation notes

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom`. The closedness of
`D(Mod_{Λ_X})` is the instance `DerivedCategory.monoidalClosed`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (X : Scheme.{u})

/-- The derived hom `RHom_{Λ_X}(-, -) : D(Mod_{Λ_X})ᵒᵖ ⥤ D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X})`
on the unbounded derived category of module objects over the coefficient ring object `Λ_X`:
the internal hom of the monoidal closed structure on `D(Mod_{Λ_X})`, i.e. the right adjoint
of the derived tensor product `- ⊗ᴸ_{Λ_X} -`. -/
@[implicit_reducible]
noncomputable def derivedHom :
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))ᵒᵖ ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  MonoidalClosed.internalHom

@[inherit_doc derivedHom]
scoped notation "RHom(" X ")⟦" Λ "⟧" => derivedHom Λ X

/-- The derived hom of module objects over `Λ_X` is right adjoint to the derived tensor
product, as an adjunction with a parameter: `- ⊗ᴸ_{Λ_X} - ⊣₂ RHom_{Λ_X}(-, -)`. -/
noncomputable def derivedTensorHomAdjunction₂ : -⊗ᴸ-(X)⟦Λ⟧ ⊣₂ RHom(X)⟦Λ⟧ :=
  MonoidalClosed.internalHomAdjunction₂

variable {X}

/-- For a fixed `K : D(Mod_{Λ_X})`, the derived tensor product `K ⊗ᴸ_{Λ_X} -` is left
adjoint to the derived hom `RHom_{Λ_X}(K, -)`. -/
noncomputable def derivedTensorHomAdjunction
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (-⊗ᴸ-(X)⟦Λ⟧).obj K ⊣ (RHom(X)⟦Λ⟧).obj (op K) :=
  (derivedTensorHomAdjunction₂ Λ X).adj K

/-- The derived hom `RHom_{Λ_X}(K, -)` is a right adjoint. -/
instance isRightAdjoint_derivedHom_obj
    (K : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))ᵒᵖ) :
    ((RHom(X)⟦Λ⟧).obj K).IsRightAdjoint :=
  (derivedTensorHomAdjunction Λ K.unop).isRightAdjoint

end AlgebraicGeometry.ProEtale.CondensedRing
