/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!

# The external Hom map

For two complexes `E₁, L₁` on `Z₁` and `E₂, L₂` on `Z₂` over a base `B`, the *external Hom map*
of `lemma-external-duality-trace-morphism` (iii) (`lemma-external-duality-trace-morphism`)

`β : RHom(E₁, L₁) ⊠ RHom(E₂, L₂) ⟶ RHom(E₁ ⊠ E₂, L₁ ⊠ L₂)`

is the tensor–Hom transpose of the two evaluations, with the tensor symmetry (the Koszul
braiding of the derived category) and its signs:

`(E₁ ⊠ E₂) ⊗ᴸ (RHom(E₁, L₁) ⊠ RHom(E₂, L₂)) ≅ (E₁ ⊗ᴸ RHom(E₁, L₁)) ⊠ (E₂ ⊗ᴸ RHom(E₂, L₂))
  ⟶ L₁ ⊠ L₂`.

## Main definitions

- `AlgebraicGeometry.Etale.externalHomMap` (`lemma-external-duality-trace-morphism` (iii)): the map
`β`.

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

universe u' u

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

/-- Blueprint `lemma-external-duality-trace-morphism` (iii), `lemma-external-duality-trace-morphism`
(iii): the external Hom map

`β : RHom(E₁, L₁) ⊠ RHom(E₂, L₂) ⟶ RHom(E₁ ⊠ E₂, L₁ ⊠ L₂)`

for `Eᵢ, Lᵢ ∈ D(Zᵢ_ét)` and `cᵢ : Zᵢ ⟶ B`, the external products being taken over `B`. It is the
tensor–Hom transpose of the two evaluations
(`CategoryTheory.MonoidalClosed.externalIhomMap` for the monoidal functors `Lp₁^*`, `Lp₂^*`),
with the tensor symmetry the Koszul braiding of `D((Z₁ ×_B Z₂)_ét)`
(`DerivedCategory.braidedCategory'`). -/
noncomputable def externalHomMap {B Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ B) (c₂ : Z₂ ⟶ B)
    (E₁ L₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology A))
    (E₂ L₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology A)) :
    externalProduct A c₁ c₂ ((RHom(Z₁)[A].obj (op E₁)).obj L₁) ((RHom(Z₂)[A].obj (op E₂)).obj L₂) ⟶
      (RHom(pullback c₁ c₂)[A].obj (op (externalProduct A c₁ c₂ E₁ E₂))).obj
        (externalProduct A c₁ c₂ L₁ L₂) :=
  letI := _root_.DerivedCategory.braidedCategory' (Sheaf (pullback c₁ c₂).smallEtaleTopology A)
  letI := leftDerivedUpperStarMonoidal A (pullback.fst c₁ c₂)
  letI := leftDerivedUpperStarMonoidal A (pullback.snd c₁ c₂)
  MonoidalClosed.externalIhomMap (L((pullback.fst c₁ c₂)^*[A])) (L((pullback.snd c₁ c₂)^*[A]))
    E₁ L₁ E₂ L₂

end Etale

end AlgebraicGeometry
