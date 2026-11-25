/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# The monoidal structure of `D(X_ét)` in terms of the derived tensor product

The derived tensor product `AlgebraicGeometry.Etale.derivedTensor` is the tensor product of
the monoidal structure on `D(X_ét)`. This file restates the associator, the left unitor, the
symmetry, invertibility and perfectness of pairings in terms of `derivedTensor`, for a general
coefficient category `A`.

## Implementation notes

Statements about a concrete coefficient category such as `ModuleCat Λ` should use these
declarations rather than `α_`, `λ_`, `ρ_`, `CategoryTheory.IsInvertible` or
`CategoryTheory.MonoidalClosed.IsPerfectPairing` directly. There, the monoidal instance on
`D(X_ét)` found by instance search is a different term from the one inside `derivedTensor`.
The two are equal, but the kernel does not decide this in reasonable time: already
`𝟙 (K ⊗ M)`, or `rfl : (K ⊗ᴸ M) = K ⊗ M`, hits a deterministic timeout. Over a general `A`
the comparison is immediate, and specialising the declarations below to `A = ModuleCat Λ`
involves no comparison at all.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensorAssociator`: `(K ⊗ᴸ M) ⊗ᴸ N ≅ K ⊗ᴸ (M ⊗ᴸ N)`.
- `AlgebraicGeometry.Etale.derivedTensorLeftUnitor`: `Λ_X ⊗ᴸ K ≅ K`.
- `AlgebraicGeometry.Etale.derivedTensorLeftUnitorNatIso`: `Λ_X ⊗ᴸ - ≅ 𝟭`.
- `AlgebraicGeometry.Etale.derivedTensorRightUnitor`: `K ⊗ᴸ Λ_X ≅ K`.
- `AlgebraicGeometry.Etale.IsPerfectPairing`: perfectness of a pairing `C ⊗ᴸ D ⟶ Λ_X`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`: the symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K`.
- `AlgebraicGeometry.Etale.isPerfectPairing_iff`,
  `AlgebraicGeometry.Etale.isInvertible_iff_exists_derivedTensor`: the comparison with
  `CategoryTheory.MonoidalClosed.IsPerfectPairing` and `CategoryTheory.IsInvertible`.
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

/-- The associator `(K ⊗ᴸ M) ⊗ᴸ N ≅ K ⊗ᴸ (M ⊗ᴸ N)` of the derived tensor product. -/
noncomputable def derivedTensorAssociator
    (K M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj (((derivedTensor A X).obj K).obj M)).obj N ≅
      ((derivedTensor A X).obj K).obj (((derivedTensor A X).obj M).obj N) :=
  α_ K M N

/-- `AlgebraicGeometry.Etale.derivedTensorAssociator` is the associator of `D(X_ét)`. -/
lemma derivedTensorAssociator_eq (K M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    derivedTensorAssociator A X K M N = α_ K M N :=
  rfl

/-- The left unitor `Λ_X ⊗ᴸ K ≅ K` of the derived tensor product, `Λ_X = 𝟙_` being the
constant complex. -/
noncomputable def derivedTensorLeftUnitor
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj (𝟙_ _)).obj K ≅ K :=
  λ_ K

/-- The left unitor `Λ_X ⊗ᴸ K ≅ K` of the derived tensor product, as a natural isomorphism
`Λ_X ⊗ᴸ - ≅ 𝟭`. -/
noncomputable def derivedTensorLeftUnitorNatIso :
    (derivedTensor A X).obj (𝟙_ _) ≅ 𝟭 (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  NatIso.ofComponents (derivedTensorLeftUnitor A X) fun f ↦ leftUnitor_naturality f

/-- The right unitor `K ⊗ᴸ Λ_X ≅ K` of the derived tensor product, `Λ_X = 𝟙_` being the
constant complex. -/
noncomputable def derivedTensorRightUnitor
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj K).obj (𝟙_ _) ≅ K :=
  ρ_ K

/-- `AlgebraicGeometry.Etale.derivedTensorRightUnitor` is the right unitor of `D(X_ét)`. -/
lemma derivedTensorRightUnitor_eq (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    derivedTensorRightUnitor A X K = ρ_ K :=
  rfl

/-- The symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the derived tensor product, natural in both variables:
an isomorphism between `- ⊗ᴸ -` and the flipped bifunctor `(K, M) ↦ M ⊗ᴸ K`. The derived
tensor product is symmetric monoidal (blueprint `theorem-f-shriek-ell-adic-coefficients--4`, remark
`rem-sf-summary`); this is the existence of its symmetry.

It is the braiding of `D(X_ét)` given by `DerivedCategory.nonempty_braidedCategory`. -/
theorem nonempty_iso_derivedTensor_flip :
    Nonempty (derivedTensor A X ≅ (derivedTensor A X).flip) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology A)
  -- `curriedBraidingNatIso` is generic in the category, so the kernel does not check the
  -- naturality of the braiding in `D(X_ét)` (which took about 50s).
  exact ⟨BraidedCategory.curriedBraidingNatIso _⟩

variable {A X}

/-- Blueprint `definition-perfect-pairing--1`: Perfect derived pairing.

A pairing `b : C ⊗ᴸ D ⟶ Λ_X` in `D(X_ét)` is *perfect* if its tensor–internal-hom adjoint
`D ⟶ RHom(C, Λ_X)` is an isomorphism.

This is `CategoryTheory.MonoidalClosed.IsPerfectPairing` (see
`AlgebraicGeometry.Etale.isPerfectPairing_iff`), stated for a pairing whose source is written
with `AlgebraicGeometry.Etale.derivedTensor`. The only difference is the term used to
elaborate `C ⊗ D`: here it is `derivedTensor`, so that the definition can be applied at
`A = ModuleCat Λ` to pairings built from `derivedTensor`, without the kernel having to
compare the two tensor products there (see the implementation notes).

The names `AlgebraicGeometry.Etale.IsPerfectPairing` and
`AlgebraicGeometry.Etale.isPerfectPairing_iff` repeat those of
`CategoryTheory.MonoidalClosed.IsPerfectPairing` on purpose, since they express the same
property. When both namespaces are open, write the namespace explicitly. -/
def IsPerfectPairing {C D : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (b : ((derivedTensor A X).obj C).obj D ⟶ 𝟙_ _) : Prop :=
  MonoidalClosed.IsPerfectPairing (C := _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) b

lemma isPerfectPairing_iff {C D : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (b : ((derivedTensor A X).obj C).obj D ⟶ 𝟙_ _) :
    IsPerfectPairing b ↔
      MonoidalClosed.IsPerfectPairing (C := _root_.DerivedCategory
        (Sheaf X.smallEtaleTopology A)) b :=
  Iff.rfl

/-- An object `K` of `D(X_ét)` is invertible if and only if `K ⊗ᴸ M ≅ Λ_X` and
`M ⊗ᴸ K ≅ Λ_X` for some `M`. -/
lemma isInvertible_iff_exists_derivedTensor
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsInvertible K ↔ ∃ M, Nonempty (((derivedTensor A X).obj K).obj M ≅ 𝟙_ _) ∧
      Nonempty (((derivedTensor A X).obj M).obj K ≅ 𝟙_ _) :=
  Iff.rfl

end Etale

end AlgebraicGeometry
