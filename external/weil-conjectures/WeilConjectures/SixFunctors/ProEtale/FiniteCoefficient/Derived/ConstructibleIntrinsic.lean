/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible

/-!
# Intrinsic bounded constructible complexes on the pro-étale site

Blueprint `definition-constructible-sheaves` defines `Dᵇc(Y, A_{E,n})` intrinsically:
the complexes on `Y_proét` with finitely many nonzero cohomology sheaves, all constructible in
the sense of `AlgebraicGeometry.ProEtale.IsConstructible` (on the strata of a finite partition by
locally closed constructible subschemes, locally constant with finitely generated stalks). The
repository works with the étale-origin reading
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible` (blueprint
`definition-small-pro-etale-site--1`). This file states the intrinsic property and shows that the
étale-origin objects satisfy it; the converse is blueprint
`theorem-comparison-constructible-sheaves`.

## Main definitions

- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleIntrinsic`: bounded with
  constructible cohomology sheaves.

## Main statements

- `ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic`:
  objects of étale origin are intrinsically bounded constructible.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- Blueprint `definition-constructible-sheaves`: Finite-torsion constructibility.

The intrinsic `Dᵇc(Y, A)`: an object of `D(Y_proét, Λ)` with finitely many nonzero cohomology
sheaves (bounded for the canonical t-structure), all of which are constructible
(`AlgebraicGeometry.ProEtale.IsConstructible`). -/
def DerivedCategory.boundedConstructibleIntrinsic :
    ObjectProperty
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  _root_.DerivedCategory.TStructure.t.bounded ⊓
    _root_.DerivedCategory.homologyProperty (fun F ↦ IsConstructible Λ F)

variable {Λ X}

/-- Intrinsic bounded constructibility is invariant under isomorphism. -/
lemma DerivedCategory.boundedConstructibleIntrinsic.of_iso
    {K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (e : K ≅ L) (hK : DerivedCategory.boundedConstructibleIntrinsic Λ X K) :
    DerivedCategory.boundedConstructibleIntrinsic Λ X L :=
  ⟨_root_.DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
    fun n ↦ isConstructible_of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩

/-- The objects of étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`) are intrinsically bounded
constructible: `D(ν^*)` is induced by the exact functor `ν^*`, which commutes with the
cohomology sheaves and preserves constructibility
(`AlgebraicGeometry.ProEtale.isConstructible_comparisonUpperStar_obj`). -/
lemma DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ≤
      DerivedCategory.boundedConstructibleIntrinsic Λ X := by
  rintro K ⟨K', ⟨hb, hc⟩, ⟨e⟩⟩
  refine DerivedCategory.boundedConstructibleIntrinsic.of_iso e
    ⟨(ν^*(X)[ModuleCat.{u + 1} Λ]).bounded_mapDerivedCategory_obj hb, fun n ↦ ?_⟩
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj K') := hc n
  exact isConstructible_of_iso
    (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app K')
    (isConstructible_comparisonUpperStar_obj _)

end AlgebraicGeometry.ProEtale
