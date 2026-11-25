/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Constructible truncations of `ℓ`-adic complexes

Let `X` be a scheme. The bounded constructible derived category `D^b_c(X, ℚ̄_ℓ)` is cut out of
the derived category of pro-étale `ℚ̄_ℓ`-sheaves by boundedness and `ℓ`-adic constructibility of
the cohomology sheaves. This file shows that the canonical truncations `τ^{≤ n}` and `τ^{≥ n}`
restrict to it, so that it inherits the bounded t-structure, and that for an automorphism `h` of
`X` the pullback `h^*` preserves it and commutes with the truncations and the cohomology sheaves.

## Main definitions

- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedAdicConstructible`: the objects of
  `D^b_c(X, ℚ̄_ℓ)`.

## Main statements

All of them are blueprint `prop-constructible-truncations`.

- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedAdicConstructible_truncLE`,
  `AlgebraicGeometry.ProEtale.DerivedCategory.boundedAdicConstructible_truncGE`: the
  truncations restrict to `D^b_c(X, ℚ̄_ℓ)`.
- `ProEtale.DerivedCategory.boundedAdicConstructible_mapDerivedCategory_upperStar`: pullback
  along an automorphism preserves `D^b_c(X, ℚ̄_ℓ)`.
- `AlgebraicGeometry.ProEtale.nonempty_truncLE_comp_mapDerivedCategory_upperStar_iso`,
  `AlgebraicGeometry.ProEtale.nonempty_truncGE_comp_mapDerivedCategory_upperStar_iso`,
  `AlgebraicGeometry.ProEtale.nonempty_mapDerivedCategory_upperStar_comp_homologyFunctor_iso`:
  pullback along an automorphism commutes with the truncations and the cohomology sheaves.

The finite coefficient stage is
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_truncLE` and
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_truncGE`.

## Implementation notes

The blueprint states the proposition at the stages `E` and `ℚ̄_ℓ`. The `E` stage of the
repository is a rationalization of derived complete integral complexes
(`DerivedCategoryDerivedCompleteRational`), which has no cohomology sheaves, so the statement is
made at `ℚ̄_ℓ` and at the finite stages. The bounded t-structure on `D^b_c(X, ℚ̄_ℓ)` is the
restriction of the canonical t-structure `DerivedCategory.TStructure.t`, whose truncation
triangles and axioms are those of the ambient derived category.

The pullback `h^*` along an automorphism `h` is an equivalence, in particular exact, so its
derived functor is `D(h^*)`, the functor induced on derived categories
(`CategoryTheory.Functor.mapDerivedCategory`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The `ℚ̄_ℓ`-stage `D^b_c(X, ℚ̄_ℓ)`, as an object property of `D(X_proét, ℚ̄_ℓ)`: bounded,
with `ℓ`-adically constructible cohomology sheaves. -/
def DerivedCategory.boundedAdicConstructible (X : Scheme.{u}) :
    ObjectProperty
      (_root_.DerivedCategory (AdicSheaf l X)) :=
  _root_.DerivedCategory.TStructure.t.bounded ⊓
    _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l X)

variable {l} {X : Scheme.{u}}

/-- Blueprint `prop-constructible-truncations`: Construction of constructible truncations.

`D^b_c(X, ℚ̄_ℓ)` is stable under the truncation `τ^{≤ n}` of the canonical t-structure: the
cohomology sheaves of `τ^{≤ n} K` are those of `K` in degrees `≤ n`, and zero above. -/
lemma DerivedCategory.boundedAdicConstructible_truncLE
    {K : _root_.DerivedCategory (AdicSheaf l X)}
    (hK : DerivedCategory.boundedAdicConstructible l X K) (n : ℤ) :
    DerivedCategory.boundedAdicConstructible l X
      ((_root_.DerivedCategory.TStructure.t.truncLE n).obj K) := by
  obtain ⟨⟨⟨a, ha⟩, -⟩, hc⟩ := hK
  exact ⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
    _root_.DerivedCategory.homologyProperty_truncLE hc n⟩

/-- Blueprint `prop-constructible-truncations`: Construction of constructible truncations.

`D^b_c(X, ℚ̄_ℓ)` is stable under the truncation `τ^{≥ n}` of the canonical t-structure: the
cohomology sheaves of `τ^{≥ n} K` are those of `K` in degrees `≥ n`, and zero below. -/
lemma DerivedCategory.boundedAdicConstructible_truncGE
    {K : _root_.DerivedCategory (AdicSheaf l X)}
    (hK : DerivedCategory.boundedAdicConstructible l X K) (n : ℤ) :
    DerivedCategory.boundedAdicConstructible l X
      ((_root_.DerivedCategory.TStructure.t.truncGE n).obj K) := by
  obtain ⟨⟨-, ⟨b, hb⟩⟩, hc⟩ := hK
  exact ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
    _root_.DerivedCategory.homologyProperty_truncGE hc n⟩

section Automorphism

variable (h : X ⟶ X) [IsIso h]

omit [IsIso h] in
/-- Blueprint `prop-constructible-truncations`: Construction of constructible truncations.

The pullback `h^*` along an automorphism `h` of `X` preserves `D^b_c(X, ℚ̄_ℓ)`: it is exact, so
`𝓗ⁱ(h^* K) ≅ h^* 𝓗ⁱ(K)`, and pullbacks of constructible sheaves are constructible. -/
lemma DerivedCategory.boundedAdicConstructible_mapDerivedCategory_upperStar
    {K : _root_.DerivedCategory (AdicSheaf l X)}
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    DerivedCategory.boundedAdicConstructible l X
      (((h)^*ᵃ[l]).mapDerivedCategory.obj K) :=
  ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun i ↦
    (adicConstructibleSheaf l X).prop_of_iso
      ((((h)^*ᵃ[l]).mapDerivedCategoryHomologyFunctorIso i).app K)
      ((hK.2 i).upperStar h)⟩

omit [IsIso h] in
/-- Blueprint `prop-constructible-truncations`: Construction of constructible truncations.

The pullback `h^*` along an automorphism `h` of `X` commutes with the truncation `τ^{≤ n}`. -/
theorem nonempty_truncLE_comp_mapDerivedCategory_upperStar_iso (n : ℤ) :
    Nonempty (_root_.DerivedCategory.TStructure.t.truncLE n ⋙
        ((h)^*ᵃ[l]).mapDerivedCategory ≅
      ((h)^*ᵃ[l]).mapDerivedCategory ⋙
        _root_.DerivedCategory.TStructure.t.truncLE n) :=
  ⟨Functor.mapDerivedCategoryTruncLEIso _ n⟩

omit [IsIso h] in
/-- Blueprint `prop-constructible-truncations`: Construction of constructible truncations.

The pullback `h^*` along an automorphism `h` of `X` commutes with the truncation `τ^{≥ n}`. -/
theorem nonempty_truncGE_comp_mapDerivedCategory_upperStar_iso (n : ℤ) :
    Nonempty (_root_.DerivedCategory.TStructure.t.truncGE n ⋙
        ((h)^*ᵃ[l]).mapDerivedCategory ≅
      ((h)^*ᵃ[l]).mapDerivedCategory ⋙
        _root_.DerivedCategory.TStructure.t.truncGE n) :=
  ⟨Functor.mapDerivedCategoryTruncGEIso _ n⟩

omit [IsIso h] in
/-- Blueprint `prop-constructible-truncations`: Construction of constructible truncations.

The pullback `h^*` along an automorphism `h` of `X` commutes with the cohomology sheaves:
`𝓗ⁱ(h^* K) ≅ h^* 𝓗ⁱ(K)`. -/
theorem nonempty_mapDerivedCategory_upperStar_comp_homologyFunctor_iso (i : ℤ) :
    Nonempty (((h)^*ᵃ[l]).mapDerivedCategory ⋙
        _root_.DerivedCategory.homologyFunctor _ i ≅
      _root_.DerivedCategory.homologyFunctor _ i ⋙ (h)^*ᵃ[l]) :=
  ⟨(Functor.mapDerivedCategoryHomologyFunctorIso _ i).symm⟩

end Automorphism

end ProEtale

end AlgebraicGeometry
