/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!
# Coefficient-side vocabulary of `D(X_ét, Λ)`

The tensor-side finiteness vocabulary of the six-functor formalism: the constant complex
`Λ_X`, Tor amplitude, the category `D^b_{ctf}(X, Λ)` of bounded constructible complexes of
finite Tor amplitude, and ⊗-invertible objects.

These belong to the framework, not to any one chapter: the finiteness statements of
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness` and the purity conventions of
`WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions` both use them.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategoryModule`: the derived category `D(X_ét, Λ)`.
- `AlgebraicGeometry.Etale.constantComplex`: the constant complex `Λ_X`, the unit of the
  derived tensor product.
- `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`: Tor amplitude in `[a, b]`.
  Finite Tor amplitude is `AlgebraicGeometry.Etale.DerivedCategory.finiteTorAmplitude` of
  `WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`, for `A = ModuleCat Λ`.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleFiniteTor`:
  `D^b_{ctf}(X, Λ)`.
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible`: ⊗-invertible objects.
- `AlgebraicGeometry.Etale.reductionModIdeal`: reduction of coefficients `K ↦ K ⊗^L (Λ/J)_X`;
  an integer in `J` kills it (`AlgebraicGeometry.Etale.nsmul_id_reductionModIdeal`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- Blueprint `def-weil-pbc-derived-categories`: Derived categories of etale sheaves

The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`: the localization of
the cochain complexes of sheaves of `Λ`-modules on the small étale site at the quasi-isomorphisms
(`DerivedCategory`). Its subcategories `D⁺(X_ét, Λ)` and `Dᵇ(X_ét, Λ)` are
`DerivedCategory.Plus` and `DerivedCategory.Bounded`, the objects whose cohomology sheaves
`DerivedCategory.homologyFunctor _ i` vanish below some degree, resp. outside a finite range
(`DerivedCategory.isGE_iff`, `DerivedCategory.isLE_iff`). -/
abbrev DerivedCategoryModule : Type (u + 2) :=
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- Blueprint `definition-constructible-sheaves--6`: Coefficients and sites

The constant complex `Λ_X ∈ D(X_ét, Λ)`: the constant sheaf with value `Λ` placed in degree
zero, which is the unit of the derived tensor product `AlgebraicGeometry.Etale.derivedTensor`.
It is the coefficient object every statement of the purity chapter is normalized against. -/
noncomputable def constantComplex :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  𝟙_ _

/-- Blueprint `definition-constructible-sheaves--6`: Coefficients and sites

An object `K` of `D(X_ét, Λ)` has *Tor amplitude in `[a, b]`* if for every sheaf `F` of
`Λ`-modules on `X_ét` the derived tensor product `K ⊗^L F` has vanishing cohomology outside
`[a, b]`. -/
def DerivedCategory.hasTorAmplitudeIn (a b : ℤ) :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), q < a ∨ b < q →
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- Blueprint `definition-constructible-sheaves--6`: Coefficients and sites

The category `D^b_{ctf}(X, Λ)` of the purity chapter, as an object property: bounded with
constructible cohomology sheaves and of finite Tor amplitude. -/
def DerivedCategory.boundedConstructibleFiniteTor :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ⊓
    DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) X

/-- An object `L` of `D(X_ét, Λ)` is *invertible* if it has a two-sided tensor inverse: there
is an `M` with `L ⊗^L M ≅ Λ_X` and `M ⊗^L L ≅ Λ_X`. A lisse rank-one sheaf placed in any degree
and twisted by any power of the Tate object is invertible in this sense, and these are the only
invertible objects that occur in the purity chapter. -/
def DerivedCategory.isInvertible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun L ↦ ∃ M, Nonempty
    (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj L).obj M ≅ constantComplex Λ X) ∧ Nonempty
    (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj L ≅ constantComplex Λ X)

/-- Reduction of coefficients along a quotient of the coefficient ring: the functor
`K ↦ K ⊗^L (Λ/J)_X` on `D(X_ét, Λ)`. For `Λ = A_{E,n}` and `J = ϖ^m` this is the finite
reduction `K ↦ K_m` of the adic formalism. -/
noncomputable def reductionModIdeal (J : Ideal Λ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))))

variable {Λ X}

/-- An integer `N` vanishing in `Λ` kills every object of `D(X_ét, Λ)`, the derived category
being `Λ`-linear. -/
lemma nsmul_id_eq_zero_of_natCast_eq_zero {N : ℕ} (hN : (N : Λ) = 0)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : N • 𝟙 K = 0 := by
  rw [← Nat.cast_smul_eq_nsmul Λ, hN, zero_smul]

/-- An integer `N` lying in the ideal `J` kills the reduction `K ⊗^L (Λ/J)_X` of every object
`K` of `D(X_ét, Λ)`: it kills `Λ/J`, hence the constant complex `(Λ/J)_X`, and tensoring with
`K` is additive. -/
lemma nsmul_id_reductionModIdeal {J : Ideal Λ} {N : ℕ} (hN : (N : Λ) ∈ J)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    N • 𝟙 ((reductionModIdeal Λ X J).obj K) = 0 := by
  have hM : N • 𝟙 (ModuleCat.of Λ (Λ ⧸ J)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [ModuleCat.hom_nsmul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [← Nat.cast_smul_eq_nsmul Λ, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact J.mul_mem_right _ hN
  change N • 𝟙 (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj _) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
    ← (DerivedCategory.singleFunctor _ 0).map_id, ← Functor.map_nsmul,
    ← (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map_id, ← Functor.map_nsmul, hM,
    Functor.map_zero, Functor.map_zero, Functor.map_zero]

/-- An element `r` of the ideal `J` kills the reduction `K ⊗ᴸ (Λ ⧸ J)_X` of every object `K` of
`D(X_ét, Λ)`: it kills `Λ ⧸ J`, hence the constant complex `(Λ ⧸ J)_X`, and tensoring with `K`
is `Λ`-linear. -/
lemma smul_id_reductionModIdeal {J : Ideal Λ} {r : Λ} (hr : r ∈ J)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    r • 𝟙 ((reductionModIdeal Λ X J).obj K) = 0 := by
  have hM : r • 𝟙 (ModuleCat.of Λ (Λ ⧸ J)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul (Ideal.Quotient.mk J),
      Ideal.Quotient.eq_zero_iff_mem]
    exact J.mul_mem_right _ hr
  change r • 𝟙 (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj _) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul,
    ← (DerivedCategory.singleFunctor _ 0).map_id, ← Functor.map_smul,
    ← (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map_id, ← Functor.map_smul, hM,
    Functor.map_zero, Functor.map_zero, Functor.map_zero]

end Etale

end AlgebraicGeometry
