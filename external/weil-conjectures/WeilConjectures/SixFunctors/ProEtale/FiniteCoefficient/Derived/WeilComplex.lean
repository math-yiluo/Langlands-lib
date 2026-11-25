/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!

# Strict Weil complexes on the pro-étale site

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex`,
at the finite coefficient stage of the trace-formula chapter.

Let `A` be a monoidal Grothendieck abelian coefficient category, for instance modules over
`A_{E,n} = 𝒪_E / ϖ_E ^ n`, and let `X` be a scheme carrying an automorphism `g`. A
*strict Weil complex* is a pair `(K, φ)` with `K` in `Dctf(X, A)` (on the small pro-étale site)
and an isomorphism `φ : Lg^* K ≅ K` formed using the derived pullback; a morphism of strict
Weil complexes is a morphism of the underlying complexes commuting with the two `φ`s. These
form a category with a forgetful functor to `Dctf(X, A)`.

The blueprint takes `X = X₀ ×_{k₀} k̄` the geometric fiber of a scheme `X₀` over a finite field
`k₀` and `g = g_γ = 𝟙 × Spec(γ)` its geometric-Frobenius automorphism, `γ` being the inverse of
the `#k₀`-power map of `k̄`. This is `AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`,
and the resulting category is `AlgebraicGeometry.ProEtale.GeometricFiberStrictWeilComplex`.

This is a category of pairs over `Dctf(X, A)`, not a triangulated (derived) category of Weil
sheaves such as `AlgebraicGeometry.WeilComplex`: its Hom-groups are not Ext groups of Weil
sheaves, since a nonsplit Frobenius extension of `Λ` by `Λ` gives no nonzero map `Λ ⟶ Λ[1]` of
pairs.

`AlgebraicGeometry.ProEtale.StrictWeilComplex` is not the category of Weil objects
`AlgebraicGeometry.ProEtale.CondensedRing.WeilBoundedConstructible` of
`WeilConjectures.WeilObject.BoundedConstructible.Defs`, which is the input of the trace formula
(`WeilConjectures.TraceFormula.Main`): there the coefficients are `ℚ̄_ℓ`, the Frobenius
`Φ : X ⟶ X` over `Spec k` is an endomorphism, not necessarily an automorphism, and `K` lies in
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. Here the coefficients are finite, the automorphism `g` is a fixed parameter, `K`
lies in `Dctf(X, A)`, `φ` is an isomorphism, and the pairs form a category.

## Main definitions

- `AlgebraicGeometry.ProEtale.StrictWeilComplex`: pairs `(K, φ : Lg^* K ≅ K)` for an
  automorphism `g` of `X`, with its `Category` instance.
- `AlgebraicGeometry.ProEtale.StrictWeilComplex.forget`: the forgetful functor to
  `Dctf(X, A)`.
- `AlgebraicGeometry.ProEtale.GeometricFiberStrictWeilComplex`: the category
  `D^b_{ctf,W}(X, A)` of strict Weil complexes on the geometric fiber `X = X₀ ×_{k₀} k̄`, for
  the geometric Frobenius `g_γ`.

## Main results

- `AlgebraicGeometry.ProEtale.StrictWeilComplex.map_hom_eq_zero_of_iso_unit` and
  `AlgebraicGeometry.ProEtale.GeometricFiberStrictWeilComplex.map_hom_eq_zero_of_iso_unit`: on a
  point, there is no nonzero morphism of strict Weil complexes from `Λ` to `Λ[1]`, whatever the
  Weil structures, so the Hom-groups are not Ext groups of Weil sheaves.

## Implementation notes

The Weil structure `φ` is an isomorphism in the ambient derived category `D(X_proét)`, so that
no stability of `Dctf(X, A)` under `Lg^*` is needed to state the definition.

The blueprint fixes `X₀` separated of finite type over `k₀` as a standing convention; the
definitions do not use these hypotheses, so they are not imposed.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

namespace ProEtale

section General

variable {X : Scheme.{u}} (g : X ≅ X)

/-- Blueprint `definition-weil-structure--2`: Strict Weil complex at finite coefficients.

A *strict Weil complex* on `X` for an automorphism `g` of `X` is a pair `(K, φ)` consisting of
an object `K` of `Dctf(X, A)` — a bounded constructible pro-étale complex of finite Tor
amplitude — together with an isomorphism `φ : Lg^* K ≅ K` formed using the derived pullback.

The blueprint takes for `g` the geometric-Frobenius automorphism `g_γ` of the geometric fiber
of a scheme over a finite field; see `AlgebraicGeometry.ProEtale.GeometricFiberStrictWeilComplex`.
-/
structure StrictWeilComplex where
  /-- The underlying object of `Dctf(X, A)`. -/
  obj : Dctf(X, A)
  /-- The Weil structure `φ : Lg^* K ≅ K`. -/
  frobenius : L((g.hom)^*[A]).obj ((DerivedCategoryFiniteTor.ι A X).obj obj) ≅
    (DerivedCategoryFiniteTor.ι A X).obj obj

namespace StrictWeilComplex

variable {A g}

/-- Blueprint `definition-weil-structure--2`: Strict Weil complex at finite coefficients.

A morphism of strict Weil complexes `(K, φ_K) ⟶ (L, φ_L)` is a morphism `u : K ⟶ L` of the
underlying objects of `Dctf(X, A)` making the square

```
  Lg^* K --Lg^* u--> Lg^* L
     |                  |
    φ_K                φ_L
     v                  v
     K -------u------>  L
```

commute. -/
@[ext]
structure Hom (K L : StrictWeilComplex A g) where
  /-- The underlying morphism of `Dctf(X, A)`. -/
  hom : K.obj ⟶ L.obj
  /-- Compatibility with the two Weil structures. -/
  comm : K.frobenius.hom ≫ (DerivedCategoryFiniteTor.ι A X).map hom =
    L((g.hom)^*[A]).map ((DerivedCategoryFiniteTor.ι A X).map hom) ≫ L.frobenius.hom

/-- Blueprint `definition-weil-structure--2`: Strict Weil complex at finite coefficients.

The category of strict Weil complexes: identities and composition are computed on the
underlying objects of `Dctf(X, A)`, and both are compatible with the Weil structures. -/
noncomputable instance : Category (StrictWeilComplex A g) where
  Hom K L := Hom K L
  id K := { hom := 𝟙 K.obj, comm := by simp }
  comp {K L M} f h :=
    { hom := f.hom ≫ h.hom
      comm := by
        rw [Functor.map_comp, ← Category.assoc, f.comm, Category.assoc, h.comm,
          ← Category.assoc, ← Functor.map_comp] }

@[ext]
lemma hom_ext {K L : StrictWeilComplex A g} {f h : K ⟶ L} (e : f.hom = h.hom) : f = h :=
  Hom.ext e

@[simp]
lemma id_hom (K : StrictWeilComplex A g) : (𝟙 K : K ⟶ K).hom = 𝟙 K.obj := rfl

@[simp]
lemma comp_hom {K L M : StrictWeilComplex A g} (f : K ⟶ L) (h : L ⟶ M) :
    (f ≫ h).hom = f.hom ≫ h.hom := rfl

variable (A g)

/-- Blueprint `definition-weil-structure--2`: Strict Weil complex at finite coefficients.

The forgetful functor `For` from strict Weil complexes to `Dctf(X, A)`, sending `(K, φ)` to the
underlying object `K` and forgetting the Weil structure. -/
noncomputable def forget : StrictWeilComplex A g ⥤ Dctf(X, A) where
  obj K := K.obj
  map f := f.hom

/-- The forgetful functor is faithful: morphisms of strict Weil complexes are determined by
their underlying morphisms. -/
instance : (forget A g).Faithful where
  map_injective e := hom_ext e

end StrictWeilComplex

end General

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀))

/-- Blueprint `definition-weil-structure--2`: Strict Weil complex at finite coefficients.

Let `X₀` be a scheme over a finite field `k₀`, with structure morphism `f`, and let
`X = X₀ ×_{k₀} k̄` be its geometric fiber. The category `D^b_{ctf,W}(X, A)` of strict Weil
complexes on `X` at the coefficients `A` (in the blueprint, `A = A_{E,n}`): pairs `(K, φ)` with
`K ∈ Dctf(X, A)` on the small pro-étale site and `φ : Lg_γ^* K ≅ K`, where
`g_γ = 𝟙 × Spec(γ)` is the geometric-Frobenius automorphism of `X`
(`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`); morphisms are the morphisms of the
underlying complexes commuting with the `φ`s. It comes with the forgetful functor
`AlgebraicGeometry.ProEtale.StrictWeilComplex.forget` to `Dctf(X, A)`.

This is a category of pairs over `Dctf(X, A)`, not a triangulated category of Weil sheaves such
as `AlgebraicGeometry.WeilComplex`. -/
abbrev GeometricFiberStrictWeilComplex : Type _ :=
  StrictWeilComplex A (f.geometricGaloisFrobenius).asIso

section HomGroups

variable {K : Type u} [Field K] [IsAlgClosed K] {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `definition-weil-structure--2`: Strict Weil complex at finite coefficients.

The Hom-groups of strict Weil complexes are not Ext groups of Weil sheaves. On a point
`X ≅ Spec K`, `K` algebraically closed, a strict Weil complex `M` with underlying complex `Λ`
and one `N` with underlying complex `Λ[1]` admit no nonzero morphism `M ⟶ N`, whatever their
Weil structures: the underlying morphism lies in `Hom(Λ, Λ[1]) = H¹(X_proét, Λ) = 0`. In
particular a nonsplit Frobenius extension of `Λ` by `Λ` (a Jordan block), which is a nonzero
extension class of Weil sheaves, gives no nonzero map `Λ ⟶ Λ[1]` of pairs. -/
lemma StrictWeilComplex.map_hom_eq_zero_of_iso_unit {X : Scheme.{u}} (e : X ≅ Spec (.of K))
    {g : X ≅ X} {M N : StrictWeilComplex (ModuleCat.{u + 1} Λ) g}
    (eM : (DerivedCategoryFiniteTor.ι _ X).obj M.obj ≅ 𝟙_ _)
    (eN : (DerivedCategoryFiniteTor.ι _ X).obj N.obj ≅ (𝟙_ _)⟦(1 : ℤ)⟧) (f : M ⟶ N) :
    (DerivedCategoryFiniteTor.ι _ X).map f.hom = 0 := by
  rw [← cancel_epi eM.inv, ← cancel_mono eN.hom, Limits.comp_zero, Limits.zero_comp]
  exact DerivedCategory.unit_hom_shift_one_eq_zero_of_iso Λ e _

variable {k₀ : Type u} [Field k₀] [Finite k₀]

/-- Blueprint `definition-weil-structure--2`: Strict Weil complex at finite coefficients.

The Hom-groups of `D^b_{ctf,W}(X, Λ)` are not Ext groups of Weil sheaves: on the geometric
fiber `X = Spec k̄` of the point `Spec k₀`, there is no nonzero morphism of strict Weil
complexes from one with underlying complex `Λ` to one with underlying complex `Λ[1]`, so a
nonsplit Frobenius extension of `Λ` by `Λ` (a Jordan block) gives no nonzero map
`Λ ⟶ Λ[1]` of pairs. -/
lemma GeometricFiberStrictWeilComplex.map_hom_eq_zero_of_iso_unit
    {M N : GeometricFiberStrictWeilComplex (ModuleCat.{u + 1} Λ) (𝟙 (Spec (.of k₀)))}
    (eM : (DerivedCategoryFiniteTor.ι _ _).obj M.obj ≅ 𝟙_ _)
    (eN : (DerivedCategoryFiniteTor.ι _ _).obj N.obj ≅ (𝟙_ _)⟦(1 : ℤ)⟧) (f : M ⟶ N) :
    (DerivedCategoryFiniteTor.ι _ _).map f.hom = 0 :=
  StrictWeilComplex.map_hom_eq_zero_of_iso_unit
    (asIso (pullback.snd (𝟙 (Spec (.of k₀))) (Scheme.specAlgebraicClosure k₀).hom)) eM eN f

end HomGroups

end ProEtale

end AlgebraicGeometry
