/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
public import WeilConjectures.SixFunctors.Etale.Derived.Stability

/-!

# Strict Weil complexes

Let `A` be a monoidal Grothendieck abelian coefficient category and let `X` be a scheme
carrying an automorphism `g`. In the `ℓ`-adic formalism `X = X₀ ×_{k₀} k` is the base change
of a scheme over a finite field to an algebraic closure and `g = g_γ` is the
geometric-Frobenius automorphism of `X` attached to a choice of Frobenius `γ` of `k` over
`k₀`. The construction of `g_γ` from `X₀` and `k₀` belongs to a different blueprint block, so
here the automorphism is simply a parameter.

A *strict Weil complex* at `Λ` is then a pair `(K, φ)` with `K` in `Dctf(X, Λ)` and an
isomorphism `φ : Lg^* K ≅ K`; a morphism of strict Weil complexes is a morphism of the
underlying complexes commuting with the two `φ`s. These form the category
`D^b_{ctf,W}(X, Λ)`, equipped with a forgetful functor to `Dctf(X, Λ)`.

## Main definitions

- `AlgebraicGeometry.Etale.WeilComplex`: the objects of `D^b_{ctf,W}(X, Λ)`.
- `AlgebraicGeometry.Etale.WeilComplex.Hom` and the `Category` instance on
  `AlgebraicGeometry.Etale.WeilComplex`.
- `AlgebraicGeometry.Etale.WeilComplex.forget`: the forgetful functor to `Dctf(X, Λ)`.

## Main results

- `AlgebraicGeometry.Etale.WeilComplex.map_hom_eq_zero_of_iso_unit` and
  `AlgebraicGeometry.Etale.WeilComplex.map_hom_eq_zero_of_iso_unit_geometricFiber`: on a point,
  there is no nonzero morphism of strict Weil complexes from `Λ` to `Λ[1]`, whatever the Weil
  structures, so the Hom-groups are not Ext groups of Weil sheaves.

## Implementation notes

`Lg^*` is taken as the restriction `DerivedCategoryFiniteTor.leftDerivedUpperStar` of the
derived pullback to the small category `Dctf(X, Λ)`, which is available by
`proposition-six-operations-dctf` (i); see
`WeilConjectures.SixFunctors.Etale.Derived.Stability`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

variable [UpperStarPreservesFlat A] {X : Scheme.{u}} (g : X ≅ X)

/-- Blueprint `definition-weil-structure`: Strict Weil complexes.

A *strict Weil complex* at `Λ` on `X` is a pair `(K, φ)` consisting of an object `K` of
`Dctf(X, Λ)` — a bounded constructible complex of finite Tor amplitude — together with an
isomorphism `φ : Lg^* K ≅ K`, where `g` is the geometric-Frobenius automorphism of
`X = X₀ ×_{k₀} k`.

The automorphism `g` is a parameter here: its construction from a model `X₀` over a finite
field `k₀` and a Frobenius `γ` of `k` over `k₀` belongs to a different blueprint block.

Strict Weil complexes form a category `D^b_{ctf,W}(X, Λ)`, whose morphisms are the morphisms
of the underlying complexes commuting with the two `φ`s, with a forgetful functor
`AlgebraicGeometry.Etale.WeilComplex.forget` to `Dctf(X, Λ)`. -/
structure WeilComplex where
  /-- The underlying object of `Dctf(X, Λ)`. -/
  obj : DerivedCategoryFiniteTor A X
  /-- The Weil structure `φ : Lg^* K ≅ K`, a descent datum along the geometric Frobenius. -/
  frobenius : (DerivedCategoryFiniteTor.leftDerivedUpperStar A g.hom).obj obj ≅ obj

namespace WeilComplex

/-- Blueprint `definition-weil-structure`: Strict Weil complexes.

A morphism of strict Weil complexes `(K, φ_K) ⟶ (L, φ_L)` is a morphism `u : K ⟶ L` of the
underlying objects of `Dctf(X, Λ)` making the square

```
  Lg^* K --Lg^* u--> Lg^* L
     |                  |
    φ_K                φ_L
     v                  v
     K -------u------>  L
```

commute. -/
@[ext]
structure Hom (K L : WeilComplex A g) where
  /-- The underlying morphism of `Dctf(X, Λ)`. -/
  hom : K.obj ⟶ L.obj
  /-- Compatibility with the two Weil structures. -/
  comm : K.frobenius.hom ≫ hom =
    (DerivedCategoryFiniteTor.leftDerivedUpperStar A g.hom).map hom ≫ L.frobenius.hom

/-- Blueprint `definition-weil-structure`: Strict Weil complexes.

The category `D^b_{ctf,W}(X, Λ)` of strict Weil complexes: identities and composition are
computed on the underlying objects of `Dctf(X, Λ)`, and both are readily checked to be
compatible with the Weil structures. -/
noncomputable instance : Category (WeilComplex A g) where
  Hom K L := Hom A g K L
  id K := { hom := 𝟙 K.obj, comm := by simp }
  comp {K L M} f h :=
    { hom := f.hom ≫ h.hom
      comm := by
        rw [← Category.assoc, f.comm, Category.assoc, h.comm, ← Category.assoc,
          ← Functor.map_comp] }

@[simp]
lemma id_hom (K : WeilComplex A g) : (𝟙 K : K ⟶ K).hom = 𝟙 K.obj := rfl

@[simp]
lemma comp_hom {K L M : WeilComplex A g} (f : K ⟶ L) (h : L ⟶ M) :
    (f ≫ h).hom = f.hom ≫ h.hom := rfl

/-- Blueprint `definition-weil-structure`: Strict Weil complexes.

The forgetful functor `D^b_{ctf,W}(X, Λ) ⥤ Dctf(X, Λ)` sending a strict Weil complex
`(K, φ)` to the underlying object `K` and forgetting the Weil structure. -/
noncomputable def forget : WeilComplex A g ⥤ DerivedCategoryFiniteTor A X where
  obj K := K.obj
  map f := f.hom

end WeilComplex

section HomGroups

variable {K : Type u} [Field K] [IsAlgClosed K] {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `definition-weil-structure`: Strict Weil complexes.

The Hom-groups of strict Weil complexes are not Ext groups of Weil sheaves. On a point
`Y ≅ Spec K`, `K` algebraically closed, a strict Weil complex `M` with underlying complex `Λ`
and one `N` with underlying complex `Λ[1]` admit no nonzero morphism `M ⟶ N`, whatever their
Weil structures: the underlying morphism lies in `Hom(Λ, Λ[1]) = H¹(Y_ét, Λ) = 0`. In
particular a nonsplit Frobenius extension of `Λ` by `Λ` (a Jordan block), which is a nonzero
extension class of Weil sheaves, gives no nonzero map `Λ ⟶ Λ[1]` of pairs. -/
lemma WeilComplex.map_hom_eq_zero_of_iso_unit {Y : Scheme.{u}} (e : Y ≅ Spec (.of K))
    {h : Y ≅ Y} {M N : WeilComplex (ModuleCat.{u + 1} Λ) h}
    (eM : (DerivedCategoryFiniteTor.ι _ Y).obj M.obj ≅ 𝟙_ _)
    (eN : (DerivedCategoryFiniteTor.ι _ Y).obj N.obj ≅ (𝟙_ _)⟦(1 : ℤ)⟧) (f : M ⟶ N) :
    (DerivedCategoryFiniteTor.ι _ Y).map f.hom = 0 := by
  rw [← cancel_epi eM.inv, ← cancel_mono eN.hom, Limits.comp_zero, Limits.zero_comp]
  exact DerivedCategory.unit_hom_shift_one_eq_zero_of_iso Λ e _

variable {k₀ : Type u} [Field k₀] [Finite k₀]

/-- Blueprint `definition-weil-structure`: Strict Weil complexes.

The Hom-groups of `D^b_{ctf,W}(X, Λ)` are not Ext groups of Weil sheaves: on the geometric
fiber `X = Spec k̄` of the point `Spec k₀`, with its geometric-Frobenius automorphism `g_γ`,
there is no nonzero morphism of strict Weil complexes from one with underlying complex `Λ` to
one with underlying complex `Λ[1]`, so a nonsplit Frobenius extension of `Λ` by `Λ` (a Jordan
block) gives no nonzero map `Λ ⟶ Λ[1]` of pairs. -/
lemma WeilComplex.map_hom_eq_zero_of_iso_unit_geometricFiber
    {M N : WeilComplex (ModuleCat.{u + 1} Λ)
      (Scheme.Hom.geometricGaloisFrobenius (𝟙 (Spec (.of k₀)))).asIso}
    (eM : (DerivedCategoryFiniteTor.ι _ _).obj M.obj ≅ 𝟙_ _)
    (eN : (DerivedCategoryFiniteTor.ι _ _).obj N.obj ≅ (𝟙_ _)⟦(1 : ℤ)⟧) (f : M ⟶ N) :
    (DerivedCategoryFiniteTor.ι _ _).map f.hom = 0 :=
  WeilComplex.map_hom_eq_zero_of_iso_unit
    (asIso (pullback.snd (𝟙 (Spec (.of k₀))) (Scheme.specAlgebraicClosure k₀).hom)) eM eN f

end HomGroups

end Etale

end AlgebraicGeometry
