/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# Weil data on pro-étale complexes at finite coefficients

Let `g : X ⟶ X` be an endomorphism of a scheme. As in blueprint
`definition-frobenius-correspondences-their-operators`, a *Weil datum* on a complex
`K ∈ D(X_proét, A)` is a morphism `φ : Lg^* K ⟶ K`, without an invertibility requirement (a strict
Weil complex, `AlgebraicGeometry.ProEtale.StrictWeilComplex`, is the case of an isomorphism and an
automorphism `g`). This file attaches to Weil data the operations that the Frobenius operators of
the trace formula are built from.

* **Iterates.** Writing `g_m = g^m` (`AlgebraicGeometry.ProEtale.iterateHom`), the iterate
  `φ_m : Lg_m^* K ⟶ K` composes the pulled back copies of `φ` along the composition isomorphisms
  of the derived pullback (blueprint `definition-frobenius-correspondences-their-operators--4`):
  ```
  φ_0 : L(𝟙 X)^* K ≅ K,
  φ_{m+1} : L(g ≫ g_m)^* K ≅ Lg^* Lg_m^* K --Lg^* φ_m--> Lg^* K --φ--> K.
  ```
* **Pullback.** For `x : P ⟶ X` and `e : P ⟶ P` with `e ≫ x = x ≫ g`, the Weil datum `φ`
  induces a Weil datum for `e` on `Lx^* K`:
  ```
  Le^* Lx^* K ≅ L(e ≫ x)^* K = L(x ≫ g)^* K ≅ Lx^* Lg^* K --Lx^* φ--> Lx^* K.
  ```
* **Stalks.** For a point `x : P ⟶ X` fixed by `g`, `x ≫ g = x`, this is a Weil datum for the
  identity of `P`, that is an endomorphism `F_x` of the stalk complex `K_x = Lx^* K`: the *local
  Frobenius* of blueprint `definition-frobenius-correspondences-their-operators`,
  `F_{x,m} = (φ_m)_x` for a point fixed by `g_m`.

## Main definitions

- `AlgebraicGeometry.ProEtale.iterateHom`: the iterate `g^m` of an endomorphism.
- `AlgebraicGeometry.ProEtale.weilDatumIterate`: the iterated Weil datum `φ_m`.
- `AlgebraicGeometry.ProEtale.upperStarWeilDatum`: the Weil datum on `Lx^* K`.
- `AlgebraicGeometry.ProEtale.stalkFrobenius`: the local Frobenius `F_x` at a fixed point.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Iterate

variable {X : Scheme.{u}} (g : X ⟶ X)

/-- The `m`-th iterate `g^m : X ⟶ X` of an endomorphism `g` of a scheme. -/
noncomputable def iterateHom (m : ℕ) : X ⟶ X :=
  End.asHom (End.of g ^ m)

@[simp]
lemma iterateHom_zero : iterateHom g 0 = 𝟙 X :=
  rfl

lemma iterateHom_succ (m : ℕ) : iterateHom g (m + 1) = g ≫ iterateHom g m := by
  rw [iterateHom, pow_succ]
  rfl

@[simp]
lemma iterateHom_one : iterateHom g 1 = g := by
  rw [iterateHom_succ, iterateHom_zero, Category.comp_id]

/-- The iterates of an endomorphism add: `g^(m + n) = g^n ≫ g^m`. -/
lemma iterateHom_add (m n : ℕ) : iterateHom g (m + n) = iterateHom g n ≫ iterateHom g m := by
  induction n with
  | zero => simp
  | succ n ih => rw [← Nat.add_assoc, iterateHom_succ, ih, iterateHom_succ, Category.assoc]

end Iterate

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Datum

variable {X : Scheme.{u}} {g : X ⟶ X}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}

/-- Blueprint `definition-frobenius-correspondences-their-operators--4`: the iterate
`φ_m : Lg_m^* K ⟶ K` of a Weil datum `φ : Lg^* K ⟶ K`, for the iterate `g_m = g^m`
(`AlgebraicGeometry.ProEtale.iterateHom`): `φ_0` is the identification `L(𝟙 X)^* K ≅ K` and
`φ_{m+1}` is the composite
```
L(g_{m+1})^* K = L(g ≫ g_m)^* K ≅ Lg^* Lg_m^* K --Lg^* φ_m--> Lg^* K --φ--> K.
```
-/
noncomputable def weilDatumIterate (φ : L((g)^*[A]).obj K ⟶ K) :
    (m : ℕ) → L((iterateHom g m)^*[A]).obj K ⟶ K
  | 0 => (leftDerivedUpperStarId A X).hom.app K
  | m + 1 =>
    (leftDerivedUpperStarCongr A (iterateHom_succ g m)).hom.app K ≫
      (leftDerivedUpperStarComp A g (iterateHom g m)).hom.app K ≫
      L((g)^*[A]).map (weilDatumIterate φ m) ≫ φ

lemma weilDatumIterate_zero (φ : L((g)^*[A]).obj K ⟶ K) :
    weilDatumIterate φ 0 = (leftDerivedUpperStarId A X).hom.app K :=
  rfl

lemma weilDatumIterate_succ (φ : L((g)^*[A]).obj K ⟶ K) (m : ℕ) :
    weilDatumIterate φ (m + 1) =
      (leftDerivedUpperStarCongr A (iterateHom_succ g m)).hom.app K ≫
        (leftDerivedUpperStarComp A g (iterateHom g m)).hom.app K ≫
        L((g)^*[A]).map (weilDatumIterate φ m) ≫ φ :=
  rfl

variable {P : Scheme.{u}} {e : P ⟶ P} {x : P ⟶ X}

/-- The Weil datum for `e` induced on the pullback `Lx^* K` by a Weil datum `φ : Lg^* K ⟶ K`,
for `x : P ⟶ X` with `e ≫ x = x ≫ g`:
```
Le^* Lx^* K ≅ L(e ≫ x)^* K = L(x ≫ g)^* K ≅ Lx^* Lg^* K --Lx^* φ--> Lx^* K.
```
-/
noncomputable def upperStarWeilDatum (h : e ≫ x = x ≫ g) (φ : L((g)^*[A]).obj K ⟶ K) :
    L((e)^*[A]).obj (L((x)^*[A]).obj K) ⟶ L((x)^*[A]).obj K :=
  (leftDerivedUpperStarComp A e x).inv.app K ≫ (leftDerivedUpperStarCongr A h).hom.app K ≫
    (leftDerivedUpperStarComp A x g).hom.app K ≫ L((x)^*[A]).map φ

/-- A point fixed by `g` is compatible with the identity of its source and `g`. -/
lemma id_comp_eq_comp_of_comp_eq (hx : x ≫ g = x) : 𝟙 P ≫ x = x ≫ g := by
  rw [Category.id_comp, hx]

/-- Blueprint `definition-frobenius-correspondences-their-operators`: the *local Frobenius*
`F_x : K_x ⟶ K_x` of a Weil datum `φ : Lg^* K ⟶ K` at a point `x : P ⟶ X` fixed by `g`
(`x ≫ g = x`), on the stalk complex `K_x = Lx^* K`:
```
Lx^* K ≅ L(𝟙 P)^* Lx^* K ≅ L(x ≫ g)^* K ≅ Lx^* Lg^* K --Lx^* φ--> Lx^* K,
```
the Weil datum `AlgebraicGeometry.ProEtale.upperStarWeilDatum` for the identity of `P`. For a
point fixed by the iterate `g_m`, the local Frobenius `F_{x,m}` of the trace formula is the
local Frobenius of the iterated datum `φ_m` (`AlgebraicGeometry.ProEtale.weilDatumIterate`). -/
noncomputable def stalkFrobenius (hx : x ≫ g = x) (φ : L((g)^*[A]).obj K ⟶ K) :
    L((x)^*[A]).obj K ⟶ L((x)^*[A]).obj K :=
  (leftDerivedUpperStarId A P).inv.app _ ≫ upperStarWeilDatum (id_comp_eq_comp_of_comp_eq hx) φ

end Datum

end AlgebraicGeometry.ProEtale
