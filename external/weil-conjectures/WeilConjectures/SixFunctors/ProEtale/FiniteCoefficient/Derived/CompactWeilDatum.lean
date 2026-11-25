/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekCompactificationBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.WeilDatum

/-!
# Weil data on compactly supported direct images and the compact Frobenius

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `c = (X ⟶[c.i] c.Z ⟶[c.g] Y)`,
and let `g : X ⟶ X`, `h : Y ⟶ Y`, `gZ : c.Z ⟶ c.Z` be endomorphisms compatible with `c`: the
square `g ≫ c.i = c.i ≫ gZ` is cartesian and `gZ ≫ c.g = c.g ≫ h`. For the geometric fibre
`X = X₀ ×_{k₀} k` of a separated scheme of finite type over a finite field `k₀`, a
compactification of `X₀` (Nagata) gives such data for the geometric Frobenius `g = g_γ`, with
`h` the identity of `Spec k`.

A Weil datum `φ : Lg^* K ⟶ K` then induces the Weil datum
```
Lh^* Rf_!(c) K --Ex_!--> Rf_!(c) Lg^* K --Rf_!(c) φ--> Rf_!(c) K
```
on `Rf_!(c) K` (`AlgebraicGeometry.ProEtale.lowerShriekWeilDatum`), with the compact-support
exchange map `Ex_!` along the compatible compactifications
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChange`). For
`h = 𝟙 Y` it is an endomorphism of `Rf_!(c) K`, the *compact Frobenius*
(`AlgebraicGeometry.ProEtale.compactFrobenius`); for `f = a_X` the structure morphism and the
iterated datum `φ_m` this is the global geometric Frobenius `F_{c,m}` on
`RΓ_c(X, K) = Ra_{X!} K` of blueprint `definition-frobenius-operator--1`, in the form
`F_{c,m} = RΓ_c(X, φ_m) ∘ g_{γ,c}^{m,*}` of blueprint
`lemma-scheme-frobenius-geometric-frobenius--3`.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerShriekWeilDatum`: the Weil datum on `Rf_!(c) K`.
- `AlgebraicGeometry.ProEtale.compactFrobenius`: the compact Frobenius on `Rf_!(c) K`.

## Main statements

- `CategoryTheory.IsPullback.iterateHom`, `CategoryTheory.CommSq.iterateHom`: the compatibility
  of the endomorphisms with `c` passes to their iterates, so that the compact Frobenius of the
  iterated datum `φ_m` is defined.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type*} [Category* C]

open AlgebraicGeometry.ProEtale in
/-- A cartesian square `g ≫ i = i ≫ gZ` of endomorphisms stays cartesian after iterating:
`g^m ≫ i = i ≫ gZ^m` is cartesian. -/
lemma IsPullback.iterateHom {X Z : AlgebraicGeometry.Scheme.{u}} {i : X ⟶ Z} {g : X ⟶ X}
    {gZ : Z ⟶ Z} (hi : IsPullback g i i gZ) (m : ℕ) :
    IsPullback (iterateHom g m) i i (iterateHom gZ m) := by
  induction m with
  | zero => exact IsPullback.id_horiz i
  | succ m ih =>
    rw [iterateHom_succ, iterateHom_succ]
    exact hi.paste_horiz ih

open AlgebraicGeometry.ProEtale in
/-- A commutative square `gZ ≫ p = p ≫ h` of endomorphisms stays commutative after iterating. -/
lemma CommSq.iterateHom {Z Y : AlgebraicGeometry.Scheme.{u}} {p : Z ⟶ Y} {gZ : Z ⟶ Z}
    {h : Y ⟶ Y} (hg : CommSq gZ p p h) (m : ℕ) :
    CommSq (iterateHom gZ m) p p (iterateHom h m) := by
  induction m with
  | zero => exact ⟨by simp⟩
  | succ m ih =>
    rw [iterateHom_succ, iterateHom_succ]
    exact hg.horiz_comp ih

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The iterates of the identity are the identity. -/
@[simp]
lemma iterateHom_id (Y : Scheme.{u}) (m : ℕ) : iterateHom (𝟙 Y) m = 𝟙 Y := by
  induction m with
  | zero => rfl
  | succ m ih => rw [iterateHom_succ, ih, Category.comp_id]

/-- A commutative square `gZ ≫ p = p ≫ 𝟙` stays commutative after iterating `gZ`. -/
lemma commSq_iterateHom_id {Z Y : Scheme.{u}} {p : Z ⟶ Y} {gZ : Z ⟶ Z}
    (hg : CommSq gZ p p (𝟙 Y)) (m : ℕ) : CommSq (iterateHom gZ m) p p (𝟙 Y) := by
  simpa using hg.iterateHom m

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) {g : X ⟶ X} {h : Y ⟶ Y}
  {gZ : c.Z ⟶ c.Z} {K : DerivedCategory (Sheaf (ProEt.topology X) A)}

/-- The Weil datum on `Rf_!(c) K` induced by a Weil datum `φ : Lg^* K ⟶ K`, for endomorphisms
`g`, `h`, `gZ` compatible with the compactification `c` (`g ≫ c.i = c.i ≫ gZ` cartesian,
`gZ ≫ c.g = c.g ≫ h`):
```
Lh^* Rf_!(c) K --Ex_!--> Rf_!(c) Lg^* K --Rf_!(c) φ--> Rf_!(c) K,
```
with the compact-support exchange map
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChange`. -/
noncomputable def lowerShriekWeilDatum (hi : IsPullback g c.i c.i gZ) (hg : CommSq gZ c.g c.g h)
    (φ : L((g)^*[A]).obj K ⟶ K) :
    L((h)^*[A]).obj (Rf_!(c)[A].obj K) ⟶ Rf_!(c)[A].obj K :=
  (rightDerivedLowerShriekOfCompactificationBaseChange A c c hi hg).app K ≫ Rf_!(c)[A].map φ

/-- Blueprint `definition-frobenius-operator--1` (the global operator) and
`lemma-scheme-frobenius-geometric-frobenius--3`: the *compact Frobenius* of a Weil datum
`φ : Lg^* K ⟶ K`, for endomorphisms `g`, `gZ` compatible with the compactification `c` over the
identity of `Y`, is the endomorphism
```
Rf_!(c) K ≅ L(𝟙 Y)^* Rf_!(c) K --Ex_!--> Rf_!(c) Lg^* K --Rf_!(c) φ--> Rf_!(c) K
```
of `Rf_!(c) K`. For the structure morphism `f = a_X : X ⟶ Spec k`, `g = g_γ^m` and the iterated
datum `φ_m` (`AlgebraicGeometry.ProEtale.weilDatumIterate`), it is the global geometric
Frobenius `F_{c,m} = RΓ_c(X, φ_m) ∘ g_{γ,c}^{m,*}` on `RΓ_c(X, K) = Ra_{X!} K`. -/
noncomputable def compactFrobenius (hi : IsPullback g c.i c.i gZ)
    (hg : CommSq gZ c.g c.g (𝟙 Y)) (φ : L((g)^*[A]).obj K ⟶ K) :
    Rf_!(c)[A].obj K ⟶ Rf_!(c)[A].obj K :=
  (leftDerivedUpperStarId A Y).inv.app _ ≫ lowerShriekWeilDatum A c hi hg φ

end AlgebraicGeometry.ProEtale
