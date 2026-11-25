/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# Pushforwards along a base change to `k̄` commute with the Frobenius pullbacks

Let `k` be a finite field, `φ : X₀ ⟶ Y₀` a morphism of `k`-schemes and `φ̄ = φ × 𝟙 : X ⟶ Y` its
base change to the geometric fibers, so that `φ̄ ≫ Fr_Y = Fr_X ≫ φ̄` for the geometric Galois
Frobenii. The square

```
          Fr_X
     X ────────▶ X
     │           │
   φ̄ │           │ φ̄
     ▼           ▼
     Y ────────▶ Y
          Fr_Y
```

(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap`) has
invertible horizontal maps, so it is cartesian and its base change maps are isomorphisms
(`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIso`,
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`). This gives the exchange
isomorphisms which transport Frobenius structures along `φ̄_*`, along `Rφ̄_*` and, for an open
immersion `φ`, along the extension by zero `φ̄_!`. The matching isomorphisms for the pullbacks
are in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.GeometricFrobenius`.

The derived isomorphism is obtained from the underived one: the pullbacks along the Frobenii are
exact, so their derived functors are computed levelwise, and they are equivalences, so they
preserve K-injective complexes and the composition theorem
`CategoryTheory.Functor.rightDerivedFunctorCompIso` applies.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarGeometricFiberMapCompFrobeniusIso`:
  `φ̄_* ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_*`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso`:
  `Rφ̄_* ⋙ D(Fr_Y^*) ≅ D(Fr_X^*) ⋙ Rφ̄_*`.
- `AlgebraicGeometry.Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`:
  `φ̄_! ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_!` for an open immersion `φ`.

## Main results

- `AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso`:
  the comparison `φ̄_! ⟶ φ̄_*` commutes with these exchange isomorphisms.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The pushforward along the base change `φ̄ = φ × 𝟙 : X ⟶ Y` of a morphism of `k`-schemes
commutes with the pullbacks along the geometric Galois Frobenii: the square

```
              φ̄_*
   Sh(X) ─────────────▶ Sh(Y)
     │                    │
 Fr_X^*                Fr_Y^*
     ▼                    ▼
   Sh(X) ─────────────▶ Sh(Y)
              φ̄_*
```

commutes up to the isomorphism `φ̄_* ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_*`, whose `hom` is the base change
map `Fr_Y^* φ̄_* ⟶ φ̄_* Fr_X^*` of the square `Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`. -/
noncomputable def Etale.lowerStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_*[A] ⋙ (g.geometricGaloisFrobenius.asIso.hom)^*[A] ≅
      (f.geometricGaloisFrobenius.asIso.hom)^*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)_*[A] :=
  -- The Frobenii are isomorphisms, so the base change map is an isomorphism.
  have := Etale.isIso_baseChangeMap_of_isIso A (Scheme.Hom.commSq_geometricGaloisFrobenius φ h)
  asIso (Etale.baseChangeMap A (Scheme.Hom.commSq_geometricGaloisFrobenius φ h))

@[simp]
lemma Etale.lowerStarGeometricFiberMapCompFrobeniusIso_hom :
    (Etale.lowerStarGeometricFiberMapCompFrobeniusIso A φ h).hom =
      Etale.baseChangeMap A (Scheme.Hom.commSq_geometricGaloisFrobenius φ h) :=
  rfl

/-- The derived form of `AlgebraicGeometry.Etale.lowerStarGeometricFiberMapCompFrobeniusIso`:
the square

```
                 Rφ̄_*
   D(X_ét) ─────────────▶ D(Y_ét)
     │                      │
 D(Fr_X^*)              D(Fr_Y^*)
     ▼                      ▼
   D(X_ét) ─────────────▶ D(Y_ét)
                 Rφ̄_*
```

commutes up to the isomorphism `Rφ̄_* ⋙ D(Fr_Y^*) ≅ D(Fr_X^*) ⋙ Rφ̄_*`, the total right
derived functor of the underived one. -/
noncomputable def Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso :
    R((Scheme.Hom.geometricFiberMap φ h)_*[A]) ⋙ D((g.geometricGaloisFrobenius.asIso.hom)^*[A]) ≅
      D((f.geometricGaloisFrobenius.asIso.hom)^*[A]) ⋙
        R((Scheme.Hom.geometricFiberMap φ h)_*[A]) :=
  -- The pullbacks along the Frobenii are exact, so `D(Fr^*)` is their total right derived
  -- functor; they are equivalences, so they preserve K-injective complexes and the composition
  -- theorem applies to both sides of the underived isomorphism.
  Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorIsoMapDerivedCategory _).symm ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (Etale.lowerStarGeometricFiberMapCompFrobeniusIso A φ h) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory _) _

section OpenImmersion

variable [IsOpenImmersion φ]

/-- The extension by zero along the base change `φ̄` of an open immersion `φ` of `k`-schemes
commutes with the pullbacks along the geometric Galois Frobenii: the square

```
              φ̄_!
   Sh(X) ─────────────▶ Sh(Y)
     │                    │
 Fr_X^*                Fr_Y^*
     ▼                    ▼
   Sh(X) ─────────────▶ Sh(Y)
              φ̄_!
```

commutes up to the isomorphism `φ̄_! ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_!`. Its `hom`
`Fr_Y^* φ̄_! ⟶ φ̄_! Fr_X^*` is the inverse of the base change map
`φ̄_! Fr_X^* ⟶ Fr_Y^* φ̄_!` (`AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`) of
the square `Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`. -/
noncomputable def Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_!open[A] ⋙ (g.geometricGaloisFrobenius.asIso.hom)^*[A] ≅
      (f.geometricGaloisFrobenius.asIso.hom)^*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)_!open[A] :=
  -- The square is cartesian, so the base change map is an isomorphism.
  have := Etale.isIso_openImmersionLowerShriekBaseChangeMap A
    (Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap φ h)
  (asIso (Etale.openImmersionLowerShriekBaseChangeMap A
    (Scheme.Hom.commSq_geometricGaloisFrobenius φ h))).symm

@[simp]
lemma Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso_inv :
    (Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso A φ h).inv =
      Etale.openImmersionLowerShriekBaseChangeMap A
        (Scheme.Hom.commSq_geometricGaloisFrobenius φ h) :=
  rfl

/-- The comparison `φ̄_! ⟶ φ̄_*` commutes with the Frobenius exchange isomorphisms
`AlgebraicGeometry.Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso` (`e_!`) and
`AlgebraicGeometry.Etale.lowerStarGeometricFiberMapCompFrobeniusIso` (`e_*`): the square

```
                  Fr_Y^* (can)
  Fr_Y^* ∘ φ̄_! ────────────────▶ Fr_Y^* ∘ φ̄_*
       │                              │
   e_! │                              │ e_*
       ▼                              ▼
  φ̄_! ∘ Fr_X^* ────────────────▶ φ̄_* ∘ Fr_X^*
                  can Fr_X^*
```

commutes, where `can` is `AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStar`. -/
@[reassoc]
lemma Etale.openImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso :
    Functor.whiskerRight
        (Etale.openImmersionLowerShriekToLowerStar A (Scheme.Hom.geometricFiberMap φ h))
        (g.geometricGaloisFrobenius.asIso.hom)^*[A] ≫
      (Etale.lowerStarGeometricFiberMapCompFrobeniusIso A φ h).hom =
    (Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso A φ h).hom ≫
      Functor.whiskerLeft (f.geometricGaloisFrobenius.asIso.hom)^*[A]
        (Etale.openImmersionLowerShriekToLowerStar A (Scheme.Hom.geometricFiberMap φ h)) := by
  rw [← Etale.openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap A
      (Scheme.Hom.commSq_geometricGaloisFrobenius φ h),
    ← Etale.lowerStarGeometricFiberMapCompFrobeniusIso_hom,
    ← Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso_inv, Iso.hom_inv_id_assoc]

end OpenImmersion

end AlgebraicGeometry
