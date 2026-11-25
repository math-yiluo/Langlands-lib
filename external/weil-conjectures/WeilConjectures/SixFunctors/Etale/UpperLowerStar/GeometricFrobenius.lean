/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Pullback along a base change to `k̄` commutes with the Frobenius pullbacks

Let `k` be a finite field, `φ : X₀ ⟶ Y₀` a morphism of `k`-schemes and `φ̄ = φ × 𝟙 : X ⟶ Y` its
base change to the geometric fibers. Since `φ̄` commutes with the geometric Galois Frobenii,
`φ̄ ≫ Fr_Y = Fr_X ≫ φ̄`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius`), the pullbacks
of étale sheaves along them commute up to a canonical isomorphism, and so do the functors they
induce on derived categories. These isomorphisms transport Frobenius structures along `φ̄^*`.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarGeometricFiberMapCompFrobeniusIso`:
  `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*`.
- `AlgebraicGeometry.Etale.mapDerivedCategoryUpperStarGeometricFiberMapCompFrobeniusIso`:
  `D(φ̄^*) ⋙ D(Fr_X^*) ≅ D(Fr_Y^*) ⋙ D(φ̄^*)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

open Etale

/-- The pullback along the base change `φ̄ = φ × 𝟙 : X ⟶ Y` of a morphism of `k`-schemes commutes
with the pullbacks along the geometric Galois Frobenii: the square

```
                φ̄^*
   Sh(Y) ─────────────▶ Sh(X)
     │                    │
 Fr_Y^*                Fr_X^*
     ▼                    ▼
   Sh(Y) ─────────────▶ Sh(X)
                φ̄^*
```

commutes up to the isomorphism `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*`, induced by
`φ̄ ≫ Fr_Y = Fr_X ≫ φ̄`. -/
noncomputable def Etale.upperStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)^*[A] ⋙ (f.geometricGaloisFrobenius.asIso.hom)^*[A] ≅
      (g.geometricGaloisFrobenius.asIso.hom)^*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)^*[A] :=
  (Etale.upperStarComp _ _ _ _
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h)).symm ≪≫
    Etale.upperStarComp _ _ _

/-- The derived form of `Etale.upperStarGeometricFiberMapCompFrobeniusIso`: the square

```
                 D(φ̄^*)
   D(Y_ét) ─────────────▶ D(X_ét)
     │                      │
 D(Fr_Y^*)              D(Fr_X^*)
     ▼                      ▼
   D(Y_ét) ─────────────▶ D(X_ét)
                 D(φ̄^*)
```

commutes up to the isomorphism `D(φ̄^*) ⋙ D(Fr_X^*) ≅ D(Fr_Y^*) ⋙ D(φ̄^*)`. -/
noncomputable def Etale.mapDerivedCategoryUpperStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)^*[A].mapDerivedCategory ⋙
        (f.geometricGaloisFrobenius.asIso.hom)^*[A].mapDerivedCategory ≅
      (g.geometricGaloisFrobenius.asIso.hom)^*[A].mapDerivedCategory ⋙
        (Scheme.Hom.geometricFiberMap φ h)^*[A].mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.upperStarGeometricFiberMapCompFrobeniusIso A φ h) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry
