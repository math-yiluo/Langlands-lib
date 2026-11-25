/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Derived

/-!
# The tensor comparison of the derived pullback

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison g`: the comparison
  `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, and
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso g`: it is a natural isomorphism.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarUnitIso g`: the canonical `Lg^* Λ_Y ≅ Λ_Z`.

See `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal` for an
overview.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
section

open DerivedCategory Functor.OplaxMonoidal

variable [ProEtale.UpperStarPreservesFlat A]

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` of bifunctors,
of type `D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`, obtained by deriving the oplax monoidal
structure `δ` of `g^*`. It is the unique natural transformation such that, for `K, M` in
`K(Y_proét)`, the square
```
  Lg^*(Qh K ⊗ᴸ Qh M) ──comparison──▶ Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M)
          │                                    │
          │ Lg^*(μ Qh) ≫ counit                │ derivedTensorLeftDerivedUpperStarCounit
          ▼                                    ▼
   Qh(g^*(K ⊗ M)) ─────────Qh(δ g^*)──────▶ Qh(g^*K ⊗ g^*M)
```
commutes, the left vertical arrow being `leftDerivedUpperStarDerivedTensorCounit`. -/
noncomputable def leftDerivedUpperStarTensorComparison :
    leftDerivedUpperStarDerivedTensor A g ⟶ derivedTensorLeftDerivedUpperStar A g :=
  Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh)

/-- The natural isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` of bifunctors,
of type `D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`, whose underlying morphism is
`leftDerivedUpperStarTensorComparison`. -/
noncomputable def leftDerivedUpperStarTensorNatIso :
    leftDerivedUpperStarDerivedTensor A g ≅ derivedTensorLeftDerivedUpperStar A g :=
  -- `δ` is an isomorphism since `g^*` is strong monoidal.
  Functor.leftDerived₂NatIso _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (asIso (Functor.postcompose₂MapWhiskeringLeft₂
      (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh))

@[simp]
lemma leftDerivedUpperStarTensorNatIso_hom :
    (leftDerivedUpperStarTensorNatIso A g).hom = leftDerivedUpperStarTensorComparison A g :=
  rfl

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` is an isomorphism. -/
instance isIso_leftDerivedUpperStarTensorComparison :
    IsIso (leftDerivedUpperStarTensorComparison A g) :=
  (leftDerivedUpperStarTensorNatIso A g).isIso_hom

/-- The isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` in `D(Z_proét)`, for `K, M` in `D(Y_proét)`. -/
noncomputable def leftDerivedUpperStarTensorIso
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    L((g)^*[A]).obj (((-⊗ᴸ-(Y)[A]).obj K).obj M) ≅
      ((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).obj (L((g)^*[A]).obj M) :=
  ((leftDerivedUpperStarTensorNatIso A g).app K).app M

@[simp]
lemma leftDerivedUpperStarTensorIso_hom
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (leftDerivedUpperStarTensorIso A g K M).hom =
      ((leftDerivedUpperStarTensorComparison A g).app K).app M :=
  rfl

end

/-- The canonical identification `Lg^* Λ_Y ≅ Λ_Z` of the units.

The unit `Λ_Y` is the image in `D(Y_proét)` of the unit sheaf placed in degree `0`. Since `g^*` is
exact, `Lg^*` is computed by applying `g^*` degreewise, and `g^*` sends the unit sheaf of `Y`
to that of `Z` because it is strong monoidal. -/
noncomputable def leftDerivedUpperStarUnitIso : (L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (leftDerivedUpperStarIsoMapDerivedCategory A g).app _ ≪≫
    (g)^*[A].mapDerivedCategory.mapIso
      ((DerivedCategory.quotientCompQhIso (Sheaf (Scheme.ProEt.topology Y) A)).app _) ≪≫
    ((g)^*[A].mapDerivedCategoryFactors).app _ ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).app _) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso (Functor.Monoidal.εIso (g)^*[A]).symm) ≪≫
    ((DerivedCategory.quotientCompQhIso (Sheaf (Scheme.ProEt.topology Z) A)).app _).symm

/-- The derived pullback preserves the unit, `Lg^* Λ_Y ≅ Λ_Z`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarUnitIso`). -/
theorem nonempty_iso_leftDerivedUpperStar_unit :
    Nonempty ((L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) :=
  ⟨leftDerivedUpperStarUnitIso A g⟩

end ProEtale

end AlgebraicGeometry
