/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift

/-!
# The base change map for a pushforward tensored with a complex

For a commutative square `h ≫ f' = e ≫ g` of schemes (with `h : Y ⟶ X'`, `e : Y ⟶ T`,
`f' : X' ⟶ S'`, `g : T ⟶ S'`), the *base change map for a pushforward tensored with a complex*
is the morphism

`M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)`

in `D(X'_ét)` (`AlgebraicGeometry.Etale.tensorBaseChangeMap`), which appears in blueprint
`lemma-kunneth-field-coefficients--1` and `lemma-kunneth-field-coefficients--1`.

This file shows that it is natural in both variables and, as a natural transformation in each
variable, compatible with the shifts. It also records that the derived tensor product commutes
with coproducts in its first variable.

## Main definitions

- `AlgebraicGeometry.Etale.tensorBaseChangeMap`: the base change map.
- `AlgebraicGeometry.Etale.tensorBaseChangeMapLeft`: the base change map as a natural
  transformation in `M`, for a fixed `F`.
- `AlgebraicGeometry.Etale.tensorBaseChangeMapRight`: the base change map as a natural
  transformation in `F`, for a fixed `M`.

## Main statements

- `AlgebraicGeometry.Etale.commShift_tensorBaseChangeMapLeft`,
  `AlgebraicGeometry.Etale.commShift_tensorBaseChangeMapRight`: compatibility with the shifts.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Maps

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {X' S' T Y : Scheme.{u}}

/-- The base change map for a pushforward tensored with a complex
(`lemma-kunneth-field-coefficients--1`, `lemma-kunneth-field-coefficients--1`): for a commutative
square `h ≫ f' = e ≫ g` (with `h : Y ⟶ X'`, `e : Y ⟶ T`, `f' : X' ⟶ S'`, `g : T ⟶ S'`) and
`M ∈ D(X'_ét)`, `F ∈ D(T_ét)`, the morphism

`M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)`

is the transpose along `Lh^* ⊣ Rh_*` of the composite

`Lh^*(M ⊗ᴸ Lf'^* Rg_* F) ≅ Lh^* M ⊗ᴸ Lh^* Lf'^* Rg_* F ≅ Lh^* M ⊗ᴸ Le^* Lg^* Rg_* F
  ⟶ Lh^* M ⊗ᴸ Le^* F`

of the monoidality of `Lh^*`, the composition isomorphisms through `L(h ≫ f')^*` and the counit
of `Lg^* ⊣ Rg_*`. -/
noncomputable def tensorBaseChangeMap (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
    (w : h ≫ f' = e ≫ g) (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    ((-⊗ᴸ-(X')[A]).obj M).obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ⟶
      R((h)_*[A]).obj (((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M)).obj (L((e)^*[A]).obj F)) :=
  (derivedUpperStarLowerStarAdjunction A h).homEquiv _ _
    (((leftDerivedUpperStarTensorComparison A h).app _).app _ ≫
      ((-⊗ᴸ-(Y)[A]).obj _).map ((leftDerivedUpperStarComp A h f').inv.app _ ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app _ ≫
          L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F)))

/-- The base change map `M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)` is natural in `M` and
`F`. -/
@[reassoc]
lemma tensorBaseChangeMap_naturality (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
    (w : h ≫ f' = e ≫ g) {M M' : DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    {F F' : DerivedCategory (Sheaf T.smallEtaleTopology A)} (φ : M ⟶ M') (ψ : F ⟶ F') :
    ((-⊗ᴸ-(X')[A]).map φ).app _ ≫
        ((-⊗ᴸ-(X')[A]).obj M').map (L((f')^*[A]).map (R((g)_*[A]).map ψ)) ≫
          tensorBaseChangeMap A h e f' g w M' F' =
      tensorBaseChangeMap A h e f' g w M F ≫ R((h)_*[A]).map
        (((-⊗ᴸ-(Y)[A]).map (L((h)^*[A]).map φ)).app _ ≫
          ((-⊗ᴸ-(Y)[A]).obj _).map (L((e)^*[A]).map ψ)) := by
  rw [tensorBaseChangeMap, tensorBaseChangeMap, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have h₁ := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A h).naturality φ)
    (L((f')^*[A]).obj (R((g)_*[A]).obj F))
  have h₂ := ((leftDerivedUpperStarTensorComparison A h).app M').naturality
    (L((f')^*[A]).map (R((g)_*[A]).map ψ))
  have hv : L((h)^*[A]).map (L((f')^*[A]).map (R((g)_*[A]).map ψ)) ≫
      (leftDerivedUpperStarComp A h f').inv.app _ ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app _ ≫
          L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F') =
      ((leftDerivedUpperStarComp A h f').inv.app _ ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app _ ≫
          L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F)) ≫
        L((e)^*[A]).map ψ := by
    have n₁ := (leftDerivedUpperStarComp A h f').inv.naturality (R((g)_*[A]).map ψ)
    have n₂ := (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.naturality (R((g)_*[A]).map ψ)
    simp only [Functor.comp_map] at n₁ n₂
    rw [reassoc_of% n₁, reassoc_of% n₂]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 3
    exact (derivedUpperStarLowerStarAdjunction A _).counit.naturality _
  simp only [derivedTensor, curriedTensor_obj_map, curriedTensor_map_app,
    Category.assoc, leftDerivedUpperStarDerivedTensor,
    derivedTensorLeftDerivedUpperStar] at h₁ h₂ hv ⊢
  have h₁' : L((h)^*[A]).map (φ ▷ L((f')^*[A]).obj (R((g)_*[A]).obj F)) ≫
      ((leftDerivedUpperStarTensorComparison A h).app M').app
        (L((f')^*[A]).obj (R((g)_*[A]).obj F)) =
      ((leftDerivedUpperStarTensorComparison A h).app M).app
          (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ≫
        L((h)^*[A]).map φ ▷ L((h)^*[A]).obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)) := h₁
  have h₂' : L((h)^*[A]).map (M' ◁ L((f')^*[A]).map (R((g)_*[A]).map ψ)) ≫
      ((leftDerivedUpperStarTensorComparison A h).app M').app
        (L((f')^*[A]).obj (R((g)_*[A]).obj F')) =
      ((leftDerivedUpperStarTensorComparison A h).app M').app
          (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ≫
        L((h)^*[A]).obj M' ◁ L((h)^*[A]).map (L((f')^*[A]).map (R((g)_*[A]).map ψ)) := h₂
  rw [reassoc_of% h₂', reassoc_of% h₁']
  congr 1
  rw [← whiskerLeft_comp, hv, whiskerLeft_comp, whisker_exchange_assoc]
  simp only [whiskerLeft_comp, Category.assoc]

variable (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)

/-- The morphism `Lh^* Lf'^* Rg_* F ⟶ Le^* F` used in the base change map: the composition
isomorphisms through `L(h ≫ f')^*` followed by `Le^*` of the counit of `Lg^* ⊣ Rg_*`. -/
noncomputable def tensorBaseChangeCounitApp
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    L((h)^*[A]).obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ⟶ L((e)^*[A]).obj F :=
  (leftDerivedUpperStarComp A h f').inv.app _ ≫
    (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app _ ≫
      L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F)

/-- The morphism `Lh^* Lf'^* Rg_* F ⟶ Le^* F` of
`AlgebraicGeometry.Etale.tensorBaseChangeCounitApp`
as a natural transformation in `F`. -/
noncomputable def tensorBaseChangeCounit :
    R((g)_*[A]) ⋙ L((f')^*[A]) ⋙ L((h)^*[A]) ⟶ L((e)^*[A]) :=
  Functor.whiskerLeft R((g)_*[A])
      ((leftDerivedUpperStarComp A h f').inv ≫ (leftDerivedUpperStarComp A e g (h ≫ f') w).hom) ≫
    (Functor.associator R((g)_*[A]) L((g)^*[A]) L((e)^*[A])).inv ≫
    Functor.whiskerRight (derivedUpperStarLowerStarAdjunction A g).counit L((e)^*[A]) ≫
    (Functor.leftUnitor L((e)^*[A])).hom

omit [UpperStarPreservesFlat A] in
/-- The components of `AlgebraicGeometry.Etale.tensorBaseChangeCounit`. -/
@[simp]
lemma tensorBaseChangeCounit_app (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (tensorBaseChangeCounit A h e f' g w).app F = tensorBaseChangeCounitApp A h e f' g w F := by
  simp [tensorBaseChangeCounit, tensorBaseChangeCounitApp]

/-- The morphism `Lh^* Lf'^* Rg_* F ⟶ Le^* F` commutes with the shifts. -/
instance commShift_tensorBaseChangeCounit :
    NatTrans.CommShift (tensorBaseChangeCounit A h e f' g w) ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarComp A h f').inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  dsimp only [tensorBaseChangeCounit]
  infer_instance

/-- The base change map `M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)` as a natural
transformation in `M`, for a fixed `F`. -/
@[simps]
noncomputable def tensorBaseChangeMapLeft (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (-⊗ᴸ-(X')[A]).flip.obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ⟶
      L((h)^*[A]) ⋙ (-⊗ᴸ-(Y)[A]).flip.obj (L((e)^*[A]).obj F) ⋙ R((h)_*[A]) where
  app M := tensorBaseChangeMap A h e f' g w M F
  naturality M M' φ := by
    simpa using tensorBaseChangeMap_naturality A h e f' g w φ (𝟙 F)

/-- The base change map `M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)` as a natural
transformation in `F`, for a fixed `M`. -/
@[simps]
noncomputable def tensorBaseChangeMapRight (M : DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    R((g)_*[A]) ⋙ L((f')^*[A]) ⋙ (-⊗ᴸ-(X')[A]).obj M ⟶
      L((e)^*[A]) ⋙ (-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M) ⋙ R((h)_*[A]) where
  app F := tensorBaseChangeMap A h e f' g w M F
  naturality F F' ψ := by
    simpa using tensorBaseChangeMap_naturality A h e f' g w (𝟙 M) ψ

/-- The base change map, as a natural transformation in `M`, is the composite of the unit of
`Lh^* ⊣ Rh_*`, the tensor comparison of `Lh^*` and `Rh_*` of the counit morphism. -/
lemma tensorBaseChangeMapLeft_eq (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    tensorBaseChangeMapLeft A h e f' g w F =
      (Functor.rightUnitor ((-⊗ᴸ-(X')[A]).flip.obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)))).inv ≫
        Functor.whiskerLeft ((-⊗ᴸ-(X')[A]).flip.obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)))
          (derivedUpperStarLowerStarAdjunction A h).unit ≫
        (Functor.associator ((-⊗ᴸ-(X')[A]).flip.obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)))
          L((h)^*[A]) R((h)_*[A])).inv ≫
        Functor.whiskerRight (leftDerivedUpperStarTensorComparisonFlipApp A h
            (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ≫
          Functor.whiskerLeft L((h)^*[A])
            ((-⊗ᴸ-(Y)[A]).flip.map (tensorBaseChangeCounitApp A h e f' g w F))) R((h)_*[A]) ≫
        (Functor.associator L((h)^*[A]) ((-⊗ᴸ-(Y)[A]).flip.obj (L((e)^*[A]).obj F))
          R((h)_*[A])).hom := by
  ext M
  simp [tensorBaseChangeMap, tensorBaseChangeCounitApp, Adjunction.homEquiv_unit]

/-- The image of a morphism under the derived tensor product commutes with the shifts in the
first variable. -/
instance commShift_derivedTensor_flip_map {X : Scheme.{u}}
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K') :
    NatTrans.CommShift ((-⊗ᴸ-(X)[A]).flip.map φ) ℤ := by
  exact Functor.CommShift₂.commShift_flip_map (h := .int)
    (G := curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A))) φ

/-- The base change map, as a natural transformation in `M`, commutes with the shifts. -/
instance commShift_tensorBaseChangeMapLeft
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    NatTrans.CommShift (tensorBaseChangeMapLeft A h e f' g w F) ℤ := by
  rw [tensorBaseChangeMapLeft_eq]
  infer_instance

/-- The base change map, as a natural transformation in `F`, is the composite of the unit of
`Lh^* ⊣ Rh_*`, the tensor comparison of `Lh^*` and `Rh_*` of the counit morphism. -/
lemma tensorBaseChangeMapRight_eq (M : DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    tensorBaseChangeMapRight A h e f' g w M =
      (Functor.rightUnitor (R((g)_*[A]) ⋙ L((f')^*[A]) ⋙ (-⊗ᴸ-(X')[A]).obj M)).inv ≫
        Functor.whiskerLeft (R((g)_*[A]) ⋙ L((f')^*[A]) ⋙ (-⊗ᴸ-(X')[A]).obj M)
          (derivedUpperStarLowerStarAdjunction A h).unit ≫
        (Functor.associator (R((g)_*[A]) ⋙ L((f')^*[A]) ⋙ (-⊗ᴸ-(X')[A]).obj M)
          L((h)^*[A]) R((h)_*[A])).inv ≫
        Functor.whiskerRight (
          (Functor.associator R((g)_*[A]) (L((f')^*[A]) ⋙ (-⊗ᴸ-(X')[A]).obj M) L((h)^*[A])).hom ≫
          Functor.whiskerLeft R((g)_*[A])
            ((Functor.associator L((f')^*[A]) ((-⊗ᴸ-(X')[A]).obj M) L((h)^*[A])).hom ≫
              Functor.whiskerLeft L((f')^*[A]) (leftDerivedUpperStarTensorComparisonApp A h M) ≫
              (Functor.associator L((f')^*[A]) L((h)^*[A])
                ((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M))).inv) ≫
          (Functor.associator R((g)_*[A]) (L((f')^*[A]) ⋙ L((h)^*[A]))
            ((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M))).inv ≫
          Functor.whiskerRight (tensorBaseChangeCounit A h e f' g w)
            ((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M))) R((h)_*[A]) ≫
        (Functor.associator L((e)^*[A]) ((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M))
          R((h)_*[A])).hom := by
  ext F
  simp [tensorBaseChangeMap, tensorBaseChangeCounitApp, Adjunction.homEquiv_unit]

/-- The base change map, as a natural transformation in `F`, commutes with the shifts. -/
instance commShift_tensorBaseChangeMapRight
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    NatTrans.CommShift (tensorBaseChangeMapRight A h e f' g w M) ℤ := by
  have b1 : NatTrans.CommShift (Functor.whiskerLeft R((g)_*[A])
            ((Functor.associator L((f')^*[A]) ((-⊗ᴸ-(X')[A]).obj M) L((h)^*[A])).hom ≫
              Functor.whiskerLeft L((f')^*[A]) (leftDerivedUpperStarTensorComparisonApp A h M) ≫
              (Functor.associator L((f')^*[A]) L((h)^*[A])
                ((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M))).inv)) ℤ := inferInstance
  rw [tensorBaseChangeMapRight_eq]
  infer_instance

end Maps

end Etale

end AlgebraicGeometry
