/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# The mixed-support cup product and exchange maps

For a commutative square `g ≫ a = a ≫ h` and any exchange map `Ex : Ra_! ⋙ Lh^* ⟶ Lg^* ⋙ Ra_!`
compatible with the projection maps, the mixed-support cup product
`Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)` intertwines the data induced by `Ex`, the derived base change
map `Ex_*` and Weil data `φ`, `ψ`
(`AlgebraicGeometry.Etale.mixedSupportCupProduct_exchange`). The proof goes through the general form
`AlgebraicGeometry.Etale.projectionMap_exchange`, where the counit `La^* Ra_* L ⟶ L` is replaced by
any morphism `La^* M ⟶ L`.
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
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

namespace Etale

variable {X Y : Scheme.{u}} {a : X ⟶ Y} [HasCompactification a] {g : X ⟶ X} {h : Y ⟶ Y}

variable (a) in
/-- Naturality of the projection map `Ra_!K ⊗ᴸ M ⟶ Ra_!(K ⊗ᴸ La^*M)` in `K`. -/
@[reassoc]
lemma projectionMap_naturality_left {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (φ : K ⟶ K') (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensor A Y).map ((R(a)_![A]).map φ)).app M ≫ ((projectionMap A a).app K').app M =
      ((projectionMap A a).app K).app M ≫
        (R(a)_![A]).map (((derivedTensor A X).map φ).app ((L((a)^*[A])).obj M)) :=
  congr_app ((projectionMap A a).naturality φ) M

variable (a) in
/-- Naturality of the projection map `Ra_!K ⊗ᴸ M ⟶ Ra_!(K ⊗ᴸ La^*M)` in `M`. -/
@[reassoc]
lemma projectionMap_naturality_right (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M M' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (u : M ⟶ M') :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map u ≫ ((projectionMap A a).app K).app M' =
      ((projectionMap A a).app K).app M ≫
        (R(a)_![A]).map (((derivedTensor A X).obj K).map ((L((a)^*[A])).map u)) :=
  ((projectionMap A a).app K).naturality u

/-- The mixed-support cup product with the counit `La^* Ra_* L ⟶ L` replaced by any morphism
`e : La^* M ⟶ L` is compatible with exchange maps: the general form of
`AlgebraicGeometry.Etale.mixedSupportCupProduct_exchange`, for a morphism `u : Lh^* M ⟶ M`
compatible with `e`, `ψ` and the square isomorphism (hypothesis `he`). -/
lemma projectionMap_exchange (sq : CommSq g a a h)
    (Ex : R(a)_![A] ⋙ L((h)^*[A]) ⟶ L((g)^*[A]) ⋙ R(a)_![A])
    (hEx : ∀ (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
      (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      L((h)^*[A]).map (((projectionMap A a).app K).app M) ≫
          Ex.app (((derivedTensor A X).obj K).obj (L((a)^*[A]).obj M)) ≫
          (R(a)_![A]).map (((leftDerivedUpperStarTensorComparison A g).app K).app
            (L((a)^*[A]).obj M)) ≫
          (R(a)_![A]).map (((derivedTensor A X).obj (L((g)^*[A]).obj K)).map
            (derivedSquareUpperStarIsoInvApp A sq M)) =
        ((leftDerivedUpperStarTensorComparison A h).app ((R(a)_![A]).obj K)).app M ≫
          ((derivedTensor A Y).map (Ex.app K)).app (L((h)^*[A]).obj M) ≫
          ((projectionMap A a).app (L((g)^*[A]).obj K)).app (L((h)^*[A]).obj M))
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (e : (L((a)^*[A])).obj M ⟶ L)
    (u : (L((h)^*[A])).obj M ⟶ M)
    (φ : (L((g)^*[A])).obj K ⟶ K) (ψ : (L((g)^*[A])).obj L ⟶ L)
    (he : (L((a)^*[A])).map u ≫ e =
      (derivedSquareUpperStarIso A sq).hom.app M ≫ (L((g)^*[A])).map e ≫ ψ) :
    (L((h)^*[A])).map (((projectionMap A a).app K).app M ≫
        (R(a)_![A]).map (((derivedTensor A X).obj K).map e)) ≫
        (Ex.app (((derivedTensor A X).obj K).obj L) ≫
          (R(a)_![A]).map ((leftDerivedUpperStarTensorIso A g K L).hom ≫
            ((derivedTensor A X).map φ).app _ ≫ ((derivedTensor A X).obj K).map ψ)) =
      ((leftDerivedUpperStarTensorIso A h ((R(a)_![A]).obj K) M).hom ≫
          ((derivedTensor A Y).map (Ex.app K ≫ (R(a)_![A]).map φ)).app _ ≫
          ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map u) ≫
        ((projectionMap A a).app K).app M ≫
          (R(a)_![A]).map (((derivedTensor A X).obj K).map e) := by
  have e₁ := Ex.naturality (((derivedTensor A X).obj K).map e)
  have e₂ := ((leftDerivedUpperStarTensorComparison A g).app K).naturality e
  have e₃ := hEx K M
  have e₇ := (((derivedTensor A Y).map ((R(a)_![A]).map φ)).naturality u).symm
  have e₈ := ((derivedTensor A X).map φ).naturality
  dsimp at e₁ e₂ e₇ e₈ ⊢
  have e₃' : L((h)^*[A]).map (((projectionMap A a).app K).app M) ≫
      Ex.app (((derivedTensor A X).obj K).obj (L((a)^*[A]).obj M)) ≫
        (R(a)_![A]).map (((leftDerivedUpperStarTensorComparison A g).app K).app
          (L((a)^*[A]).obj M)) =
      ((leftDerivedUpperStarTensorComparison A h).app ((R(a)_![A]).obj K)).app M ≫
        ((derivedTensor A Y).map (Ex.app K)).app (L((h)^*[A]).obj M) ≫
        ((projectionMap A a).app (L((g)^*[A]).obj K)).app (L((h)^*[A]).obj M) ≫
        (R(a)_![A]).map (((derivedTensor A X).obj (L((g)^*[A]).obj K)).map
          ((derivedSquareUpperStarIso A sq).hom.app M)) := by
    rw [← reassoc_of% e₃]
    simp only [← Functor.map_comp, derivedSquareUpperStarIsoInvApp, Iso.inv_hom_id_app,
      Functor.comp_obj, CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [Functor.map_comp, Category.assoc, reassoc_of% e₁, ← Functor.map_comp, reassoc_of% e₂,
    Functor.map_comp, reassoc_of% e₃']
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% e₇, projectionMap_naturality_left_assoc, projectionMap_naturality_right_assoc]
  simp only [← Functor.map_comp]
  congr 4
  rw [← Functor.map_comp_assoc, reassoc_of% e₈, reassoc_of% e₈]
  simp only [← Functor.map_comp, he, Category.assoc]

/-- **The mixed-support cup product is compatible with exchange maps**: for an exchange map `Ex`
compatible with the projection maps (hypothesis `hEx`), the cup product intertwines
`Ex ≫ Ra_!(φ ⊗ ψ)` and `(Ex ≫ Ra_! φ) ⊗ (Ex_* ≫ Ra_* ψ)`. -/
theorem mixedSupportCupProduct_exchange (sq : CommSq g a a h)
    (Ex : R(a)_![A] ⋙ L((h)^*[A]) ⟶ L((g)^*[A]) ⋙ R(a)_![A])
    (hEx : ∀ (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
      (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      L((h)^*[A]).map (((projectionMap A a).app K).app M) ≫
          Ex.app (((derivedTensor A X).obj K).obj (L((a)^*[A]).obj M)) ≫
          (R(a)_![A]).map (((leftDerivedUpperStarTensorComparison A g).app K).app
            (L((a)^*[A]).obj M)) ≫
          (R(a)_![A]).map (((derivedTensor A X).obj (L((g)^*[A]).obj K)).map
            (derivedSquareUpperStarIsoInvApp A sq M)) =
        ((leftDerivedUpperStarTensorComparison A h).app ((R(a)_![A]).obj K)).app M ≫
          ((derivedTensor A Y).map (Ex.app K)).app (L((h)^*[A]).obj M) ≫
          ((projectionMap A a).app (L((g)^*[A]).obj K)).app (L((h)^*[A]).obj M))
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (φ : (L((g)^*[A])).obj K ⟶ K) (ψ : (L((g)^*[A])).obj L ⟶ L) :
    (L((h)^*[A])).map (mixedSupportCupProduct A a K L) ≫
        (Ex.app (((derivedTensor A X).obj K).obj L) ≫
          (R(a)_![A]).map ((leftDerivedUpperStarTensorIso A g K L).hom ≫
            ((derivedTensor A X).map φ).app _ ≫ ((derivedTensor A X).obj K).map ψ)) =
      ((leftDerivedUpperStarTensorIso A h ((R(a)_![A]).obj K) ((R((a)_*[A])).obj L)).hom ≫
          ((derivedTensor A Y).map (Ex.app K ≫ (R(a)_![A]).map φ)).app _ ≫
          ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map
            ((derivedBaseChangeMap A sq).app L ≫ (R((a)_*[A])).map ψ)) ≫
        mixedSupportCupProduct A a K L := by
  unfold mixedSupportCupProduct
  exact projectionMap_exchange A sq Ex hEx K L _ _ _ φ ψ
    (by
      simp only [Functor.map_comp, Category.assoc]
      erw [(derivedUpperStarLowerStarAdjunction A a).counit.naturality ψ]
      exact derivedUpperStar_map_derivedBaseChangeMap_app_counit_assoc A sq L ψ)

end Etale

end AlgebraicGeometry
