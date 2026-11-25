/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# The projection map of the compactly supported direct image commutes with base change

For a cartesian square `g' ≫ f = f' ≫ g` and a compactification `c` of `f`, the projection map
`PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)`
(`AlgebraicGeometry.Etale.projectionMapOfCompactification`) commutes with the compactly supported
base change map `Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`), where `c'` is
the base changed compactification, and the tensor comparisons of the derived pullbacks.
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

namespace Etale

lemma leftDerivedUpperStarComp_symm_trans_eqToIso {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R)
    (k : T ⟶ R) (e : k = a ≫ b) :
    (leftDerivedUpperStarComp A a b).symm ≪≫
        eqToIso (congrArg (fun h : T ⟶ R ↦ L((h)^*[A])) e.symm) =
      (leftDerivedUpperStarComp A a b k e).symm := by
  subst e
  ext
  simp

lemma leftDerivedUpperStarCompactificationIso_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    leftDerivedUpperStarCompactificationIso A c =
      (leftDerivedUpperStarComp A c.i c.g f c.comm).symm :=
  leftDerivedUpperStarComp_symm_trans_eqToIso A c.i c.g f c.comm

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : CommSq g' f' f g) (c : Compactification f) (c' : Compactification f') (q : c'.Z ⟶ c.Z)
  (hi : IsPullback g' c'.i c.i q) (hp : CommSq q c'.g c.g g)

/-- The compatibility of the square isomorphisms of the derived pullbacks for the squares of a
compactification `c` of `f` and of a compactification `c'` of its base change `f'`, lying over
`c` through `q`, with the isomorphisms `L(c.i)^* L(c.g)^* ≅ Lf^*` and
`L(c'.i)^* L(c'.g)^* ≅ Lf'^*`. -/
lemma compactification_derivedSquareUpperStarIso
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((c'.i)^*[A]).map ((derivedSquareUpperStarIso A hp).hom.app L) ≫
      (derivedSquareUpperStarIso A hi.toCommSq).hom.app (L((c.g)^*[A]).obj L) ≫
      L((g')^*[A]).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L) ≫
      (derivedSquareUpperStarIso A sq).inv.app L =
    (leftDerivedUpperStarCompactificationIso A c').hom.app (L((g)^*[A]).obj L) := by
  rw [leftDerivedUpperStarCompactificationIso_eq, leftDerivedUpperStarCompactificationIso_eq]
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app_assoc A g' c.i c.g
      (g' ≫ c.i) f (g' ≫ f) rfl c.comm (by rw [Category.assoc, ← c.comm]),
    Iso.hom_inv_id_app_assoc,
    map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app_assoc A
      c'.i q c.g (g' ≫ c.i) (q ≫ c.g) (g' ≫ f) hi.w rfl (by rw [Category.assoc, ← c.comm]),
    Iso.hom_inv_id_app_assoc,
    map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app_assoc A
      c'.i c'.g g f' (q ≫ c.g) (g' ≫ f) c'.comm hp.w sq.w,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]

section

variable [Etale.UpperStarPreservesFlat A] [HasSmallSiteSheafify A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The open part of the compatibility of the projection map with the compactly supported base
change map, inside the compactification `c'` of the base change. -/
lemma projectionMapOfCompactification_baseChange_aux
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((-⊗ᴸ-(c'.Z)[A]).obj (L((q)^*[A]).obj (D((c.i)_!open[A]).obj K))).map
        ((derivedSquareUpperStarIso A hp).hom.app L) ≫
      (leftDerivedUpperStarTensorIso A q (D((c.i)_!open[A]).obj K) (L((c.g)^*[A]).obj L)).inv ≫
      L((q)^*[A]).map (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
        (L((c.g)^*[A]).obj L)) ≫
      L((q)^*[A]).map (D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
        ((leftDerivedUpperStarCompactificationIso A c).hom.app L))) ≫
      (derivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app
        (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
      D((c'.i)_!open[A]).map
        (((leftDerivedUpperStarTensorComparison A g').app K).app (L((f)^*[A]).obj L)) ≫
      D((c'.i)_!open[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
        ((derivedSquareUpperStarIso A sq).inv.app L)) =
    ((-⊗ᴸ-(c'.Z)[A]).map ((derivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K)).app
        (L((c'.g)^*[A]).obj (L((g)^*[A]).obj L)) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso A c'.i).inv.app (L((g')^*[A]).obj K)).app
        (L((c'.g)^*[A]).obj (L((g)^*[A]).obj L)) ≫
      D((c'.i)_!open[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
        ((leftDerivedUpperStarCompactificationIso A c').hom.app (L((g)^*[A]).obj L))) := by
  have oi := derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange A hi K
    (L((c.g)^*[A]).obj L)
  have n₁ := (derivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.naturality
    (((-⊗ᴸ-(X)[A]).obj K).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L))
  dsimp only [Functor.comp_map] at n₁
  rw [reassoc_of% n₁, reassoc_of% oi]
  have e₁ := ((-⊗ᴸ-(c'.Z)[A]).map ((derivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app
    K)).naturality ((derivedSquareUpperStarIso A hp).hom.app L)
  have e₂ := ((derivedOpenImmersionLowerShriekProjectionIso A c'.i).inv.app
    (L((g')^*[A]).obj K)).naturality ((derivedSquareUpperStarIso A hp).hom.app L)
  have e₃ := ((leftDerivedUpperStarTensorComparison A g').app K).naturality
    ((leftDerivedUpperStarCompactificationIso A c).hom.app L)
  have hC := compactification_derivedSquareUpperStarIso A sq c c' q hi hp L
  dsimp at e₁ e₂ e₃
  rw [reassoc_of% e₁, reassoc_of% e₂]
  simp only [← Functor.map_comp]
  congr 2
  congr 1
  rw [reassoc_of% e₃, ← leftDerivedUpperStarTensorIso_hom, Iso.inv_hom_id_assoc]
  simp only [← Functor.map_comp]
  rw [hC]

end

/-- The component `Lg'^* Lf^* L ⟶ Lf'^* Lg^* L` of the inverse of the square isomorphism of the
derived pullbacks of a commutative square, with source and target written without composite
functors. -/
noncomputable def derivedSquareUpperStarIsoInvApp
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g')^*[A]).obj (L((f)^*[A]).obj L) ⟶ L((f')^*[A]).obj (L((g)^*[A]).obj L) :=
  (derivedSquareUpperStarIso A sq).inv.app L

/-- The compactly supported base change map `Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*` for a compactification
`c'` of the base change `f'` lying over `c` through `q`: the derived base change map of the square
`q ≫ c.g = c'.g ≫ g`, whiskered by `Di_!`, followed by the inverse of the base change isomorphism
of the extension by zero for the cartesian square `g' ≫ c.i = c'.i ≫ q`. For
`c' = c.ofIsPullback sq` it is `rightDerivedLowerShriekOfCompactificationBaseChangeMap`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationBaseChangeMap' [HasSmallSiteSheafify A] :
    Rf_!(c)[A] ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ Rf_!(c')[A] :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open[A]) (derivedBaseChangeMap A hp) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedOpenImmersionLowerShriekBaseChangeIso A hi).inv R((c'.g)_*[A]) ≫
    (Functor.associator _ _ _).hom

/-- The component `Lg^* Rf_!(c) T ⟶ Rf'_!(c') Lg'^* T` of
`rightDerivedLowerShriekOfCompactificationBaseChangeMap'`, with source and target written without
composite functors. -/
noncomputable def rightDerivedLowerShriekOfCompactificationBaseChangeMapApp [HasSmallSiteSheafify A]
    (T : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    L((g)^*[A]).obj ((Rf_!(c)[A]).obj T) ⟶ (Rf_!(c')[A]).obj (L((g')^*[A]).obj T) :=
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi hp).app T

lemma rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app [HasSmallSiteSheafify A]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi hp).app K =
      (derivedBaseChangeMap A hp).app (D((c.i)_!open[A]).obj K) ≫
        R((c'.g)_*[A]).map ((derivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K) := by
  simp [rightDerivedLowerShriekOfCompactificationBaseChangeMap']

lemma rightDerivedLowerShriekOfCompactificationBaseChangeMap_eq [HasSmallSiteSheafify A]
    (sq : IsPullback g' f' f g) :
    rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c =
      rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c (c.ofIsPullback sq)
        (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq)
        (IsPullback.of_hasPullback c.g g).toCommSq :=
  rfl

section

variable [Etale.UpperStarPreservesFlat A] [HasSmallSiteSheafify A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

omit [HasSmallSiteSheafify A] in
/-- Restating an intertwining property of a morphism `κ : Rf_!(c₁) ⟶ Rf_!(c₂)` with the projection
maps. Specialising this generic statement, rather than using a specialised proof directly, keeps
the instance terms of the projection maps identical to those of other generic statements. -/
lemma projectionMapOfCompactification_comp_of_forall {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c₁ c₂ : Compactification f) (κ : Rf_!(c₁)[A] ⟶ Rf_!(c₂)[A])
    (h : ∀ (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
      (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      ((projectionMapOfCompactification A c₁).app K).app L ≫
        κ.app (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) =
      ((-⊗ᴸ-(Y)[A]).map (κ.app K)).app L ≫ ((projectionMapOfCompactification A c₂).app K).app L)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c₁).app K).app L ≫
        κ.app (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) =
      ((-⊗ᴸ-(Y)[A]).map (κ.app K)).app L ≫ ((projectionMapOfCompactification A c₂).app K).app L :=
  h K L

/-- **The projection map commutes with compactly supported base change**, for a compactification
`c'` of the base change lying over `c`. -/
theorem projectionMapOfCompactification_baseChange'
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map (((projectionMapOfCompactification A c).app K).app L) ≫
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi hp).app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
        (Rf_!(c')[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((f)^*[A]).obj L)) ≫
        (Rf_!(c')[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
          ((derivedSquareUpperStarIso A sq).inv.app L)) =
      ((leftDerivedUpperStarTensorComparison A g).app ((Rf_!(c)[A]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi
          hp).app K)).app (L((g)^*[A]).obj L) ≫
        ((projectionMapOfCompactification A c').app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj L) := by
  rw [rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app,
    projectionMapOfCompactification_app_app, projectionMapOfCompactification_app_app]
  have n₁ := (derivedBaseChangeMap A hp).naturality (D((c.i)_!open[A]).map
    (((-⊗ᴸ-(X)[A]).obj K).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L)))
  have n₂ := (derivedBaseChangeMap A hp).naturality
    (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app (L((c.g)^*[A]).obj L))
  have n₃ : ((-⊗ᴸ-(Y')[A]).map (R((c'.g)_*[A]).map
      ((derivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K))).app (L((g)^*[A]).obj L) ≫
      ((rightDerivedLowerStarProjectionMap A c'.g).app (D((c'.i)_!open[A]).obj
        (L((g')^*[A]).obj K))).app (L((g)^*[A]).obj L) =
      ((rightDerivedLowerStarProjectionMap A c'.g).app
        (L((q)^*[A]).obj (D((c.i)_!open[A]).obj K))).app (L((g)^*[A]).obj L) ≫
      R((c'.g)_*[A]).map (((-⊗ᴸ-(c'.Z)[A]).map
        ((derivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K)).app
          (L((c'.g)^*[A]).obj (L((g)^*[A]).obj L))) :=
    NatTrans.congr_app ((rightDerivedLowerStarProjectionMap A c'.g).naturality
      ((derivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K)) (L((g)^*[A]).obj L)
  have E2 := rightDerivedLowerStarProjectionMap_derivedBaseChangeMap A hp
    (D((c.i)_!open[A]).obj K) L
  have E2' : L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A c.g).app
      (D((c.i)_!open[A]).obj K)).app L) ≫ (derivedBaseChangeMap A hp).app
        (((-⊗ᴸ-(c.Z)[A]).obj (D((c.i)_!open[A]).obj K)).obj (L((c.g)^*[A]).obj L)) =
      ((leftDerivedUpperStarTensorComparison A g).app
          (R((c.g)_*[A]).obj (D((c.i)_!open[A]).obj K))).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((derivedBaseChangeMap A hp).app (D((c.i)_!open[A]).obj K))).app
          (L((g)^*[A]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap A c'.g).app
          (L((q)^*[A]).obj (D((c.i)_!open[A]).obj K))).app (L((g)^*[A]).obj L) ≫
        R((c'.g)_*[A]).map (((-⊗ᴸ-(c'.Z)[A]).obj (L((q)^*[A]).obj (D((c.i)_!open[A]).obj K))).map
          ((derivedSquareUpperStarIso A hp).hom.app L)) ≫
        R((c'.g)_*[A]).map (leftDerivedUpperStarTensorIso A q (D((c.i)_!open[A]).obj K)
          (L((c.g)^*[A]).obj L)).inv := by
    rw [← cancel_mono (R((c'.g)_*[A]).map (leftDerivedUpperStarTensorIso A q
      (D((c.i)_!open[A]).obj K) (L((c.g)^*[A]).obj L)).hom)]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
    exact E2
  have aux := projectionMapOfCompactification_baseChange_aux A sq c c' q hi hp K L
  simp only [← Functor.map_comp] at aux
  dsimp at n₁ n₂
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map, NatTrans.comp_app]
  rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% E2']
  erw [reassoc_of% n₃]
  simp only [← Functor.map_comp]
  rw [aux]
  rfl

/-- `projectionMapOfCompactification_baseChange'` with the square isomorphism written through
`derivedSquareUpperStarIsoInvApp`, so that both sides end at the same object syntactically. -/
theorem projectionMapOfCompactification_baseChange
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map (((projectionMapOfCompactification A c).app K).app L) ≫
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi hp).app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
        (Rf_!(c')[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((f)^*[A]).obj L)) ≫
        (Rf_!(c')[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
          (derivedSquareUpperStarIsoInvApp A sq L)) =
      ((leftDerivedUpperStarTensorComparison A g).app ((Rf_!(c)[A]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi
          hp).app K)).app (L((g)^*[A]).obj L) ≫
        ((projectionMapOfCompactification A c').app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj L) :=
  projectionMapOfCompactification_baseChange' A sq c c' q hi hp K L

/-- `projectionMapOfCompactification_baseChange` with the base change map written through its
plain-typed components. -/
theorem projectionMapOfCompactification_baseChange_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map (((projectionMapOfCompactification A c).app K).app L) ≫
        rightDerivedLowerShriekOfCompactificationBaseChangeMapApp A c c' q hi hp
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
        (Rf_!(c')[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((f)^*[A]).obj L)) ≫
        (Rf_!(c')[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
          (derivedSquareUpperStarIsoInvApp A sq L)) =
      ((leftDerivedUpperStarTensorComparison A g).app ((Rf_!(c)[A]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[A]).map (rightDerivedLowerShriekOfCompactificationBaseChangeMapApp A c c' q
          hi hp K)).app (L((g)^*[A]).obj L) ≫
        ((projectionMapOfCompactification A c').app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj L) :=
  projectionMapOfCompactification_baseChange' A sq c c' q hi hp K L


/-- `projectionMapOfCompactification_baseChange` followed by a comparison `κ : Rf'_!(c') ⟶ Rf'_!(e)`
intertwining the projection maps. -/
theorem projectionMapOfCompactification_baseChange_comp (e : Compactification f')
    (κ : Rf_!(c')[A] ⟶ Rf_!(e)[A])
    (hκ : ∀ (K : DerivedCategory (Sheaf X'.smallEtaleTopology A))
      (L : DerivedCategory (Sheaf Y'.smallEtaleTopology A)),
      ((projectionMapOfCompactification A c').app K).app L ≫
        κ.app (((-⊗ᴸ-(X')[A]).obj K).obj (L((f')^*[A]).obj L)) =
      ((-⊗ᴸ-(Y')[A]).map (κ.app K)).app L ≫ ((projectionMapOfCompactification A e).app K).app L)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map (((projectionMapOfCompactification A c).app K).app L) ≫
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi hp).app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
        κ.app (L((g')^*[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L))) ≫
        (Rf_!(e)[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((f)^*[A]).obj L)) ≫
        (Rf_!(e)[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
          (derivedSquareUpperStarIsoInvApp A sq L)) =
      ((leftDerivedUpperStarTensorComparison A g).app ((Rf_!(c)[A]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi
          hp).app K)).app (L((g)^*[A]).obj L) ≫
        ((-⊗ᴸ-(Y')[A]).map (κ.app (L((g')^*[A]).obj K))).app (L((g)^*[A]).obj L) ≫
        ((projectionMapOfCompactification A e).app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj L) := by
  have thm := projectionMapOfCompactification_baseChange A sq c c' q hi hp K L
  have hn₁ : κ.app (L((g')^*[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L))) ≫
      (Rf_!(e)[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
        (L((f)^*[A]).obj L)) =
      (Rf_!(c')[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
        (L((f)^*[A]).obj L)) ≫
      κ.app (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).obj (L((g')^*[A]).obj (L((f)^*[A]).obj L))) :=
    (κ.naturality _).symm
  have hn₂ : κ.app (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).obj
        (L((g')^*[A]).obj (L((f)^*[A]).obj L))) ≫
      (Rf_!(e)[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
        (derivedSquareUpperStarIsoInvApp A sq L)) =
      (Rf_!(c')[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
        (derivedSquareUpperStarIsoInvApp A sq L)) ≫
      κ.app (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).obj
        (L((f')^*[A]).obj (L((g)^*[A]).obj L))) :=
    (κ.naturality _).symm
  erw [reassoc_of% hn₁, hn₂]
  erw [reassoc_of% thm]
  rw [hκ]
  rfl

/-- `projectionMapOfCompactification_baseChange_comp` with the base change map followed by the
comparison written as a single natural transformation. -/
theorem projectionMapOfCompactification_baseChange_comp' (e : Compactification f')
    (κ : Rf_!(c')[A] ⟶ Rf_!(e)[A])
    (hκ : ∀ (K : DerivedCategory (Sheaf X'.smallEtaleTopology A))
      (L : DerivedCategory (Sheaf Y'.smallEtaleTopology A)),
      ((projectionMapOfCompactification A c').app K).app L ≫
        κ.app (((-⊗ᴸ-(X')[A]).obj K).obj (L((f')^*[A]).obj L)) =
      ((-⊗ᴸ-(Y')[A]).map (κ.app K)).app L ≫ ((projectionMapOfCompactification A e).app K).app L)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map (((projectionMapOfCompactification A c).app K).app L) ≫
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi hp ≫
          Functor.whiskerLeft _ κ).app (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
        (Rf_!(e)[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((f)^*[A]).obj L)) ≫
        (Rf_!(e)[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
          (derivedSquareUpperStarIsoInvApp A sq L)) =
      ((leftDerivedUpperStarTensorComparison A g).app ((Rf_!(c)[A]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi
          hp ≫ Functor.whiskerLeft _ κ).app K)).app (L((g)^*[A]).obj L) ≫
        ((projectionMapOfCompactification A e).app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj L) := by
  have h := projectionMapOfCompactification_baseChange_comp A sq c c' q hi hp e κ hκ K L
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, NatTrans.comp_app,
    Category.assoc] at h ⊢
  exact h
end

end Etale

end AlgebraicGeometry
