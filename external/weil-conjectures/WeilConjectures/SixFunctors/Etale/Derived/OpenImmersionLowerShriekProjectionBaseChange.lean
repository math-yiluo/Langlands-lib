/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-!
# The projection formula for the extension by zero commutes with base change

For a cartesian square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the
projection formula `j_!(K ⊗ᴸ Lj^*M) ≅ j_!K ⊗ᴸ M`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionMap`) commutes with the
derived base change isomorphism `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso`) and the tensor
comparisons of the derived pullbacks.

## Main results

- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionMap_baseChange`: the
  compatibility.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

/-- Transport tensor compatibility of a square along isomorphisms of its vertical functors.
The calculation only uses naturality in the first tensor variable. -/
private lemma tensorComparison_square_transport
    {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory D₁] [MonoidalCategory D₂]
    {F₁ G₁ : D₁ ⥤ C₁} {F₂ G₂ : D₂ ⥤ C₂} (U : C₁ ⥤ C₂) (V : D₁ ⥤ D₂)
    (e₁ : F₁ ≅ G₁) (e₂ : F₂ ≅ G₂) (σ : V ⋙ F₂ ≅ F₁ ⋙ U)
    (δ₁ : ∀ X Y, F₁.obj (X ⊗ Y) ≅ F₁.obj X ⊗ F₁.obj Y)
    (δ₂ : ∀ X Y, F₂.obj (X ⊗ Y) ≅ F₂.obj X ⊗ F₂.obj Y)
    (ψU : ∀ X Y, U.obj (X ⊗ Y) ⟶ U.obj X ⊗ U.obj Y)
    (ψV : ∀ X Y, V.obj (X ⊗ Y) ⟶ V.obj X ⊗ V.obj Y)
    (hU : ∀ {P Q} (f : P ⟶ Q) R, ψU P R ≫ U.map f ▷ U.obj R =
      U.map (f ▷ R) ≫ ψU Q R)
    (X Y : D₁)
    (hσ : F₂.map (ψV X Y) ≫ (δ₂ (V.obj X) (V.obj Y)).hom ≫
        (σ.hom.app X ⊗ₘ σ.hom.app Y) =
      σ.hom.app (X ⊗ Y) ≫ U.map (δ₁ X Y).hom ≫ ψU (F₁.obj X) (F₁.obj Y)) :
    U.map (e₁.inv.app X ▷ F₁.obj Y ≫ (δ₁ X Y).inv ≫ e₁.hom.app (X ⊗ Y)) ≫
        U.map (e₁.inv.app (X ⊗ Y)) ≫ σ.inv.app (X ⊗ Y) ≫ e₂.hom.app (V.obj (X ⊗ Y)) ≫
        G₂.map (ψV X Y) =
      ψU (G₁.obj X) (F₁.obj Y) ≫
        (U.map (e₁.inv.app X) ≫ σ.inv.app X ≫ e₂.hom.app (V.obj X)) ▷ U.obj (F₁.obj Y) ≫
        G₂.obj (V.obj X) ◁ σ.inv.app Y ≫
        (e₂.inv.app (V.obj X) ▷ F₂.obj (V.obj Y) ≫
          (δ₂ (V.obj X) (V.obj Y)).inv ≫ e₂.hom.app (V.obj X ⊗ V.obj Y)) := by
  have key : U.map (δ₁ X Y).inv ≫ σ.inv.app (X ⊗ Y) ≫ F₂.map (ψV X Y) =
      ψU (F₁.obj X) (F₁.obj Y) ≫ (σ.inv.app X ⊗ₘ σ.inv.app Y) ≫
        (δ₂ (V.obj X) (V.obj Y)).inv := by
    rw [← cancel_epi (U.map (δ₁ X Y).hom), ← Functor.map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [← Category.assoc]
    rw [Iso.eq_comp_inv, ← cancel_mono (σ.hom.app X ⊗ₘ σ.hom.app Y)]
    simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app]
    rw [hσ]
    erw [Iso.inv_hom_id_app_assoc, id_tensorHom_id, Category.comp_id]
  simp only [Functor.map_comp, comp_whiskerRight, Category.assoc]
  rw [← U.map_comp_assoc (e₁.hom.app (X ⊗ Y)) (e₁.inv.app (X ⊗ Y)),
    e₁.hom_inv_id_app, U.map_id, Category.id_comp]
  rw [← e₂.hom.naturality (ψV X Y), reassoc_of% key, reassoc_of% (hU (e₁.inv.app X) _)]
  rw [← whisker_exchange_assoc]
  erw [← comp_whiskerRight_assoc (e₂.hom.app (V.obj X)) (e₂.inv.app (V.obj X)), e₂.hom_inv_id_app,
    id_whiskerRight, Category.id_comp, tensorHom_def, Category.assoc]
  rfl

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Underived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

omit [HasSmallSiteSheafify A] [IsOpenImmersion j] [IsOpenImmersion j'] in
/-- The square isomorphism of pullbacks does not depend on the chosen composite. -/
lemma upperStarComp_symm_trans_eq {k₁ k₂ : U' ⟶ Z} (h₁ : k₁ = g' ≫ j) (h₁' : k₁ = j' ≫ g'')
    (h₂ : k₂ = g' ≫ j) (h₂' : k₂ = j' ≫ g'') :
    (upperStarComp A g' j k₁ h₁).symm ≪≫ upperStarComp A j' g'' k₁ h₁' =
      (upperStarComp A g' j k₂ h₂).symm ≪≫ upperStarComp A j' g'' k₂ h₂' := by
  subst h₁ h₂
  rfl

/-- The square isomorphism `j^* ⋙ g'^* ≅ g''^* ⋙ j'^*` of a commutative square
`g' ≫ j = j' ≫ g''`, computed with the composite `g' ≫ j`. -/
noncomputable abbrev openImmersionSquareIso (sq : CommSq g' j' j g'') :
    (j)^*[A] ⋙ (g')^*[A] ≅ (g'')^*[A] ⋙ (j')^*[A] :=
  (upperStarComp A g' j).symm ≪≫ upperStarComp A j' g'' (g' ≫ j) sq.w

omit [HasSmallSiteSheafify A] in
lemma unit_map_openImmersionLowerShriekBaseChangeMap_app' (sq : CommSq g' j' j g'')
    (F : Sheaf U.smallEtaleTopology A) :
    (openImmersionLowerShriekUpperStarAdjunction A j').unit.app ((g')^*[A].obj F) ≫
        (j')^*[A].map ((openImmersionLowerShriekBaseChangeMap A sq).app F) =
      (g')^*[A].map ((openImmersionLowerShriekUpperStarAdjunction A j).unit.app F) ≫
        (openImmersionSquareIso A sq).hom.app ((j)_!open[A].obj F) := by
  rw [unit_map_openImmersionLowerShriekBaseChangeMap_app]
  congr 2
  exact congrArg Iso.hom (upperStarComp_symm_trans_eq A _ _ _ _)

end Underived

section Derived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The derived base change isomorphism for the extension by zero is the mate of the derived
square isomorphism of pullbacks, for the adjunctions `Dj_! ⊣ Dj^*` and `Dj'_! ⊣ Dj'^*`. -/
lemma mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.app (D((g')^*[A]).obj K) ≫
        D((j')^*[A]).map
          ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K) =
      D((g')^*[A]).map ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso (openImmersionSquareIso A hsq.toCommSq)).hom.app
          (D((j)_!open[A]).obj K) :=
  Adjunction.mapDerivedCategoryAdjunction_mate (openImmersionLowerShriekUpperStarAdjunction A j)
    (openImmersionLowerShriekUpperStarAdjunction A j') (openImmersionSquareIso A hsq.toCommSq)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A hsq))
    (unit_map_openImmersionLowerShriekBaseChangeMap_app' A hsq.toCommSq) K

/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` of a commutative square
`g' ≫ j = j' ≫ g''`: the isomorphism induced on derived categories by the square isomorphism of
pullbacks, read through `Lg^* ≅ Dg^*`. -/
noncomputable def derivedOpenImmersionSquareMap (sq : CommSq g' j' j g'') :
    D((j)^*[A]) ⋙ L((g')^*[A]) ⟶ L((g'')^*[A]) ⋙ D((j')^*[A]) :=
  Functor.whiskerLeft D((j)^*[A]) (leftDerivedUpperStarIsoMapDerivedCategory A g').hom ≫
    (Functor.mapDerivedCategorySquareIso (openImmersionSquareIso A sq)).hom ≫
    Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g'').inv D((j')^*[A])

omit [HasSmallSiteSheafify A] in
/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` is the inverse of the square isomorphism
`Lg''^* ⋙ Lj'^* ≅ Lj^* ⋙ Lg'^*` of the derived pullbacks, read through `Lj^* ≅ Dj^*` and
`Lj'^* ≅ Dj'^*`. -/
lemma derivedOpenImmersionSquareMap_app (sq : CommSq g' j' j g'')
    (Y : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (derivedOpenImmersionSquareMap A sq).app Y =
      L((g')^*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y) ≫
        (derivedSquareUpperStarIso A sq).inv.app Y ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j').hom.app (L((g'')^*[A]).obj Y) := by
  have hnat := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y)
  simp only [derivedOpenImmersionSquareMap, derivedSquareUpperStarIso, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory] at hnat
  rw [reassoc_of% hnat, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The derived base change isomorphism for the extension by zero is the mate of the square map
`derivedOpenImmersionSquareMap`. -/
lemma unit_map_derivedOpenImmersionLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.app (L((g')^*[A]).obj K) ≫
        D((j')^*[A]).map ((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K) =
      L((g')^*[A]).map ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) ≫
        (derivedOpenImmersionSquareMap A hsq.toCommSq).app (D((j)_!open[A]).obj K) := by
  have h₁ := (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app K)
  have h₂ := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K)
  dsimp at h₁ h₂
  simp only [derivedOpenImmersionLowerShriekBaseChangeIso, derivedOpenImmersionSquareMap,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Functor.map_comp]
  rw [← reassoc_of% h₁, reassoc_of% (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate
    A hsq K), reassoc_of% h₂]
  rfl

variable [Etale.UpperStarPreservesFlat A]

omit [HasSmallSiteSheafify A] in
/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` and the square isomorphism of the derived
pullbacks are compatible with the comparisons `Dj^*X ⊗ᴸ Lj^*Y ≅ Dj^*(X ⊗ᴸ Y)` and the tensor
comparisons of the derived pullbacks. -/
lemma derivedOpenImmersionSquareMap_tensor (sq : CommSq g' j' j g'')
    (X Y : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    L((g')^*[A]).map (((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app X).app Y) ≫
        (derivedOpenImmersionSquareMap A sq).app (((-⊗ᴸ-(Z)[A]).obj X).obj Y) ≫
        D((j')^*[A]).map (((leftDerivedUpperStarTensorComparison A g'').app X).app Y) =
      ((leftDerivedUpperStarTensorComparison A g').app (D((j)^*[A]).obj X)).app
          (L((j)^*[A]).obj Y) ≫
        ((-⊗ᴸ-(U')[A]).map ((derivedOpenImmersionSquareMap A sq).app X)).app _ ≫
        ((-⊗ᴸ-(U')[A]).obj _).map ((derivedSquareUpperStarIso A sq).inv.app Y) ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A j').hom.app
          (L((g'')^*[A]).obj X)).app (L((g'')^*[A]).obj Y) := by
  rw [derivedOpenImmersionSquareMap_app, derivedOpenImmersionSquareMap_app]
  simp only [mapDerivedCategoryUpperStarDerivedTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Functor.whiskeringLeft₂_map_app_app_app_app,
    Functor.postcompose₂_map_app_app_app, derivedTensor, curriedTensor_map_app,
    curriedTensor_obj_map, Category.assoc]
  exact tensorComparison_square_transport L((g')^*[A]) L((g'')^*[A])
      (leftDerivedUpperStarIsoMapDerivedCategory A j)
      (leftDerivedUpperStarIsoMapDerivedCategory A j') (derivedSquareUpperStarIso A sq)
      (leftDerivedUpperStarTensorIso A j) (leftDerivedUpperStarTensorIso A j')
      (fun P Q ↦ ((leftDerivedUpperStarTensorComparison A g').app P).app Q)
      (fun P Q ↦ ((leftDerivedUpperStarTensorComparison A g'').app P).app Q)
      (fun {P Q} f R ↦ by
        simpa only [CategoryTheory.Functor.map_id, tensorHom_id] using
          leftDerivedUpperStarTensorComparison_naturality A g' f (𝟙 R))
      X Y (derivedSquareUpperStarIso_hom_tensor A sq X Y)

/-- **The projection formula for the extension by zero commutes with base change**: for a
cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, `K` in `D(U_ét)` and `M` in
`D(Z_ét)`, the square
```
Dj'_!Lg'^*(K ⊗ᴸ Lj^*M) ──≅──▶ Lg''^*Dj_!(K ⊗ᴸ Lj^*M) ──Lg''^* π──▶ Lg''^*(Dj_!K ⊗ᴸ M)
          │                                                              │
          ▼                                                              ▼
Dj'_!(Lg'^*K ⊗ᴸ Lj'^*Lg''^*M) ──π──▶ Dj'_!Lg'^*K ⊗ᴸ Lg''^*M ──≅ ⊗ 1──▶ Lg''^*Dj_!K ⊗ᴸ Lg''^*M
```
commutes, where `π` is the projection map, the horizontal isomorphisms are the base change
isomorphism, and the vertical arrows are the tensor comparisons of the derived pullbacks
followed, on the left, by `Lg'^*Lj^* ≅ Lj'^*Lg''^*`. -/
lemma derivedOpenImmersionLowerShriekProjectionMap_baseChange (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app
          (((-⊗ᴸ-(U)[A]).obj K).obj (L((j)^*[A]).obj M)) ≫
        L((g'')^*[A]).map (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A g'').app (D((j)_!open[A]).obj K)).app M =
      D((j')_!open[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((j)^*[A]).obj M)) ≫
        D((j')_!open[A]).map (((-⊗ᴸ-(U')[A]).obj (L((g')^*[A]).obj K)).map
          ((derivedSquareUpperStarIso A hsq.toCommSq).inv.app M)) ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j').app (L((g')^*[A]).obj K)).app
          (L((g'')^*[A]).obj M) ≫
        ((-⊗ᴸ-(Z')[A]).map ((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K)).app
          (L((g'')^*[A]).obj M) :=
  Adjunction.projectionMap_mate (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j') L((j)^*[A]) L((j')^*[A])
    (mapDerivedCategoryUpperStarDerivedTensorIso A j).hom
    (mapDerivedCategoryUpperStarDerivedTensorIso A j').hom
    (leftDerivedUpperStarTensorComparison A g') (leftDerivedUpperStarTensorComparison A g'')
    (derivedOpenImmersionSquareMap A hsq.toCommSq) (derivedSquareUpperStarIso A hsq.toCommSq).inv
    (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom
    (unit_map_derivedOpenImmersionLowerShriekBaseChangeIso A hsq)
    (derivedOpenImmersionSquareMap_tensor A hsq.toCommSq) K M

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The inverse form of `derivedOpenImmersionLowerShriekProjectionMap_baseChange`, with the
blueprint's projection map `j_!K ⊗ᴸ M ⟶ j_!(K ⊗ᴸ Lj^*M)`. -/
lemma derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange
    (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (leftDerivedUpperStarTensorIso A g'' (D((j)_!open[A]).obj K) M).inv ≫
        L((g'')^*[A]).map (((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app M) ≫
        (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).inv.app
          (((-⊗ᴸ-(U)[A]).obj K).obj (L((j)^*[A]).obj M)) =
      ((-⊗ᴸ-(Z')[A]).map ((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).inv.app K)).app
          (L((g'')^*[A]).obj M) ≫
        ((derivedOpenImmersionLowerShriekProjectionIso A j').inv.app (L((g')^*[A]).obj K)).app
          (L((g'')^*[A]).obj M) ≫
        D((j')_!open[A]).map (((-⊗ᴸ-(U')[A]).obj (L((g')^*[A]).obj K)).map
          ((derivedSquareUpperStarIso A hsq.toCommSq).hom.app M)) ≫
        D((j')_!open[A]).map (leftDerivedUpperStarTensorIso A g' K (L((j)^*[A]).obj M)).inv := by
  have h := derivedOpenImmersionLowerShriekProjectionMap_baseChange A hsq K M
  rw [← cancel_epi (leftDerivedUpperStarTensorIso A g'' (D((j)_!open[A]).obj K) M).hom,
    Iso.hom_inv_id_assoc, ← cancel_epi (L((g'')^*[A]).map
      (((derivedOpenImmersionLowerShriekProjectionIso A j).hom.app K).app M)),
    ← Functor.map_comp_assoc, ← NatTrans.comp_app, Iso.hom_inv_id_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← cancel_epi ((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app _),
    Iso.hom_inv_id_app]
  erw [reassoc_of% h]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← derivedOpenImmersionLowerShriekProjectionIso_hom, Iso.hom_inv_id_app, NatTrans.id_app,
    Category.id_comp, ← Functor.map_comp, ← Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← leftDerivedUpperStarTensorIso_hom, Iso.hom_inv_id]
  exact (CategoryTheory.Functor.map_id D((j')_!open[A]) _).symm

end Derived

end Etale

end AlgebraicGeometry
