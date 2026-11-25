/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.BaseChange.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

/-!
# Derived base change for the extension by zero along an étale morphism

For a commutative square of schemes

```
  U' --j'--> Z'
  |          |
  g'         g''
  ↓          ↓
  U  --j---> Z
```

with `j` and `j'` étale, the base change map `j'_! g'^* ⟶ g''^* j_!` of the extensions by zero
(`AlgebraicGeometry.Etale.etaleLowerShriekSquareBaseChangeMap`) is the conjugate of the base
change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of the pushforwards; for a cartesian square it is an
isomorphism, by étale base change for the pushforward. All four functors being exact, it induces
an isomorphism `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` on the unbounded derived categories
(`AlgebraicGeometry.Etale.derivedEtaleLowerShriekBaseChangeIso`), which is the mate of the
square isomorphism of the derived pullbacks for the adjunctions `Dj_! ⊣ Lj^*` and
`Dj'_! ⊣ Lj'^*` (`AlgebraicGeometry.Etale.unit_map_derivedEtaleLowerShriekBaseChangeIso`).

This is the étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange`.

## Main definitions

- `AlgebraicGeometry.Etale.etaleLowerShriekSquareBaseChangeMap`
- `AlgebraicGeometry.Etale.derivedEtaleLowerShriekAdjunction`: `Dj_! ⊣ Lj^*`.
- `AlgebraicGeometry.Etale.derivedEtaleLowerShriekBaseChangeIso`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Underived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [_root_.AlgebraicGeometry.Etale j] [_root_.AlgebraicGeometry.Etale j']

/-- The base change map `j'_! g'^* ⟶ g''^* j_!` for the extensions by zero along the étale
morphisms of a commutative square `g' ≫ j = j' ≫ g''`: the conjugate of the base change map
`g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of the pushforwards, under the adjunctions
`j_! ⋙ g''^* ⊣ g''_* ⋙ j^*` and `g'^* ⋙ j'_! ⊣ j'^* ⋙ g'_*`. -/
noncomputable def etaleLowerShriekSquareBaseChangeMap (sq : CommSq g' j' j g'') :
    (g')^*[A] ⋙ etaleLowerShriek A j' inferInstance ⟶
      etaleLowerShriek A j inferInstance ⋙ (g'')^*[A] :=
  (conjugateEquiv ((etaleLowerShriekUpperStarAdjunction A j inferInstance).comp
      (upperStarLowerStarAdjunction A g''))
    ((upperStarLowerStarAdjunction A g').comp
      (etaleLowerShriekUpperStarAdjunction A j' inferInstance))).symm
    (baseChangeMap A sq.flip)

/-- **Base change for the étale extension by zero along a cartesian square**: the conjugate of
the étale base change isomorphism of the pushforwards
(`AlgebraicGeometry.Etale.isIso_baseChangeMap_flip_of_isPullback`). -/
lemma isIso_etaleLowerShriekSquareBaseChangeMap (hsq : IsPullback g' j' j g'') :
    IsIso (etaleLowerShriekSquareBaseChangeMap A hsq.toCommSq) :=
  have := isIso_baseChangeMap_flip_of_isPullback A hsq
  conjugateEquiv_symm_iso _ _ _

/-- The square isomorphism `j^* ⋙ g'^* ≅ g''^* ⋙ j'^*` of a commutative square
`g' ≫ j = j' ≫ g''`, computed with the composite `g' ≫ j`. -/
noncomputable abbrev etaleSquareUpperStarIso (sq : CommSq g' j' j g'') :
    (j)^*[A] ⋙ (g')^*[A] ≅ (g'')^*[A] ⋙ (j')^*[A] :=
  (upperStarComp A g' j).symm ≪≫ upperStarComp A j' g'' (g' ≫ j) sq.w

omit [HasSmallSiteSheafify A] in
/-- The transpose of the base change map `j'_! g'^* ⟶ g''^* j_!` under `j'_! ⊣ j'^*` is `g'^*`
of the unit of `j_! ⊣ j^*` followed by the square isomorphism. -/
lemma unit_map_etaleLowerShriekSquareBaseChangeMap_app (sq : CommSq g' j' j g'')
    (F : Sheaf U.smallEtaleTopology A) :
    (etaleLowerShriekUpperStarAdjunction A j' inferInstance).unit.app ((g')^*[A].obj F) ≫
        (j')^*[A].map ((etaleLowerShriekSquareBaseChangeMap A sq).app F) =
      (g')^*[A].map ((etaleLowerShriekUpperStarAdjunction A j inferInstance).unit.app F) ≫
        (etaleSquareUpperStarIso A sq).hom.app (etaleLowerShriek A j inferInstance |>.obj F) := by
  apply ((upperStarLowerStarAdjunction A g').homEquiv _ _).injective
  have := unit_conjugateEquiv_symm ((etaleLowerShriekUpperStarAdjunction A j inferInstance).comp
      (upperStarLowerStarAdjunction A g''))
    ((upperStarLowerStarAdjunction A g').comp
      (etaleLowerShriekUpperStarAdjunction A j' inferInstance))
    (baseChangeMap A sq.flip) F
  dsimp only [Functor.comp_obj, Functor.comp_map] at this
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, Category.assoc,
    map_unit_baseChangeMap_app] at this
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Adjunction.unit_naturality_assoc]
  refine (this.trans (Category.assoc _ _ _)).symm.trans ?_
  congr 3
  have key : ∀ (k₁ k₂ : U' ⟶ Z) (h₁ : k₁ = g' ≫ j) (h₁' : k₁ = j' ≫ g'')
      (h₂ : k₂ = g' ≫ j) (h₂' : k₂ = j' ≫ g''),
      (upperStarComp A g' j k₁ h₁).symm ≪≫ upperStarComp A j' g'' k₁ h₁' =
        (upperStarComp A g' j k₂ h₂).symm ≪≫ upperStarComp A j' g'' k₂ h₂' := by
    rintro k₁ k₂ rfl h₁' rfl h₂'
    rfl
  exact congrArg (fun e ↦ e.hom.app _) (key _ _ _ _ _ _)

end Underived

section Derived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [_root_.AlgebraicGeometry.Etale j] [_root_.AlgebraicGeometry.Etale j']

variable (j) in
/-- The levelwise derived adjunction `Dj_! ⊣ Dj^*` of the extension by zero along an étale
morphism `j`, both functors being exact. -/
noncomputable def derivedEtaleLowerShriekMapAdjunction :
    D(etaleLowerShriek A j inferInstance) ⊣ D((j)^*[A]) :=
  (etaleLowerShriekUpperStarAdjunction A j inferInstance).mapDerivedCategoryAdjunction

variable (j) in
/-- The derived adjunction `Dj_! ⊣ Lj^*` of the extension by zero along an étale morphism `j`:
the levelwise adjunction transported along `Lj^* ≅ Dj^*`. -/
noncomputable def derivedEtaleLowerShriekAdjunction :
    D(etaleLowerShriek A j inferInstance) ⊣ L((j)^*[A]) :=
  (derivedEtaleLowerShriekMapAdjunction A j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory A j).symm

/-- The derived base change isomorphism `Dg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Dg''^*` induced by the base
change isomorphism of the étale extensions by zero along a cartesian square. -/
noncomputable def mapDerivedCategoryEtaleLowerShriekBaseChangeIso
    (hsq : IsPullback g' j' j g'') :
    D((g')^*[A]) ⋙ D(etaleLowerShriek A j' inferInstance) ≅
      D(etaleLowerShriek A j inferInstance) ⋙ D((g'')^*[A]) :=
  (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ _ (isIso_etaleLowerShriekSquareBaseChangeMap A hsq)) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The derived base change isomorphism for the étale extension by zero is the mate of the
derived square isomorphism of pullbacks, for the adjunctions `Dj_! ⊣ Dj^*` and
`Dj'_! ⊣ Dj'^*`. -/
lemma mapDerivedCategoryEtaleLowerShriekBaseChangeIso_mate (hsq : IsPullback g' j' j g'')
    (K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    (derivedEtaleLowerShriekMapAdjunction A j').unit.app (D((g')^*[A]).obj K) ≫
        D((j')^*[A]).map
          ((mapDerivedCategoryEtaleLowerShriekBaseChangeIso A hsq).hom.app K) =
      D((g')^*[A]).map ((derivedEtaleLowerShriekMapAdjunction A j).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso (etaleSquareUpperStarIso A hsq.toCommSq)).hom.app
          (D(etaleLowerShriek A j inferInstance).obj K) :=
  Adjunction.mapDerivedCategoryAdjunction_mate
    (etaleLowerShriekUpperStarAdjunction A j inferInstance)
    (etaleLowerShriekUpperStarAdjunction A j' inferInstance)
    (etaleSquareUpperStarIso A hsq.toCommSq)
    (@asIso _ _ _ _ _ (isIso_etaleLowerShriekSquareBaseChangeMap A hsq))
    (unit_map_etaleLowerShriekSquareBaseChangeMap_app A hsq.toCommSq) K

/-- **Derived base change for the étale extension by zero**: for a cartesian square
`g' ≫ j = j' ≫ g''` with `j` and `j'` étale, the isomorphism `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*`
on unbounded derived categories, induced by the base change isomorphism
`AlgebraicGeometry.Etale.etaleLowerShriekSquareBaseChangeMap`. -/
noncomputable def derivedEtaleLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'') :
    L((g')^*[A]) ⋙ D(etaleLowerShriek A j' inferInstance) ≅
      D(etaleLowerShriek A j inferInstance) ⋙ L((g'')^*[A]) :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g') _ ≪≫
    mapDerivedCategoryEtaleLowerShriekBaseChangeIso A hsq ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A g'').symm

/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` of a commutative square
`g' ≫ j = j' ≫ g''`: the isomorphism induced on derived categories by the square isomorphism of
pullbacks, read through `Lg^* ≅ Dg^*`. -/
noncomputable def derivedEtaleSquareMap (sq : CommSq g' j' j g'') :
    D((j)^*[A]) ⋙ L((g')^*[A]) ⟶ L((g'')^*[A]) ⋙ D((j')^*[A]) :=
  Functor.whiskerLeft D((j)^*[A]) (leftDerivedUpperStarIsoMapDerivedCategory A g').hom ≫
    (Functor.mapDerivedCategorySquareIso (etaleSquareUpperStarIso A sq)).hom ≫
    Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g'').inv D((j')^*[A])

omit [HasSmallSiteSheafify A] in
/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` is the inverse of the square isomorphism
`Lg''^* ⋙ Lj'^* ≅ Lj^* ⋙ Lg'^*` of the derived pullbacks, read through `Lj^* ≅ Dj^*` and
`Lj'^* ≅ Dj'^*`. -/
lemma derivedEtaleSquareMap_app (sq : CommSq g' j' j g'')
    (Y : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (derivedEtaleSquareMap A sq).app Y =
      L((g')^*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y) ≫
        (derivedSquareUpperStarIso A sq).inv.app Y ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j').hom.app (L((g'')^*[A]).obj Y) := by
  have hnat := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y)
  simp only [derivedEtaleSquareMap, derivedSquareUpperStarIso, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory] at hnat
  rw [reassoc_of% hnat, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The derived base change isomorphism for the étale extension by zero is the mate of the
square map `derivedEtaleSquareMap`, for the adjunctions `Dj_! ⊣ Dj^*` and `Dj'_! ⊣ Dj'^*`. -/
lemma unit_map_derivedEtaleLowerShriekBaseChangeIso_map (hsq : IsPullback g' j' j g'')
    (K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    (derivedEtaleLowerShriekMapAdjunction A j').unit.app (L((g')^*[A]).obj K) ≫
        D((j')^*[A]).map ((derivedEtaleLowerShriekBaseChangeIso A hsq).hom.app K) =
      L((g')^*[A]).map ((derivedEtaleLowerShriekMapAdjunction A j).unit.app K) ≫
        (derivedEtaleSquareMap A hsq.toCommSq).app
          (D(etaleLowerShriek A j inferInstance).obj K) := by
  have h₁ := (derivedEtaleLowerShriekMapAdjunction A j').unit.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app K)
  have h₂ := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((derivedEtaleLowerShriekMapAdjunction A j).unit.app K)
  dsimp at h₁ h₂
  simp only [derivedEtaleLowerShriekBaseChangeIso, derivedEtaleSquareMap,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Functor.map_comp]
  rw [← reassoc_of% h₁, reassoc_of% (mapDerivedCategoryEtaleLowerShriekBaseChangeIso_mate
    A hsq K), reassoc_of% h₂]
  rfl

/-- **The derived base change isomorphism for the étale extension by zero is the mate of the
square isomorphism of the derived pullbacks**: under `Dj'_! ⊣ Lj'^*`, the transpose of
`Dj'_! Lg'^* K ≅ Lg''^* Dj_! K` is `Lg'^*` of the unit of `Dj_! ⊣ Lj^*` followed by the square
isomorphism `Lg'^* Lj^* ≅ Lj'^* Lg''^*`. -/
lemma unit_map_derivedEtaleLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'')
    (K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    (derivedEtaleLowerShriekAdjunction A j').unit.app (L((g')^*[A]).obj K) ≫
        L((j')^*[A]).map ((derivedEtaleLowerShriekBaseChangeIso A hsq).hom.app K) =
      L((g')^*[A]).map ((derivedEtaleLowerShriekAdjunction A j).unit.app K) ≫
        (derivedSquareUpperStarIso A hsq.toCommSq).inv.app
          (D(etaleLowerShriek A j inferInstance).obj K) := by
  have h := unit_map_derivedEtaleLowerShriekBaseChangeIso_map A hsq K
  rw [derivedEtaleSquareMap_app] at h
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory A j').inv.naturality
    ((derivedEtaleLowerShriekBaseChangeIso A hsq).hom.app K)
  simp only [derivedEtaleLowerShriekAdjunction, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc, Functor.map_comp]
  dsimp at hn ⊢
  rw [← hn, reassoc_of% h]
  simp

end Derived

end Etale

end AlgebraicGeometry
