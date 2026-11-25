/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Pasting laws for the base change map

For two commutative squares of schemes pasted horizontally

```
  X'' --g''--> X' --g'--> X
  |            |          |
  f''          f'         f
  ↓            ↓          ↓
  Y'' --h----> Y' --g---> Y
```

(`sq₁ : CommSq g' f' f g`, `sq₂ : CommSq g'' f'' f' h`, and `sq : CommSq (g'' ≫ g') f'' f (h ≫ g)`
the pasted square) the base change map of the pasted square is the composite of the base change
maps of the two squares, modulo the composition isomorphisms
`AlgebraicGeometry.Etale.upperStarComp` of the pullbacks along the horizontal maps
(`AlgebraicGeometry.Etale.baseChangeMap_paste_horiz`,
`AlgebraicGeometry.Etale.baseChangeMap_paste_horiz_app`). Similarly for two squares pasted
vertically

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
  |          |
  e'         e
  ↓          ↓
  Z' --k---> Z
```

(`sq₁ : CommSq g' f' f g`, `sq₂ : CommSq g e' e k`, `sq : CommSq g' (f' ≫ e') (f ≫ e) k`), modulo
the composition isomorphisms `AlgebraicGeometry.Etale.lowerStarComp` of the pushforwards along
the vertical maps (`AlgebraicGeometry.Etale.baseChangeMap_paste_vert`,
`AlgebraicGeometry.Etale.baseChangeMap_paste_vert_app`).

Both are instances of the compatibility of the mates correspondence with pasting
(`CategoryTheory.mateEquiv_vcomp`, `CategoryTheory.mateEquiv_hcomp`), applied to the
corresponding pasting laws of the square isomorphisms of the pullbacks
(`AlgebraicGeometry.Etale.squareUpperStarIso_paste_horiz_hom`,
`AlgebraicGeometry.Etale.squareUpperStarIso_paste_vert_hom`), which in turn are the
associativity law `AlgebraicGeometry.Etale.upperStarComp_assoc'` of the composition
isomorphisms of the pullbacks. Since the mates correspondence is taken with respect to the
vertical adjunctions `f^* ⊣ f_*`, the vertical pasting law also involves the change of
adjunction `(f ≫ e)^* ⊣ (f ≫ e)_*` versus `f^* ⋙ e^* ⊣ …`, i.e. the conjugation lemma
`AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarComp`.
(blueprint: `lemma-identity-pasting`, underived pasting bullets)

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory

section IsoAux

variable {C : Type*} [Category C]

/-- Rearranging a commutative square with two invertible sides. -/
lemma comp_inv_eq_inv_comp_of_eq {P Q R S : C} (a : P ⟶ Q) (b : P ⟶ R) (x : Q ⟶ S) (y : R ⟶ S)
    [IsIso a] [IsIso y] (h : a ≫ x = b ≫ y) : x ≫ inv y = inv a ≫ b := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, comp_id]

end IsoAux

end CategoryTheory

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

section Coherence

/-- The associativity law for `AlgebraicGeometry.Etale.upperStarComp` in the form of an
equality of natural transformations, with all three composites of the morphisms named: the
counterpart of `AlgebraicGeometry.Etale.lowerStarComp_assoc'`. -/
lemma Etale.upperStarComp_assoc' {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h)
    (hfgh : fgh = fg ≫ h) :
    (Etale.upperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (Etale.upperStarComp A g h gh hgh).hom ((f)^*[A]) =
      (Etale.upperStarComp A fg h fgh hfgh).hom ≫
        Functor.whiskerLeft ((h)^*[A]) (Etale.upperStarComp A f g fg hfg).hom := by
  subst hfg
  subst hgh
  subst hfgh
  have key := congrArg Iso.hom
    (Etale.upperStarComp_assoc A f g h ((f ≫ g) ≫ h) (Category.assoc f g h))
  refine NatTrans.ext (funext fun G => ?_)
  simpa using NatTrans.congr_app key G

/-- The component form of `AlgebraicGeometry.Etale.upperStarComp_assoc'`, rearranged: the
composite `f^* (upperStarComp g h) ≫ (upperStarComp f g)⁻¹` is
`(upperStarComp f gh)⁻¹ ≫ upperStarComp fg h`. -/
@[reassoc]
lemma Etale.map_upperStarComp_hom_app_upperStarComp_inv_app {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (G : Sheaf Z.smallEtaleTopology A) :
    ((f)^*[A]).map ((Etale.upperStarComp A g h gh hgh).hom.app G) ≫
        (Etale.upperStarComp A f g fg hfg).inv.app (((h)^*[A]).obj G) =
      (Etale.upperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app G ≫
        (Etale.upperStarComp A fg h fgh hfgh).hom.app G := by
  have key := NatTrans.congr_app (Etale.upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  simpa using comp_inv_eq_inv_comp_of_eq _ _ _ _ key

/-- The component form of `AlgebraicGeometry.Etale.upperStarComp_assoc'`, rearranged the other
way: the composite `upperStarComp f g ≫ f^* (upperStarComp g h)⁻¹` is
`(upperStarComp fg h)⁻¹ ≫ upperStarComp f gh`. -/
@[reassoc]
lemma Etale.upperStarComp_hom_app_map_upperStarComp_inv_app {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (G : Sheaf Z.smallEtaleTopology A) :
    (Etale.upperStarComp A f g fg hfg).hom.app (((h)^*[A]).obj G) ≫
        ((f)^*[A]).map ((Etale.upperStarComp A g h gh hgh).inv.app G) =
      (Etale.upperStarComp A fg h fgh hfgh).inv.app G ≫
        (Etale.upperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app G := by
  have key := NatTrans.congr_app (Etale.upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  have := comp_inv_eq_inv_comp_of_eq _ _ _ _ key.symm
  rwa [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at this

end Coherence

section Horizontal

variable {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''}
  {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}

open scoped TwoSquare in
/-- Blueprint `definition-underived-base-change-map`: Cartesian square and chosen pullback
identification, compatibility with horizontal pasting.

**Horizontal pasting of the square isomorphisms**: the square isomorphism of two squares
pasted horizontally is the horizontal composite of the two square isomorphisms, modulo the
composition isomorphisms of the pullbacks along the horizontal maps
(blueprint `definition-underived-base-change-map`). -/
lemma Etale.squareUpperStarIso_paste_horiz_hom (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    (Etale.squareUpperStarIso A sq).hom =
      Functor.whiskerRight (Etale.upperStarComp A h g).hom ((f'')^*[A]) ≫
        (TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq₁).hom ≫ₕ
          TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq₂).hom) ≫
        Functor.whiskerLeft ((f)^*[A]) (Etale.upperStarComp A g'' g').inv := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [Etale.squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, TwoSquare.hComp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [Etale.map_upperStarComp_hom_app_upperStarComp_inv_app_assoc A f'' h g (g'' ≫ f')
    (h ≫ g) ((g'' ≫ g') ≫ f) sq₂.w rfl (by rw [Category.assoc, sq₁.w, Category.assoc]),
    Etale.upperStarComp_hom_app_map_upperStarComp_inv_app_assoc A g'' f' g (g'' ≫ f')
    (g' ≫ f) ((g'' ≫ g') ≫ f) rfl sq₁.w (by rw [Category.assoc, sq₁.w, Category.assoc]),
    Etale.map_upperStarComp_hom_app_upperStarComp_inv_app A g'' g' f (g'' ≫ g') (g' ≫ f)
    ((g'' ≫ g') ≫ f) rfl rfl rfl, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

open scoped TwoSquare in
/-- **Horizontal pasting of the base change squares**, in the language of `TwoSquare`: the
base change square of two squares pasted horizontally is the vertical composite (in the sense
of `CategoryTheory.TwoSquare.vComp`: the mates correspondence exchanges the two directions)
of the two base change squares, whiskered by the composition isomorphisms of the pullbacks
along the horizontal maps. -/
lemma Etale.baseChangeSquare_paste_horiz (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    Etale.baseChangeSquare A sq =
      ((Etale.baseChangeSquare A sq₁ ≫ᵥ Etale.baseChangeSquare A sq₂).whiskerRight
        (Etale.upperStarComp A h g).hom).whiskerLeft (Etale.upperStarComp A g'' g').inv := by
  have h1 : TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq).hom =
      ((TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq₁).hom ≫ₕ
        TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq₂).hom).whiskerTop
          (Etale.upperStarComp A h g).hom).whiskerBottom (Etale.upperStarComp A g'' g').inv := by
    refine NatTrans.ext (funext fun F => ?_)
    have := NatTrans.congr_app (Etale.squareUpperStarIso_paste_horiz_hom A sq₁ sq₂ sq) F
    simpa only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using this
  rw [Etale.baseChangeSquare, h1, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp]

/-- **Horizontal pasting of the base change maps**, component form: for two squares pasted
horizontally and a sheaf `F` on `X`, the base change map of the pasted square is the
composite `(h ≫ g)^* f_* F ≅ h^* g^* f_* F ⟶ h^* f'_* g'^* F ⟶ f''_* g''^* g'^* F ≅
f''_* (g'' ≫ g')^* F` of the base change maps of the two squares, modulo the composition
isomorphisms of the pullbacks along the horizontal maps. -/
lemma Etale.baseChangeMap_paste_horiz_app (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) (F : Sheaf X.smallEtaleTopology A) :
    (Etale.baseChangeMap A sq).app F =
      (Etale.upperStarComp A h g).hom.app (((f)_*[A]).obj F) ≫
        ((h)^*[A]).map ((Etale.baseChangeMap A sq₁).app F) ≫
        (Etale.baseChangeMap A sq₂).app (((g')^*[A]).obj F) ≫
        ((f'')_*[A]).map ((Etale.upperStarComp A g'' g').inv.app F) := by
  have := NatTrans.congr_app (Etale.baseChangeSquare_paste_horiz A sq₁ sq₂ sq) F
  simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    Functor.comp_obj, Category.assoc] at this
  simp only [Etale.baseChangeMap]
  exact this

/-- **Horizontal pasting of the base change maps**: for two squares pasted horizontally, the
base change map of the pasted square is the composite of the base change maps of the two
squares, modulo the composition isomorphisms of the pullbacks along the horizontal maps. -/
lemma Etale.baseChangeMap_paste_horiz (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    Etale.baseChangeMap A sq =
      Functor.whiskerLeft ((f)_*[A]) (Etale.upperStarComp A h g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.baseChangeMap A sq₁) ((h)^*[A]) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((g')^*[A]) (Etale.baseChangeMap A sq₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.upperStarComp A g'' g').inv ((f'')_*[A]) := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [Etale.baseChangeMap_paste_horiz_app A sq₁ sq₂ sq]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.comp_obj, id_comp]

end Horizontal

section Vertical

variable {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {k : Z' ⟶ Z}

open scoped TwoSquare in
/-- Blueprint `definition-underived-base-change-map`: Cartesian square and chosen pullback
identification, compatibility with vertical pasting.

**Vertical pasting of the square isomorphisms**: the square isomorphism of two squares
pasted vertically is the vertical composite of the two square isomorphisms, modulo the
composition isomorphisms of the pullbacks along the vertical maps
(blueprint `definition-underived-base-change-map`). -/
lemma Etale.squareUpperStarIso_paste_vert_hom (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' (f' ≫ e') (f ≫ e) k) :
    (Etale.squareUpperStarIso A sq).hom =
      Functor.whiskerLeft ((k)^*[A]) (Etale.upperStarComp A f' e').hom ≫
        (TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq₂).hom ≫ᵥ
          TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq₁).hom) ≫
        Functor.whiskerRight (Etale.upperStarComp A f e).inv ((g')^*[A]) := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [Etale.squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, TwoSquare.vComp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [Etale.upperStarComp_hom_app_map_upperStarComp_inv_app_assoc A f' e' k (f' ≫ e') (g ≫ e)
    (g' ≫ (f ≫ e)) rfl sq₂.w sq.w,
    Etale.map_upperStarComp_hom_app_upperStarComp_inv_app_assoc A f' g e (g' ≫ f) (g ≫ e)
    (g' ≫ (f ≫ e)) sq₁.w rfl (Category.assoc g' f e).symm,
    Etale.upperStarComp_hom_app_map_upperStarComp_inv_app A g' f e (g' ≫ f) (f ≫ e)
    (g' ≫ (f ≫ e)) rfl rfl (Category.assoc g' f e).symm, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app_assoc]

open scoped TwoSquare in
/-- **Vertical pasting of the base change squares**, in the language of `TwoSquare`: the
base change square of two squares pasted vertically is the horizontal composite (in the
sense of `CategoryTheory.TwoSquare.hComp`: the mates correspondence exchanges the two
directions) of the two base change squares, whiskered by the composition isomorphisms of the
pushforwards along the vertical maps. Besides `CategoryTheory.mateEquiv_hcomp`, this uses
that the composition isomorphisms of the pullbacks and of the pushforwards are conjugate
(`AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarComp`). -/
lemma Etale.baseChangeSquare_paste_vert (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' (f' ≫ e') (f ≫ e) k) :
    Etale.baseChangeSquare A sq =
      ((Etale.baseChangeSquare A sq₁ ≫ₕ Etale.baseChangeSquare A sq₂).whiskerBottom
        (Etale.lowerStarComp A f' e').hom).whiskerTop (Etale.lowerStarComp A f e).inv := by
  have h1 : TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq).hom =
      ((TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq₂).hom ≫ᵥ
        TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq₁).hom).whiskerRight
          (Etale.upperStarComp A f' e').hom).whiskerLeft (Etale.upperStarComp A f e).inv := by
    refine NatTrans.ext (funext fun F => ?_)
    have := NatTrans.congr_app (Etale.squareUpperStarIso_paste_vert_hom A sq₁ sq₂ sq) F
    simpa only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using this
  have h2 : conjugateEquiv (Etale.upperStarLowerStarAdjunction A (f ≫ e))
      ((Etale.upperStarLowerStarAdjunction A e).comp (Etale.upperStarLowerStarAdjunction A f))
      (Etale.upperStarComp A f e).inv = (Etale.lowerStarComp A f e).inv :=
    congrArg Iso.inv (Etale.conjugateIsoEquiv_upperStarComp A f e)
  have h3 : conjugateEquiv
      ((Etale.upperStarLowerStarAdjunction A e').comp (Etale.upperStarLowerStarAdjunction A f'))
      (Etale.upperStarLowerStarAdjunction A (f' ≫ e'))
      (Etale.upperStarComp A f' e').hom = (Etale.lowerStarComp A f' e').hom :=
    congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarComp A f' e')
  rw [Etale.baseChangeSquare, h1, conjugateEquiv_mateEquiv_vcomp _
    ((Etale.upperStarLowerStarAdjunction A e).comp (Etale.upperStarLowerStarAdjunction A f)),
    mateEquiv_conjugateEquiv_vcomp _
    ((Etale.upperStarLowerStarAdjunction A e').comp (Etale.upperStarLowerStarAdjunction A f')),
    mateEquiv_hcomp, h2, h3]

/-- **Vertical pasting of the base change maps**, component form: for two squares pasted
vertically and a sheaf `F` on `X`, the base change map of the pasted square is the composite
`k^* (f ≫ e)_* F ≅ k^* e_* f_* F ⟶ e'_* g^* f_* F ⟶ e'_* f'_* g'^* F ≅ (f' ≫ e')_* g'^* F` of
the base change maps of the two squares, modulo the composition isomorphisms of the
pushforwards along the vertical maps. -/
lemma Etale.baseChangeMap_paste_vert_app (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' (f' ≫ e') (f ≫ e) k) (F : Sheaf X.smallEtaleTopology A) :
    (Etale.baseChangeMap A sq).app F =
      ((k)^*[A]).map ((Etale.lowerStarComp A f e).inv.app F) ≫
        (Etale.baseChangeMap A sq₂).app (((f)_*[A]).obj F) ≫
        ((e')_*[A]).map ((Etale.baseChangeMap A sq₁).app F) ≫
        (Etale.lowerStarComp A f' e').hom.app (((g')^*[A]).obj F) := by
  have := NatTrans.congr_app (Etale.baseChangeSquare_paste_vert A sq₁ sq₂ sq) F
  simp only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app, TwoSquare.hComp_app,
    Functor.comp_obj, Category.assoc] at this
  simp only [Etale.baseChangeMap]
  exact this

/-- **Vertical pasting of the base change maps**: for two squares pasted vertically, the
base change map of the pasted square is the composite of the base change maps of the two
squares, modulo the composition isomorphisms of the pushforwards along the vertical maps. -/
lemma Etale.baseChangeMap_paste_vert (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' (f' ≫ e') (f ≫ e) k) :
    Etale.baseChangeMap A sq =
      Functor.whiskerRight (Etale.lowerStarComp A f e).inv ((k)^*[A]) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((f)_*[A]) (Etale.baseChangeMap A sq₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.baseChangeMap A sq₁) ((e')_*[A]) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((g')^*[A]) (Etale.lowerStarComp A f' e').hom := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [Etale.baseChangeMap_paste_vert_app A sq₁ sq₂ sq]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.comp_obj, id_comp]

end Vertical

end AlgebraicGeometry
