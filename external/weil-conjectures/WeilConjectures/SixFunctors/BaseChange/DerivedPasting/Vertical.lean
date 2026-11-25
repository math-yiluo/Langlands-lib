/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Pasting
public import WeilConjectures.SixFunctors.BaseChange.Derived

/-!
# Vertical pasting law for the derived base change map

For two squares pasted vertically, the derived base change map
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` of the pasted square is the composite of the
derived base change maps of the two squares, modulo the composition isomorphisms of the derived
pushforwards (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_vert`). As a consequence
the proper base change property is stable under composition
(`AlgebraicGeometry.Etale.IsBaseChangeIso.comp`).
(blueprint: `lemma-identity-pasting`, vertical pasting;
`lemma:weil-pbc-composition`, formal part)

The pasting laws are collected in `WeilConjectures.SixFunctors.BaseChange.DerivedPasting`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.NatTrans

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]

/-- `NatTrans.mapHomotopyCategoryPlus` is compatible with right whiskering, definitionally. -/
lemma mapHomotopyCategoryPlus_whiskerRight_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (H : D ⥤ E) [H.Additive] (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight α H)).app K =
      H.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus α).app K) :=
  rfl

/-- `NatTrans.mapHomotopyCategoryPlus` is compatible with left whiskering, definitionally. -/
lemma mapHomotopyCategoryPlus_whiskerLeft_app (F : C ⥤ D) [F.Additive] {G H : D ⥤ E}
    [G.Additive] [H.Additive] (α : G ⟶ H) (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft F α)).app K =
      (NatTrans.mapHomotopyCategoryPlus α).app (F.mapHomotopyCategoryPlus.obj K) :=
  rfl

end CategoryTheory.NatTrans

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

section Instances

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pushforward `f_*` preserves injective objects, being right adjoint to the exact
functor `f^*`. (blueprint: `lemma-composition-cancellation`) -/
instance Etale.preservesInjectiveObjects_lowerStar : ((f)_*[A]).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction A f)

end Instances

section Vertical

variable {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {k : Z' ⟶ Z}

/-- The underived vertical pasting law, without associators. -/
lemma Etale.baseChangeMap_paste_vert' (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' (f' ≫ e') (f ≫ e) k) :
    Etale.baseChangeMap A sq =
      Functor.whiskerRight (Etale.lowerStarComp A f e).inv ((k)^*[A]) ≫
        Functor.whiskerLeft ((f)_*[A]) (Etale.baseChangeMap A sq₂) ≫
        Functor.whiskerRight (Etale.baseChangeMap A sq₁) ((e')_*[A]) ≫
        Functor.whiskerLeft ((g')^*[A]) (Etale.lowerStarComp A f' e').hom := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [Etale.baseChangeMap_paste_vert_app A sq₁ sq₂ sq]
  rfl

/-- **Vertical pasting of the derived base change maps**: for two squares pasted vertically,
the derived base change map of the pasted square is the composite
`k^* R(f ≫ e)_* ≅ k^* Re_* Rf_* ⟶ Re'_* g^* Rf_* ⟶ Re'_* Rf'_* g'^* ≅ R(f' ≫ e')_* g'^*` of
the derived base change maps of the two squares, modulo the composition isomorphisms of the
derived pushforwards along the vertical maps.
(blueprint: `lemma-identity-pasting`,
`lemma-identity-pasting`) -/
lemma Etale.derivedBaseChangeMapPlus_paste_vert (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g e' e k) (sq : CommSq g' (f' ≫ e') (f ≫ e) k) :
    Etale.derivedBaseChangeMapPlus A sq =
      Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIso' (f)_*[A] (e)_*[A]
          (Etale.lowerStarComp A f e)).inv ((k)^*[A]).mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
          (Etale.derivedBaseChangeMapPlus A sq₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A sq₁)
          (e')_*[A].rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((g')^*[A]).mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusCompIso' (f')_*[A] (e')_*[A]
            (Etale.lowerStarComp A f' e')).hom := by
  symm
  refine Etale.derivedBaseChangeMapPlus_ext A sq _ fun K => ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, id_comp]
  -- the unit of `R(f ≫ e)_*` through the composition isomorphism
  have hCI1 : (f ≫ e)_*[A].rightDerivedFunctorPlusUnith.app K ≫
      (Functor.rightDerivedFunctorPlusCompIso' (f)_*[A] (e)_*[A]
        (Etale.lowerStarComp A f e)).inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K) ≫
        (e)_*[A].rightDerivedFunctorPlusUnith.app ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
        (e)_*[A].rightDerivedFunctorPlus.map ((f)_*[A].rightDerivedFunctorPlusUnith.app K) := by
    have h := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac (f)_*[A] (e)_*[A]
      (Etale.lowerStarComp A f e)) K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at h
    have h' : (f ≫ e)_*[A].rightDerivedFunctorPlusUnith.app K =
        DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K) ≫
          (e)_*[A].rightDerivedFunctorPlusUnith.app ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
          (e)_*[A].rightDerivedFunctorPlus.map ((f)_*[A].rightDerivedFunctorPlusUnith.app K) ≫
          (Functor.rightDerivedFunctorPlusCompIso' (f)_*[A] (e)_*[A]
            (Etale.lowerStarComp A f e)).hom.app (DerivedCategory.Plus.Qh.obj K) := by
      rw [h, ← Category.assoc, ← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
        ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
        NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app, DerivedCategory.Plus.Qh.map_id,
        Category.id_comp]
    rw [h']
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  -- naturality of the derived base change map of the lower square along the unit of `Rf_*`
  have hnat₂ := (Etale.derivedBaseChangeMapPlus A sq₂).naturality
    ((f)_*[A].rightDerivedFunctorPlusUnith.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnat₂
  have hfac₂ := Etale.derivedBaseChangeMapPlus_fac_app A sq₂
    ((f)_*[A].mapHomotopyCategoryPlus.obj K)
  have hfac₁ := Etale.derivedBaseChangeMapPlus_fac_app A sq₁ K
  have hnatη : DerivedCategory.Plus.Qh.map (((e')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)) ≫
      (e')_*[A].rightDerivedFunctorPlusUnith.app
        ((f')_*[A].mapHomotopyCategoryPlus.obj (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) =
      (e')_*[A].rightDerivedFunctorPlusUnith.app
        (((g)^*[A]).mapHomotopyCategoryPlus.obj ((f)_*[A].mapHomotopyCategoryPlus.obj K)) ≫
      (e')_*[A].rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)) :=
    (e')_*[A].rightDerivedFunctorPlusUnith.naturality
      ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)
  have hCI2 := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac (f')_*[A]
    (e')_*[A] (Etale.lowerStarComp A f' e')) (((g')^*[A]).mapHomotopyCategoryPlus.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at hCI2
  have hnatCI := (Functor.rightDerivedFunctorPlusCompIso' (f')_*[A] (e')_*[A]
    (Etale.lowerStarComp A f' e')).hom.naturality
    (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatCI
  have hnatF : ((k)^*[A]).mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K)) ≫
      ((k)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        ((e)_*[A].mapHomotopyCategoryPlus.obj ((f)_*[A].mapHomotopyCategoryPlus.obj K)) =
      ((k)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        ((f ≫ e)_*[A].mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map (((k)^*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K)) :=
    ((k)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K)
  have hpaste : (NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app K =
      ((k)^*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f e).inv).app K) ≫
        (NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₂)).app
          ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
        ((e')_*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K) ≫
        (NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarComp A f' e').hom).app
          (((g')^*[A]).mapHomotopyCategoryPlus.obj K) := by
    rw [Etale.baseChangeMap_paste_vert' A sq₁ sq₂ sq, NatTrans.mapHomotopyCategoryPlus_comp,
      NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.mapHomotopyCategoryPlus_comp,
      NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    rfl
  rw [← Functor.map_comp_assoc, hCI1, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, reassoc_of% hnat₂, reassoc_of% hfac₂, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, Category.assoc, hfac₁, Iso.inv_hom_id_app_assoc,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ← reassoc_of% hnatη,
    hnatCI, reassoc_of% hCI2, reassoc_of% hnatF, hpaste, Functor.map_comp,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

/-- If the derived base change maps of two squares pasted vertically are isomorphisms, so is
the derived base change map of the pasted square (whose left vertical map is only required
to be equal to the composite). -/
lemma Etale.isIso_derivedBaseChangeMapPlus_of_paste_vert {f'' : X' ⟶ Z'}
    (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k) (sq : CommSq g' f'' (f ≫ e) k)
    (hf'' : f'' = f' ≫ e') [IsIso (Etale.derivedBaseChangeMapPlus A sq₁)]
    [IsIso (Etale.derivedBaseChangeMapPlus A sq₂)] :
    IsIso (Etale.derivedBaseChangeMapPlus A sq) := by
  subst hf''
  rw [Etale.derivedBaseChangeMapPlus_paste_vert A sq₁ sq₂ sq]
  infer_instance

end Vertical

section Comp

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z)

/-- **The proper base change property is stable under composition**: if `f` and `e` satisfy
`AlgebraicGeometry.Etale.IsBaseChangeIso`, so does `f ≫ e`. Every cartesian square on `f ≫ e`
is the vertical pasting of the cartesian square on `e` with the same base change and the
induced cartesian square on `f`, and the derived base change maps paste accordingly.
(blueprint: `lemma:weil-pbc-composition`, formal part) -/
lemma Etale.IsBaseChangeIso.comp [Etale.IsBaseChangeIso A f] [Etale.IsBaseChangeIso A e] :
    Etale.IsBaseChangeIso A (f ≫ e) where
  isIso {X' Z'} g' f'' k sq := by
    let f' : X' ⟶ pullback e k := pullback.lift (g' ≫ f) f'' (by rw [Category.assoc, sq.w])
    have hf'' : f'' = f' ≫ pullback.snd e k := (pullback.lift_snd _ _ _).symm
    have sq₂ : IsPullback (pullback.fst e k) (pullback.snd e k) e k :=
      IsPullback.of_hasPullback e k
    have sq₁ : IsPullback g' f' f (pullback.fst e k) :=
      IsPullback.of_bot (hf'' ▸ sq) (pullback.lift_fst _ _ _).symm sq₂
    have h₁ := Etale.IsBaseChangeIso.isIso (A := A) g' f' (pullback.fst e k) sq₁
    have h₂ := Etale.IsBaseChangeIso.isIso (A := A) (pullback.fst e k) (pullback.snd e k) k sq₂
    exact Etale.isIso_derivedBaseChangeMapPlus_of_paste_vert A sq₁.toCommSq sq₂.toCommSq
      sq.toCommSq hf''

end Comp

end AlgebraicGeometry
