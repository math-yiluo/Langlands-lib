/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.BaseChange.Derived

/-!
# Finite morphisms satisfy proper base change

For a cartesian square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `f` finite, the base change map `g^* f_* ⟶ f'_* g'^*`
(`AlgebraicGeometry.Etale.baseChangeMap`) is an isomorphism
(`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`), hence finite morphisms satisfy
the proper base change property, both at the level of sheaves
(`AlgebraicGeometry.Etale.isBaseChangeIsoSheaf_of_isFinite`) and on the bounded below derived
categories (`AlgebraicGeometry.Etale.isBaseChangeIso_of_isFinite`).

## The proof

Geometric points with algebraically closed residue field jointly reflect isomorphisms, so it
suffices to show that the base change map is an isomorphism on the stalk at such a point
`y'` of `Y'`. Both sides are computed by the geometric stalk formula for finite direct images
(`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`): the stalk of `g^* f_* F` at `y'` is the
stalk of `f_* F` at `y' ≫ g`, the product of the stalks of `F` at the geometric points of
`X` over `y' ≫ g`, and the stalk of `f'_* g'^* F` at `y'` is the product of the stalks of
`g'^* F` at the geometric points `t'` of `X'` over `y'`, each of which is the stalk of `F` at
`t' ≫ g'`. The geometric fibres correspond by
`AlgebraicGeometry.Scheme.Hom.GeometricFiber.baseChangeEquiv`, and the base change map is
the identity on each factor
(`AlgebraicGeometry.Etale.sheafFiber_map_baseChangeMap_app_stalkRestrict`).

The last point is where the mate description of the base change map meets the concrete
description of the stalk of a direct image. The base change map is the mate of the
composition isomorphisms `f_* g'_* ≅ (g' ≫ f)_* ≅ g_* f'_*` of the pushforwards along the
horizontal adjunctions (`AlgebraicGeometry.Etale.baseChangeSquare_eq_mateEquiv_symm`), the
counits of which restrict to the projections `AlgebraicGeometry.Etale.stalkRestrict` of the
stalk formula (`AlgebraicGeometry.Etale.stalkRestrict_eq_counit`), and the composition
isomorphisms of the pushforwards are compatible with these projections
(`AlgebraicGeometry.Etale.sheafFiber_map_lowerStarComp_hom_app_stalkRestrict`): the
restriction of germs along `h₁ ≫ h₂` is the restriction along `h₂` followed by the restriction
along `h₁`.

The passage to the derived category is
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIso_baseChangeMap`: the
pushforwards along `f` and `f'` are exact, so no resolutions are involved.
(blueprint: `lemma:weil-pbc-finite-exchange`, `prop:weil-pbc-finite-morphism`)

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

open Scheme Etale Scheme.Hom

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section StalkRestrictComp

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

omit [HasSmallSiteSheafify A] in
/-- **The restriction of germs is compatible with composition**: for a composite
`h₁₂ = h₁ ≫ h₂` and a geometric point `t` of `T` over the geometric point `y` of `R`,
restricting germs of `(h₁ ≫ h₂)_* G` at `y` to germs of `G` at `t` is, through the
composition isomorphism `AlgebraicGeometry.Etale.lowerStarComp` of the pushforwards, the
restriction of germs of `h₂_* (h₁_* G)` at `y` to germs of `h₁_* G` at `t ≫ h₁` followed by
the restriction of these to germs of `G` at `t`. -/
lemma Etale.sheafFiber_map_lowerStarComp_hom_app_stalkRestrict (h₁₂ : T ⟶ R)
    (hh : h₁₂ = h₁ ≫ h₂) (y : Spec (.of Ω) ⟶ R) (t : GeometricFiber h₁₂ y)
    (G : Sheaf T.smallEtaleTopology A) :
    (pointSmallEtale y).sheafFiber.map ((Etale.lowerStarComp A h₁ h₂ h₁₂ hh).hom.app G) ≫
        Etale.stalkRestrict A h₁₂ y t G =
      Etale.stalkRestrict A h₂ y ⟨t.1 ≫ h₁, by rw [Category.assoc, ← hh, t.2]⟩
          ((h₁)_*[A].obj G) ≫
        Etale.stalkRestrict A h₁ (t.1 ≫ h₁) ⟨t.1, rfl⟩ G := by
  subst hh
  apply (pointSmallEtale y).presheafFiber_hom_ext
  intro V v
  change (pointSmallEtale y).toPresheafFiber V v _ ≫
      (pointSmallEtale y).presheafFiber.map ((Etale.lowerStarComp A h₁ h₂).hom.app G).hom ≫
        Etale.stalkRestrict A (h₁ ≫ h₂) y t G =
    (pointSmallEtale y).toPresheafFiber V v _ ≫
      Etale.stalkRestrict A h₂ y ⟨t.1 ≫ h₁, _⟩ ((h₁)_*[A].obj G) ≫
        Etale.stalkRestrict A h₁ (t.1 ≫ h₁) ⟨t.1, rfl⟩ G
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc,
    Etale.toPresheafFiber_stalkRestrict A (h₁ ≫ h₂) y t G (Functor.elementsMk _ V v),
    Etale.toPresheafFiber_stalkRestrict_assoc A h₂ y _ _ (Functor.elementsMk _ V v),
    Etale.toPresheafFiber_stalkRestrict A h₁ _ _ G (Functor.elementsMk _ (h₂.Etale.obj V) _)]
  -- the component of the composition isomorphism is restriction along the pasting
  -- isomorphism `(V ×_R S) ×_S T ≅ V ×_R T`
  set ψ := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h₁ h₂).hom.app V with hψ
  have hcomp : ((Etale.lowerStarComp A h₁ h₂).hom.app G).hom.app (op V) = G.obj.map ψ.op := by
    simp only [Etale.lowerStarComp,
      Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv, hψ]
  rw [hcomp]
  erw [GrothendieckTopology.Point.toPresheafFiber_w]
  congr 1
  -- the pasting isomorphism carries the point `(v, t)` to the point `((v, t ≫ h₁), t)`
  refine CategoryTheory.Over.OverMorphism.ext ?_
  have hmap : (pointSmallEtale t.1).fiber.map ψ
      ((Etale.baseChangeNbhd (h₁ ≫ h₂) y t).obj (Functor.elementsMk _ V v)).val =
      ((Etale.baseChangeNbhd (h₁ ≫ h₂) y t).obj (Functor.elementsMk _ V v)).val ≫
        (Etale.forget T).map ψ := rfl
  have hl : ((Etale.forget T).map ψ).left = ψ.left := rfl
  have hψ₁ : ψ.left ≫ pullback.fst ((MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      h₂).obj V).hom h₁ ≫ pullback.fst V.hom h₂ = pullback.fst V.hom (h₁ ≫ h₂) :=
    MorphismProperty.Over.pullbackComp_left_fst_fst h₁ h₂ V
  have hψ₂ : ψ.left ≫ pullback.fst ((MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      h₂).obj V).hom h₁ ≫ pullback.snd V.hom h₂ = pullback.snd V.hom (h₁ ≫ h₂) ≫ h₁ := by
    rw [hψ, MorphismProperty.Over.pullbackComp_hom_app_left]
    erw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, pullback.lift_snd_assoc,
      Category.comp_id]
  have hψ₃ : ψ.left ≫ pullback.snd ((MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      h₂).obj V).hom h₁ = pullback.snd V.hom (h₁ ≫ h₂) := by
    rw [hψ, MorphismProperty.Over.pullbackComp_hom_app_left]
    erw [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, pullback.lift_snd,
      Category.comp_id]
  have ht : (t.1 ≫ h₁) ≫ h₂ = y := by rw [Category.assoc, t.2]
  set c' : Nbhd (t.1 ≫ h₁) :=
    Functor.elementsMk _ (h₂.Etale.obj V)
      (CategoryTheory.Over.homMk (basePt h₂ (Functor.elementsMk _ V v) ⟨t.1 ≫ h₁, ht⟩)
        (basePt_snd h₂ (Functor.elementsMk _ V v) ⟨t.1 ≫ h₁, ht⟩)) with hc'
  have hb₁ : basePt h₁ c' ⟨t.1, rfl⟩ ≫ pullback.fst ((MorphismProperty.Over.pullback
      (P := @Etale) (Q := ⊤) h₂).obj V).hom h₁ =
      basePt h₂ (Functor.elementsMk _ V v) ⟨t.1 ≫ h₁, ht⟩ :=
    basePt_fst h₁ c' ⟨t.1, rfl⟩
  have hb₂ : basePt h₁ c' ⟨t.1, rfl⟩ ≫ pullback.snd ((MorphismProperty.Over.pullback
      (P := @Etale) (Q := ⊤) h₂).obj V).hom h₁ = t.1 :=
    basePt_snd h₁ c' ⟨t.1, rfl⟩
  rw [hmap, CategoryTheory.Over.comp_left, hl]
  simp only [Etale.baseChangeNbhd_obj_val_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hψ₁, basePt_fst, hb₁, basePt_fst]
    · rw [Category.assoc, Category.assoc, hψ₂, basePt_snd_assoc, hb₁, basePt_snd]
  · rw [Category.assoc, hψ₃, basePt_snd, hb₂]

end StalkRestrictComp

section BaseChangeApp

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **The pushforward form of the base change map, componentwise**: it is `g^* f_*` of the
unit of `g'^* ⊣ g'_*`, followed by `g^*` of the composition isomorphisms
`f_* g'_* ≅ (g' ≫ f)_* ≅ g_* f'_*` of the pushforwards, followed by the counit of `g^* ⊣ g_*`. -/
lemma Etale.baseChangeMap_app_eq (sq : CommSq g' f' f g) (F : Sheaf X.smallEtaleTopology A) :
    (Etale.baseChangeMap A sq).app F =
      ((g)^*[A]).map ((f)_*[A].map ((Etale.upperStarLowerStarAdjunction A g').unit.app F)) ≫
        ((g)^*[A]).map ((Etale.lowerStarComp A g' f).hom.app (((g')^*[A]).obj F)) ≫
        ((g)^*[A]).map
          ((Etale.lowerStarComp A f' g (g' ≫ f) sq.w).inv.app (((g')^*[A]).obj F)) ≫
        (Etale.upperStarLowerStarAdjunction A g).counit.app
          ((f')_*[A].obj (((g')^*[A]).obj F)) := by
  have h := congrArg (fun (w : TwoSquare (f)_*[A] (g')^*[A] (g)^*[A] (f')_*[A]) ↦
    w.app F) (Etale.baseChangeSquare_eq_mateEquiv_symm A sq)
  simp only [mateEquiv_symm_apply, Etale.squareLowerStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc,
    CategoryTheory.Functor.map_id] at h
  exact h

end BaseChangeApp

section Stalk

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- **The base change map is the identity on the factors of the stalk formula**: for a
geometric point `s` of `X'`, the stalk at `s ≫ f'` of the base change map
`g^* f_* F ⟶ f'_* g'^* F` followed by the restriction of germs to `s` is, through the
identifications `(g^* f_* F)_{s ≫ f'} ≅ (f_* F)_{s ≫ f' ≫ g}` and `(g'^* F)_s ≅ F_{s ≫ g'}`,
the restriction of germs of `f_* F` to `s ≫ g'`. -/
lemma Etale.sheafFiber_map_baseChangeMap_app_stalkRestrict (sq : CommSq g' f' f g)
    (s : Spec (.of Ω) ⟶ X') (F : Sheaf X.smallEtaleTopology A) :
    (pointSmallEtale (s ≫ f')).sheafFiber.map ((Etale.baseChangeMap A sq).app F) ≫
        Etale.stalkRestrict A f' (s ≫ f') ⟨s, rfl⟩ (((g')^*[A]).obj F) ≫
        (Etale.upperStarCompSheafFiberIso A g' s).hom.app F =
      (Etale.upperStarCompSheafFiberIso A g (s ≫ f')).hom.app ((f)_*[A].obj F) ≫
        Etale.stalkRestrict A f ((s ≫ f') ≫ g)
          ⟨s ≫ g', by rw [Category.assoc, sq.w, Category.assoc]⟩ F := by
  have ht : s ≫ (g' ≫ f) = (s ≫ f') ≫ g := by rw [sq.w, Category.assoc]
  -- the counit of `g^* ⊣ g_*` on stalks is the restriction of germs along `g`
  have hε (G : Sheaf Y'.smallEtaleTopology A) :
      (pointSmallEtale (s ≫ f')).sheafFiber.map
          ((Etale.upperStarLowerStarAdjunction A g).counit.app G) =
        (Etale.upperStarCompSheafFiberIso A g (s ≫ f')).hom.app ((g)_*[A].obj G) ≫
          Etale.stalkRestrict A g ((s ≫ f') ≫ g) ⟨s ≫ f', rfl⟩ G := by
    rw [Etale.stalkRestrict_eq_counit, Iso.hom_inv_id_app_assoc]
  -- the stalk isomorphism for `g^*` is natural
  have hnat {G G' : Sheaf Y.smallEtaleTopology A} (φ : G ⟶ G') :
      (pointSmallEtale (s ≫ f')).sheafFiber.map (((g)^*[A]).map φ) ≫
          (Etale.upperStarCompSheafFiberIso A g (s ≫ f')).hom.app G' =
        (Etale.upperStarCompSheafFiberIso A g (s ≫ f')).hom.app G ≫
          (pointSmallEtale ((s ≫ f') ≫ g)).sheafFiber.map φ :=
    (Etale.upperStarCompSheafFiberIso A g (s ≫ f')).hom.naturality φ
  -- the composition laws for the restriction of germs
  have hL₁ := Etale.sheafFiber_map_lowerStarComp_hom_app_stalkRestrict A f' g (g' ≫ f) sq.w
    ((s ≫ f') ≫ g) ⟨s, ht⟩ (((g')^*[A]).obj F)
  have hL₂ := Etale.sheafFiber_map_lowerStarComp_hom_app_stalkRestrict A g' f (g' ≫ f) rfl
    ((s ≫ f') ≫ g) ⟨s, ht⟩ (((g')^*[A]).obj F)
  -- the unit of `g'^* ⊣ g'_*` on stalks is inverse to the restriction of germs along `g'`
  have hnat' {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G') :
      (pointSmallEtale (s ≫ g')).sheafFiber.map φ ≫
          (Etale.upperStarCompSheafFiberIso A g' s).inv.app G' =
        (Etale.upperStarCompSheafFiberIso A g' s).inv.app G ≫
          (pointSmallEtale s).sheafFiber.map (((g')^*[A]).map φ) :=
    (Etale.upperStarCompSheafFiberIso A g' s).inv.naturality φ
  have hη : (pointSmallEtale (s ≫ g')).sheafFiber.map
        ((Etale.upperStarLowerStarAdjunction A g').unit.app F) ≫
      Etale.stalkRestrict A g' (s ≫ g') ⟨s, rfl⟩ (((g')^*[A]).obj F) ≫
      (Etale.upperStarCompSheafFiberIso A g' s).hom.app F = 𝟙 _ := by
    have h := hnat' ((Etale.upperStarLowerStarAdjunction A g').unit.app F)
    rw [Etale.stalkRestrict_eq_counit]
    simp only [Category.assoc]
    rw [reassoc_of% h, ← Functor.map_comp_assoc, Adjunction.left_triangle_components,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
    rfl
  have hnat₁ := hnat ((f)_*[A].map ((Etale.upperStarLowerStarAdjunction A g').unit.app F))
  have hnat₂ := hnat ((Etale.lowerStarComp A g' f).hom.app (((g')^*[A]).obj F))
  have hnat₃ := hnat ((Etale.lowerStarComp A f' g (g' ≫ f) sq.w).inv.app (((g')^*[A]).obj F))
  rw [Etale.baseChangeMap_app_eq, Functor.map_comp, Functor.map_comp, Functor.map_comp, hε]
  simp only [Category.assoc]
  rw [reassoc_of% hnat₃, reassoc_of% hnat₂, reassoc_of% hnat₁, ← reassoc_of% hL₁,
    ← (pointSmallEtale ((s ≫ f') ≫ g)).sheafFiber.map_comp_assoc
      ((Etale.lowerStarComp A f' g (g' ≫ f) sq.w).inv.app _)
      ((Etale.lowerStarComp A f' g (g' ≫ f) sq.w).hom.app _),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hL₂,
    ← Etale.stalkRestrict_naturality_assoc, hη]
  exact congrArg (fun φ ↦ (Etale.upperStarCompSheafFiberIso A g (s ≫ f')).hom.app
    ((f)_*[A].obj F) ≫ φ) (Category.comp_id _)

end Stalk

section IsIso

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g) [IsFinite f]

include sq in
/-- The base change of a finite morphism is finite. -/
lemma isFinite_of_isPullback : IsFinite f' :=
  MorphismProperty.of_isPullback (P := @IsFinite) sq inferInstance

/-- **The base change map of a finite morphism is an isomorphism on stalks** at geometric
points with algebraically closed residue field: through the stalk formula, it is the
reindexing of the finite product of stalks of `F` along the bijection
`AlgebraicGeometry.Scheme.Hom.GeometricFiber.baseChangeEquiv` of the geometric fibres. -/
lemma Etale.isIso_sheafFiber_map_baseChangeMap_app {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y' : Spec (.of Ω) ⟶ Y') (F : Sheaf X.smallEtaleTopology A) :
    IsIso ((pointSmallEtale y').sheafFiber.map ((Etale.baseChangeMap A sq.toCommSq).app F)) := by
  have : IsFinite f' := isFinite_of_isPullback sq
  -- the two product decompositions of the stalks
  let P : (pointSmallEtale y').sheafFiber.obj ((f')_*[A].obj (((g')^*[A]).obj F)) ⟶
      ∏ᶜ fun t' : GeometricFiber f' y' ↦ (pointSmallEtale (t'.1 ≫ g')).sheafFiber.obj F :=
    Pi.lift fun t' ↦ Etale.stalkRestrict A f' y' t' (((g')^*[A]).obj F) ≫
      (Etale.upperStarCompSheafFiberIso A g' t'.1).hom.app F
  let Q : (pointSmallEtale (y' ≫ g)).sheafFiber.obj ((f)_*[A].obj F) ⟶
      ∏ᶜ fun t' : GeometricFiber f' y' ↦ (pointSmallEtale (t'.1 ≫ g')).sheafFiber.obj F :=
    Pi.lift fun t' ↦ Etale.stalkRestrict A f (y' ≫ g) (GeometricFiber.baseChangeEquiv sq y' t') F
  -- the base change map is the identity on the factors
  have key : (pointSmallEtale y').sheafFiber.map ((Etale.baseChangeMap A sq.toCommSq).app F) ≫
      P = (Etale.upperStarCompSheafFiberIso A g y').hom.app ((f)_*[A].obj F) ≫ Q := by
    apply Pi.hom_ext
    rintro ⟨s, rfl⟩
    simp only [P, Q, Category.assoc, Pi.lift_comp_π]
    exact Etale.sheafFiber_map_baseChangeMap_app_stalkRestrict A sq.toCommSq s F
  -- both product decompositions are isomorphisms
  have hP : IsIso P := by
    have : P = Pi.lift (fun t' ↦ Etale.stalkRestrict A f' y' t' (((g')^*[A]).obj F)) ≫
        Limits.Pi.map (fun t' : GeometricFiber f' y' ↦
          (Etale.upperStarCompSheafFiberIso A g' t'.1).hom.app F) := by
      apply Pi.hom_ext
      intro t'
      simp [P]
    rw [this]
    infer_instance
  have hQ : IsIso Q := by
    have : Q = Pi.lift (fun t ↦ Etale.stalkRestrict A f (y' ≫ g) t F) ≫
        (Pi.reindex (GeometricFiber.baseChangeEquiv sq y')
          (fun t : GeometricFiber f (y' ≫ g) ↦ (pointSmallEtale t.1).sheafFiber.obj F)).inv := by
      apply Pi.hom_ext
      intro t'
      simp only [Q, Pi.lift_comp_π, Category.assoc]
      erw [Pi.reindex_inv_π, Pi.lift_comp_π]
    rw [this]
    infer_instance
  have : (pointSmallEtale y').sheafFiber.map ((Etale.baseChangeMap A sq.toCommSq).app F) =
      (Etale.upperStarCompSheafFiberIso A g y').hom.app ((f)_*[A].obj F) ≫ Q ≫ inv P := by
    rw [← Category.assoc, ← key, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [this]
  infer_instance

end IsIso

section Main

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [IsFinite f]

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

/-- **The finite exchange isomorphism**: for a cartesian square with `f` finite, the base
change map `g^* f_* ⟶ f'_* g'^*` is an isomorphism. The geometric points of `Y'` with
algebraically closed residue field jointly reflect isomorphisms, and the base change map is
an isomorphism on each of these stalks by
`AlgebraicGeometry.Etale.isIso_sheafFiber_map_baseChangeMap_app`.
(blueprint: `lemma:weil-pbc-finite-exchange`, `lemma-finite-morphisms`) -/
lemma Etale.isIso_baseChangeMap_of_isFinite
    [hJ : Y'.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (sq : IsPullback g' f' f g) : IsIso (Etale.baseChangeMap A sq.toCommSq) := by
  have : ∀ F : Sheaf X.smallEtaleTopology A, IsIso ((Etale.baseChangeMap A sq.toCommSq).app F) := by
    intro F
    refine isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
    have : IsIso (((pointSmallEtale (Y'.algClosurePoint s)).ulift.{u + 1}).sheafFiber.map
        ((Etale.baseChangeMap A sq.toCommSq).app F)) := by
      rw [← NatIso.naturality_2 ((pointSmallEtale (Y'.algClosurePoint s)).uliftSheafFiberIso A)
        ((Etale.baseChangeMap A sq.toCommSq).app F)]
      have := Etale.isIso_sheafFiber_map_baseChangeMap_app A sq (Y'.algClosurePoint s) F
      infer_instance
    exact this
  exact NatIso.isIso_of_isIso_app _

variable [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- **Finite morphisms satisfy the sheaf-level base change property.** -/
instance Etale.isBaseChangeIsoSheaf_of_isFinite : Etale.IsBaseChangeIsoSheaf A f where
  isIso _ _ _ sq := Etale.isIso_baseChangeMap_of_isFinite A sq

/-- **Finite morphisms satisfy proper base change**: for every cartesian square on a finite
morphism `f`, the derived base change map `g^* Rf_* ⟶ Rf'_* g'^*` on `D⁺` is an isomorphism.
The pushforwards along `f` and its base change `f'` are exact, so this follows from the
sheaf-level statement without any resolutions.
(blueprint: `prop:weil-pbc-finite-morphism`, `lemma-finite-morphisms`, derived part) -/
instance Etale.isBaseChangeIso_of_isFinite : Etale.IsBaseChangeIso A f where
  isIso _ _ _ sq := by
    have : IsFinite _ := isFinite_of_isPullback sq
    have := Etale.isIso_baseChangeMap_of_isFinite A sq
    exact Etale.isIso_derivedBaseChangeMapPlus_of_isIso_baseChangeMap A sq.toCommSq

end Main

end AlgebraicGeometry

end
