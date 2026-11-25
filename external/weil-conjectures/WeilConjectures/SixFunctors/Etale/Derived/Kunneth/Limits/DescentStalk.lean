/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentDiagram
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Germs of the system `q^* q_* F`

Let `q : X ⟶ Y` be a morphism of schemes, `x̄ : Spec Ω ⟶ X` a geometric point and `F` an étale
sheaf on `X`. Under the identification `(q^* G)_x̄ ≅ G_{q x̄}` of
`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`, this file computes on germs:

- the unit of `q^* ⊣ q_*`
  (`AlgebraicGeometry.Etale.toPresheafFiber_upperStarCompSheafFiberIso_inv`);
- the counit `q^* q_* F ⟶ F`: the germ of a section `t ∈ (q_* F)(V) = F(V ×_Y X)` at a point
  `v` of `V` over `q x̄` is sent to the germ of `t` at the point `(v, x̄)` of `V ×_Y X`
  (`AlgebraicGeometry.Etale.toPresheafFiber_comp_sheafFiber_map_counit`);
- the transition maps `AlgebraicGeometry.Etale.descentTransition`
  (`AlgebraicGeometry.Etale.toPresheafFiber_comp_sheafFiber_map_descentTransition`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section Germs

variable {X Y : Scheme.{u}} (q : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (.of Ω) ⟶ X)

omit [IsSepClosed Ω] in
@[simp]
lemma pointSmallEtale_fiber_map_left [IsSepClosed Ω] {U U' : X.Etale} (φ : U ⟶ U')
    (y : (pointSmallEtale x).fiber.obj U) :
    ((pointSmallEtale x).fiber.map φ y).left = y.left ≫ φ.left :=
  rfl

/-- The point `(v, x̄)`
 of `V ×_Y X` attached to a point `v` of `V` over `q x̄` by
`AlgebraicGeometry.Scheme.pointSmallEtaleFiberEtaleIso` is the morphism `pullback.lift v x̄`. -/
lemma pointSmallEtaleFiberEtaleIso_inv_app_left (V : Y.Etale)
    (v : (pointSmallEtale (x ≫ q)).fiber.obj V) :
    ((pointSmallEtaleFiberEtaleIso q x).inv.app V v).left =
      pullback.lift v.left x (CategoryTheory.Over.w v) := by
  apply pullback.hom_ext
  · rw [pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
    exact (pullback.lift_fst _ _ _).symm
  · rw [pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
    exact (pullback.lift_snd _ _ _).symm

/-- **Germs of the unit**, in the form of `AlgebraicGeometry.inverseImage_stalk_germ`: under
`(q^* G)_x̄ ≅ G_{q x̄}`, the germ of the image of a section `a ∈ G(V)` under the unit of
`q^* ⊣ q_*`, a section of `q^* G` over `V ×_Y X`, at the point `(v, x̄)` is the germ of `a` at
`v`. -/
lemma unit_toPresheafFiber_upperStarCompSheafFiberIso_hom (G : Sheaf Y.smallEtaleTopology A)
    (V : Y.Etale) (v : (pointSmallEtale (x ≫ q)).fiber.obj V) :
    ((upperStarLowerStarAdjunction A q).unit.app G).hom.app (op V) ≫
        (pointSmallEtale x).toPresheafFiber (q.Etale.obj V)
          ((pointSmallEtaleFiberEtaleIso q x).inv.app V v) ((q)^*[A].obj G).obj ≫
        ((upperStarCompSheafFiberIso A q x).app G).hom =
      (pointSmallEtale (x ≫ q)).toPresheafFiber V v G.obj := by
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv _).1
  simp only [upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc,
    GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  erw [show (pointSmallEtale x).sheafFiber.map _ =
    (pointSmallEtale x).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ q) A
      (Y.smallGrothendieckTopology (P := @Etale))
      (X.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction A q) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op V)
  erw [← Category.assoc, ← huU]
  rfl

/-- **Germs of the unit.** Under `(q^* G)_x̄ ≅ G_{q x̄}`, the germ of a section `a ∈ G(V)` at
a point `v` of `V` over `q x̄` corresponds to the germ of its image under the unit of
`q^* ⊣ q_*`, a section of `q^* G` over `V ×_Y X`, at the point `(v, x̄)`. -/
lemma toPresheafFiber_upperStarCompSheafFiberIso_inv (G : Sheaf Y.smallEtaleTopology A)
    (V : Y.Etale) (v : (pointSmallEtale (x ≫ q)).fiber.obj V) :
    (pointSmallEtale (x ≫ q)).toPresheafFiber V v G.obj ≫
        ((upperStarCompSheafFiberIso A q x).app G).inv =
      ((upperStarLowerStarAdjunction A q).unit.app G).hom.app (op V) ≫
        (pointSmallEtale x).toPresheafFiber (q.Etale.obj V)
          ((pointSmallEtaleFiberEtaleIso q x).inv.app V v) ((q)^*[A].obj G).obj := by
  rw [← unit_toPresheafFiber_upperStarCompSheafFiberIso_hom, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **Germs of the counit.** Under `(q^* q_* F)_x̄ ≅ (q_* F)_{q x̄}`, the counit
`q^* q_* F ⟶ F` sends the germ of a section `t ∈ (q_* F)(V) = F(V ×_Y X)` at a point `v` of
`V` over `q x̄` to the germ of `t` at the point `(v, x̄)` of `V ×_Y X`. -/
lemma toPresheafFiber_comp_sheafFiber_map_counit (F : Sheaf X.smallEtaleTopology A)
    (V : Y.Etale) (v : (pointSmallEtale (x ≫ q)).fiber.obj V) :
    (pointSmallEtale (x ≫ q)).toPresheafFiber V v ((q)_*[A].obj F).obj ≫
        ((upperStarCompSheafFiberIso A q x).app ((q)_*[A].obj F)).inv ≫
        (pointSmallEtale x).sheafFiber.map ((upperStarLowerStarAdjunction A q).counit.app F) =
      (pointSmallEtale x).toPresheafFiber (q.Etale.obj V)
        ((pointSmallEtaleFiberEtaleIso q x).inv.app V v) F.obj := by
  rw [reassoc_of% toPresheafFiber_upperStarCompSheafFiberIso_inv]
  erw [show (pointSmallEtale x).sheafFiber.map ((upperStarLowerStarAdjunction A q).counit.app F) =
    (pointSmallEtale x).presheafFiber.map ((upperStarLowerStarAdjunction A q).counit.app F).hom
    from rfl, GrothendieckTopology.Point.toPresheafFiber_naturality]
  have h := congrArg (fun φ ↦ φ.hom.app (op V))
    ((upperStarLowerStarAdjunction A q).right_triangle_components F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at h
  erw [← Category.assoc, h, Category.id_comp]
  rfl

/-- **Germs of the transition maps.** Let `r = q ≫ g` and let `t ∈ (r_* F)(V)` be a section over
an étale `Z`-scheme `V`, with a point `v` of `V` over `r x̄`. Under the identifications
`(r^* r_* F)_x̄ ≅ (r_* F)_{r x̄}` and `(q^* q_* F)_x̄ ≅ (q_* F)_{q x̄}`, the transition map
`r^* r_* F ⟶ q^* q_* F` sends the germ of `t` at `v` to the germ at a point `v'` of `V ×_Z Y`
lying over `v` and `q x̄` of the section of `q_* F` over `V ×_Z Y` corresponding to `t`. -/
lemma toPresheafFiber_comp_sheafFiber_map_descentTransition {Z : Scheme.{u}} (g : Y ⟶ Z)
    (r : X ⟶ Z) (hr : r = q ≫ g) (F : Sheaf X.smallEtaleTopology A) (V : Z.Etale)
    (v : (pointSmallEtale (x ≫ r)).fiber.obj V)
    (v' : (pointSmallEtale (x ≫ q)).fiber.obj (g.Etale.obj V))
    (hv' : v'.left ≫ pullback.fst V.hom g = v.left) :
    (pointSmallEtale (x ≫ r)).toPresheafFiber V v ((r)_*[A].obj F).obj ≫
        ((upperStarCompSheafFiberIso A r x).app ((r)_*[A].obj F)).inv ≫
        (pointSmallEtale x).sheafFiber.map (descentTransition A q g r hr F) =
      ((lowerStarComp A q g r hr).inv.app F).hom.app (op V) ≫
        (pointSmallEtale (x ≫ q)).toPresheafFiber (g.Etale.obj V) v' ((q)_*[A].obj F).obj ≫
        ((upperStarCompSheafFiberIso A q x).app ((q)_*[A].obj F)).inv := by
  rw [reassoc_of% toPresheafFiber_upperStarCompSheafFiberIso_inv]
  erw [show (pointSmallEtale x).sheafFiber.map (descentTransition A q g r hr F) =
    (pointSmallEtale x).presheafFiber.map (descentTransition A q g r hr F).hom
    from rfl, GrothendieckTopology.Point.toPresheafFiber_naturality]
  have h := congrArg (fun φ ↦ φ.hom.app (op V))
    (homEquiv_descentTransition A q g r hr F)
  simp only [Adjunction.homEquiv_unit, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at h
  erw [← Category.assoc, h]
  rw [toPresheafFiber_upperStarCompSheafFiberIso_inv]
  simp only [descentTransitionAux, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Category.assoc]
  have hpt : (pointSmallEtale x).fiber.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q g r hr).hom.app V)
      ((pointSmallEtaleFiberEtaleIso r x).inv.app V v) =
      (pointSmallEtaleFiberEtaleIso q x).inv.app (g.Etale.obj V) v' := by
    subst hr
    apply CategoryTheory.Over.OverMorphism.ext
    erw [pointSmallEtale_fiber_map_left]
    have h₁ := MorphismProperty.Over.w
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q g).hom.app V)
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · calc _ = ((pointSmallEtaleFiberEtaleIso (q ≫ g) x).inv.app V v).left ≫
              pullback.fst V.hom (q ≫ g) := by
                simp only [Category.assoc]
                exact congrArg (_ ≫ ·) (MorphismProperty.Over.pullbackComp_left_fst_fst q g V)
          _ = v.left := pointSmallEtaleFiberEtaleIso_inv_app_left_fst _ _ _ _
          _ = _ := by
                rw [← hv', Category.assoc]
                exact congrArg (· ≫ pullback.fst V.hom g)
                  (pointSmallEtaleFiberEtaleIso_inv_app_left_fst q x _ v').symm
      · calc _ = ((pointSmallEtaleFiberEtaleIso (q ≫ g) x).inv.app V v).left ≫
              pullback.snd V.hom (q ≫ g) ≫ q := by
                simp only [Category.assoc]
                refine congrArg (_ ≫ ·) ?_
                refine (congrArg (_ ≫ ·) pullback.condition).trans ?_
                rw [← Category.assoc]
                exact congrArg (· ≫ q) h₁
          _ = x ≫ q := by
                rw [← Category.assoc]
                exact congrArg (· ≫ q) (pointSmallEtaleFiberEtaleIso_inv_app_left_snd _ _ _ _)
          _ = _ := by
                exact ((congrArg (fun t ↦ t ≫ pullback.snd V.hom g)
                  (pointSmallEtaleFiberEtaleIso_inv_app_left_fst q x _ v')).trans
                    (CategoryTheory.Over.w v')).symm
    · calc _ = ((pointSmallEtaleFiberEtaleIso (q ≫ g) x).inv.app V v).left ≫
            pullback.snd V.hom (q ≫ g) := by
              simp only [Category.assoc]
              exact congrArg (_ ≫ ·) h₁
        _ = x := pointSmallEtaleFiberEtaleIso_inv_app_left_snd _ _ _ _
        _ = _ := (pointSmallEtaleFiberEtaleIso_inv_app_left_snd q x _ v').symm
  erw [lowerStarComp_hom_app_hom_app, GrothendieckTopology.Point.toPresheafFiber_w, hpt]
  rfl

end Germs

end AlgebraicGeometry.Etale
