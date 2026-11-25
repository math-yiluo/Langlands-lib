/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# The base change map on sections

For a commutative square of schemes `g' ≫ f = f' ≫ g` (notation as in
`WeilConjectures.SixFunctors.BaseChange.Square`) and a sheaf `F` on `X_ét`, a local section of
`g^* f_* F` over an étale `V → Y'` is represented by an étale `W → Y`, a morphism
`φ : V ⟶ W ×_Y Y'` over `Y'` and a section `s` of `F` over `W ×_Y X`: it is the restriction
along `φ` of the image of `s` under the unit `f_* F ⟶ g_* g^* f_* F`. The base change map sends
it to the section of `f'_* g'^* F` over `V`, that is of `g'^* F` over `V ×_{Y'} X'`, obtained
by restricting the image of `s` under the unit `F ⟶ g'_* g'^* F` along the canonical morphism
`V ×_{Y'} X' ⟶ (W ×_Y X) ×_X X'` (`AlgebraicGeometry.Etale.baseChangeMap_app_sectionwise`).
Being a statement about the composite with the restriction maps of the presheaf `g^* f_* F`,
it is automatically independent of the representative.
(blueprint: `prose-04-05`)
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open Etale

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **The base change map on sections.** Let `W → Y` be étale, `V → Y'` étale and
`φ : V ⟶ W ×_Y Y'` a morphism over `Y'`; a section `s` of `F` over `W ×_Y X`, i.e. of `f_* F`
over `W`, together with `φ` represents the section of `g^* f_* F` over `V` obtained by
restricting along `φ` the image of `s` under the unit of `g^* ⊣ g_*`. The base change map
sends it to the restriction, along the canonical morphism `ψ : V ×_{Y'} X' ⟶ (W ×_Y X) ×_X X'`
(characterized by its component to `W`), of the image of `s` under the unit of `g'^* ⊣ g'_*`,
a section of `g'^* F` over `V ×_{Y'} X'`, that is of `f'_* g'^* F` over `V`. The statement is
an equality of morphisms out of `F(W ×_Y X)`, so it holds for all sections at once and does not
depend on the chosen representative.
This is also the content of the pointer remark `prose-04-05`: the
sectionwise rule is independent of the representative and agrees with the adjoint description.
(blueprint: `prose-04-05`)
-/
lemma Etale.baseChangeMap_app_sectionwise (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology A) (W : Y.Etale) (V : Y'.Etale)
    (φ : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W)
    (ψ : (MorphismProperty.Over.pullback @Etale ⊤ f').obj V ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ g').obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
    (hψ : ψ.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ φ.left ≫ pullback.fst _ _) :
    ((Etale.upperStarLowerStarAdjunction A g).unit.app ((f)_*[A].obj F)).hom.app (op W) ≫
        (((g)^*[A]).obj ((f)_*[A].obj F)).obj.map φ.op ≫
        ((Etale.baseChangeMap A sq).app F).hom.app (op V) =
      ((Etale.upperStarLowerStarAdjunction A g').unit.app F).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) ≫
        (((g')^*[A]).obj F).obj.map ψ.op := by
  have h₁ := ((Etale.baseChangeMap A sq).app F).hom.naturality φ.op
  have h₂ := congrArg (fun t ↦ t.hom.app (op W)) (Etale.unit_map_baseChangeMap_app A sq F)
  dsimp at h₁ h₂
  rw [Etale.lowerStar_map_hom_app, Etale.lowerStar_map_hom_app] at h₂
  rw [h₁, reassoc_of% h₂]
  simp only [Etale.squareLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, Etale.lowerStarComp_hom_app_hom_app,
    Etale.lowerStarComp_inv_app_hom_app]
  rw [Etale.lowerStar_obj_val_map, assoc, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
    ← op_comp]
  congr 3
  have hψ' : ψ.left ≫ pullback.snd _ _ = pullback.snd V.hom f' := MorphismProperty.Over.w ψ
  have e₁ : (pullbackLeftPullbackSndIso W.hom f g').inv ≫
      pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W).hom g' ≫
        pullback.fst W.hom f = pullback.fst _ _ :=
    pullbackLeftPullbackSndIso_inv_fst _ _ _
  have e₂ : (pullbackLeftPullbackSndIso W.hom f g').inv ≫
      pullback.snd ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W).hom g' =
        pullback.snd _ _ :=
    pullbackLeftPullbackSndIso_inv_snd_snd _ _ _
  have e₃ : pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W).hom g' ≫
      pullback.snd W.hom f =
        pullback.snd ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W).hom g' ≫ g' :=
    pullback.condition
  ext1
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [assoc, MorphismProperty.Comma.comp_hom, Comma.comp_left,
        MorphismProperty.Over.pullback_map_left, MorphismProperty.Over.pullbackComp_inv_app_left,
        MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id, id_comp, comp_id,
        pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst, hψ, e₁]
      erw [pullback.lift_fst_assoc]
      simp
    · simp only [assoc, MorphismProperty.Comma.comp_hom, Comma.comp_left,
        MorphismProperty.Over.pullback_map_left, MorphismProperty.Over.pullbackComp_inv_app_left,
        MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id, id_comp, comp_id,
        pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.lift_snd_assoc, e₃,
        reassoc_of% hψ', reassoc_of% e₂]
      erw [pullback.lift_snd_assoc]
  · simp only [assoc, MorphismProperty.Comma.comp_hom, Comma.comp_left,
      MorphismProperty.Over.pullback_map_left, MorphismProperty.Over.pullbackComp_inv_app_left,
      MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id, id_comp, comp_id,
      pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd, hψ', e₂]
    erw [pullback.lift_snd]

end AlgebraicGeometry
