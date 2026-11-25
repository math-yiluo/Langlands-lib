/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# The base change map on pulled back sections

For a commutative square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

and an abelian étale sheaf `F` on `X`, the base change map `g^* f_* F ⟶ f'_* g'^* F` sends the
pullback `φ^* s` of a section `s` of `f_* F` over an étale `W ⟶ Y` along `φ : V ⟶ W` (over
`g`) to the pullback of `s`, as a section of `F` over `W ×_Y X`, along the induced morphism
`V ×_{Y'} X' ⟶ W ×_Y X` (`AlgebraicGeometry.Etale.baseChangeMap_app_pullSection`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : CommSq g' f' f g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

include sq in
/-- The morphism `V ×_{Y'} X' ⟶ W ×_Y X` induced by a morphism `φ : V ⟶ W` over `g`. -/
noncomputable def baseChangeSectionMap {W : Y.Etale} {V : Y'.Etale} (φ : V.left ⟶ W.left)
    (hφ : φ ≫ W.hom = V.hom ≫ g) : pullback V.hom f' ⟶ pullback W.hom f :=
  pullback.lift (pullback.fst V.hom f' ≫ φ) (pullback.snd V.hom f' ≫ g') (by
    rw [Category.assoc, hφ, pullback.condition_assoc, ← sq.w, Category.assoc])

@[reassoc (attr := simp)]
lemma baseChangeSectionMap_fst {W : Y.Etale} {V : Y'.Etale} (φ : V.left ⟶ W.left)
    (hφ : φ ≫ W.hom = V.hom ≫ g) :
    baseChangeSectionMap sq φ hφ ≫ pullback.fst W.hom f = pullback.fst V.hom f' ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeSectionMap_snd {W : Y.Etale} {V : Y'.Etale} (φ : V.left ⟶ W.left)
    (hφ : φ ≫ W.hom = V.hom ≫ g) :
    baseChangeSectionMap sq φ hφ ≫ pullback.snd W.hom f = pullback.snd V.hom f' ≫ g' :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The base change map on pulled back sections.** The base change map sends the pullback
`φ^* s` of a section `s` of `f_* F` over `W` to the pullback of `s` along
`V ×_{Y'} X' ⟶ W ×_Y X`. -/
lemma baseChangeMap_app_pullSection {W : Y.Etale} {V : Y'.Etale} (φ : V.left ⟶ W.left)
    (hφ : φ ≫ W.hom = V.hom ≫ g) (s : F.obj.obj (op (f.Etale.obj W))) :
    ((Etale.baseChangeMap AddCommGrpCat.{u + 1} sq).app F).hom.app (op V)
        (pullSection g ((f)_*[AddCommGrpCat.{u + 1}].obj F) φ hφ s) =
      pullSection g' F (V := f'.Etale.obj V) (U := f.Etale.obj W) (baseChangeSectionMap sq φ hφ)
        (baseChangeSectionMap_snd sq φ hφ) s := by
  rw [pullSection]
  erw [NatTrans.naturality_apply ((Etale.baseChangeMap AddCommGrpCat.{u + 1} sq).app F).hom
    (homToPullback g φ hφ).op]
  have h := congrArg (fun α ↦ α.hom.app (op W) s)
    (Etale.unit_map_baseChangeMap_app AddCommGrpCat.{u + 1} sq F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at h
  erw [h]
  simp only [Etale.squareLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, ConcreteCategory.comp_apply,
    lowerStarComp_hom_app_hom_app]
  rw [lowerStarComp_inv_app_hom_app]
  change (((g')^*[AddCommGrpCat.{u + 1}].obj F).obj.map _ ≫
    ((g')^*[AddCommGrpCat.{u + 1}].obj F).obj.map _ ≫
      ((g')^*[AddCommGrpCat.{u + 1}].obj F).obj.map _) _ = _
  rw [← Functor.map_comp, ← Functor.map_comp, pullSection]
  congr 2
  refine congrArg (fun a ↦ ((g')^*[AddCommGrpCat.{u + 1}].obj F).obj.map a) ?_
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op, Functor.op_map]
  apply hom_ext_pullback
  refine (?_ : _ = baseChangeSectionMap sq φ hφ).trans
    (homToPullback_left_fst g' (V := f'.Etale.obj V) (U := f.Etale.obj W) _ _).symm
  apply pullback.hom_ext <;> simp [homToPullback]

end AlgebraicGeometry.Etale
