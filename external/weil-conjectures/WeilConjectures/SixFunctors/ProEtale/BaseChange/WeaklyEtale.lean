/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Weakly étale base change for the pro-étale pushforward

Consider a commutative square of schemes

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

with `j` and `j'` weakly étale, i.e. `g' ≫ j = j' ≫ g''`. This file proves **weakly étale base
change for the pushforward** on the small pro-étale sites, the pro-étale counterpart of
`WeilConjectures.SixFunctors.BaseChange.Etale`: if the square is cartesian, the base change map

`j^* ∘ g''_* ⟶ g'_* ∘ j'^*`

is an isomorphism. Along a weakly étale morphism the pullback is computed by restriction along
the localization functor (`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), so
both sides are composition with functors of small pro-étale sites, compared by
`CategoryTheory.MorphismProperty.Over.pullbackMapComparison`.

The base change map is defined here as the mate, along `j'^* ⊣ j'_*` and `j^* ⊣ j_*`, of the
square isomorphism `j'_* ⋙ g''_* ≅ g'_* ⋙ j_*` of pushforwards: this only involves the
pullbacks along the weakly étale `j` and `j'`.

## Main definitions

- `AlgebraicGeometry.ProEtale.squareLowerStarIso`: `j'_* ⋙ g''_* ≅ g'_* ⋙ j_*`.
- `AlgebraicGeometry.ProEtale.localizationRestrictionBaseChangeMap`: the base change map with
  the pullbacks computed as restrictions.
- `AlgebraicGeometry.ProEtale.baseChangeMap`: the base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*`.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback`: weakly étale base change.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme MorphismProperty ProEtale

variable (A : Type u') [Category.{u + 1} A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}

/-- The square isomorphism `j'_* ⋙ g''_* ≅ g'_* ⋙ j_*` of pushforwards attached to a commutative
square `g' ≫ j = j' ≫ g''`: both sides are identified with the pushforward along the diagonal
by `AlgebraicGeometry.ProEtale.lowerStarComp`. -/
noncomputable def ProEtale.squareLowerStarIso (sq : CommSq g' j' j g'') :
    (j')_*[A] ⋙ (g'')_*[A] ≅ (g')_*[A] ⋙ (j)_*[A] :=
  lowerStarComp A j' g'' ≪≫ lowerStarCongr A sq.w.symm ≪≫ (lowerStarComp A g' j).symm

omit [Category.{u + 1} A] in
/-- The restriction maps of `g_* G` are those of `G` along the base changed morphisms. -/
lemma ProEtale.lowerStar_obj_obj_map [Category.{u + 1} A] {Y W : Scheme.{u}} (g : W ⟶ Y)
    (G : Sheaf (Scheme.ProEt.topology W) A) {b b' : Y.ProEt} (φ : b ⟶ b') :
    ((g)_*[A].obj G).obj.map φ.op =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map φ).op :=
  rfl

variable [WeaklyEtale j] [WeaklyEtale j']

instance : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g' ⋙
    MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j')).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
  have := Scheme.ProEt.isContinuous_overPullback g'
  have := Scheme.ProEt.isContinuous_overMap (inferInstance : @WeaklyEtale _ _ j')
  Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology U') _

instance : (MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j) ⋙
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g'').IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
  have := Scheme.ProEt.isContinuous_overPullback g''
  have := Scheme.ProEt.isContinuous_overMap (inferInstance : @WeaklyEtale _ _ j)
  Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology Z) _

/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` on pro-étale sheaves, with the pullbacks
along the weakly étale morphisms `j` and `j'` computed as restrictions along the localization
functors: the map induced by `CategoryTheory.MorphismProperty.Over.pullbackMapComparison`. -/
noncomputable def ProEtale.localizationRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    (g'')_*[A] ⋙ ProEtale.localizationRestriction A j inferInstance ⟶
      ProEtale.localizationRestriction A j' inferInstance ⋙ (g')_*[A] :=
  Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') sq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')

/-- If the square is cartesian, the base change map on restrictions is an isomorphism, being
induced by an isomorphism of site functors. -/
lemma ProEtale.isIso_localizationRestrictionBaseChangeMap_of_isPullback
    (hsq : IsPullback g' j' j g'') :
    IsIso (ProEtale.localizationRestrictionBaseChangeMap A hsq.toCommSq) :=
  have := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : @WeaklyEtale _ _ j) (inferInstance : @WeaklyEtale _ _ j') hsq
  inferInstanceAs (IsIso (Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') hsq.toCommSq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')))

/-- The mate of `ProEtale.localizationRestrictionBaseChangeMap` under the adjunctions
`j'^* ⊣ j'_*` and `j^* ⊣ j_*` is the square isomorphism of pushforwards. -/
lemma ProEtale.mateEquiv_localizationRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    (mateEquiv (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (ProEtale.localizationRestrictionBaseChangeMap A sq))) =
      (ProEtale.squareLowerStarIso A sq).hom := by
  ext F ⟨b⟩
  simp only [Functor.comp_obj, mateEquiv, ProEtale.localizationRestrictionLowerStarAdjunction,
    Adjunction.sheafPushforwardContinuous, Functor.id_obj,
    ProEtale.localizationRestrictionBaseChangeMap, Functor.sheafPushforwardContinuousNatTrans,
    ObjectProperty.ι_obj, Equiv.coe_fn_mk, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.leftUnitor_hom_app, comp_id, id_comp,
    ObjectProperty.FullSubcategory.comp_hom, Adjunction.whiskerLeft_unit_app_app,
    Functor.op_obj, Adjunction.op_unit_app, NatTrans.op_app,
    MorphismProperty.Over.mapPullbackAdj_counit_app, ProEtale.lowerStar_map_hom_app,
    Adjunction.whiskerLeft_counit_app_app, Adjunction.op_counit_app,
    MorphismProperty.Over.mapPullbackAdj_unit_app, MorphismProperty.Over.pullback_obj_hom,
    ProEtale.squareLowerStarIso, Iso.trans_hom, Iso.symm_hom]
  rw [lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app, ProEtale.lowerStar_obj_obj_map,
    ProEtale.lowerStar_obj_obj_map, ProEtale.lowerStar_obj_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  set_option backward.defeqAttrib.useBackward true in
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]

variable [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **The base change map** `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of a commutative square
`g' ≫ j = j' ≫ g''` with `j`, `j'` weakly étale: the mate, along `j'^* ⊣ j'_*` and
`j^* ⊣ j_*`, of the square isomorphism `ProEtale.squareLowerStarIso` of pushforwards. -/
noncomputable def ProEtale.baseChangeMap (sq : CommSq g' j' j g'') :
    (g'')_*[A] ⋙ (j)^*[A] ⟶ (j')^*[A] ⋙ (g')_*[A] :=
  ((mateEquiv (upperStarLowerStarAdjunction A j') (upperStarLowerStarAdjunction A j)).symm
    (TwoSquare.mk _ _ _ _ (ProEtale.squareLowerStarIso A sq).hom))

/-- The base change map agrees with `ProEtale.localizationRestrictionBaseChangeMap`,
transported along the identifications `j^* ≅ j_{loc}^*` and `j'^* ≅ j'_{loc}^*`. -/
lemma ProEtale.baseChangeMap_eq (sq : CommSq g' j' j g'') :
    ProEtale.baseChangeMap A sq =
      Functor.whiskerLeft (g'')_*[A]
          (ProEtale.upperStarIsoLocalizationRestriction A j inferInstance).hom ≫
        ProEtale.localizationRestrictionBaseChangeMap A sq ≫
        Functor.whiskerRight
          (ProEtale.upperStarIsoLocalizationRestriction A j' inferInstance).inv (g')_*[A] := by
  have h := mateEquiv_leftAdjointUniq (upperStarLowerStarAdjunction A j')
    (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
    (upperStarLowerStarAdjunction A j)
    (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
    (TwoSquare.mk _ _ _ _ (ProEtale.localizationRestrictionBaseChangeMap A sq))
  have h' : TwoSquare.mk _ _ _ _ (ProEtale.squareLowerStarIso A sq).hom =
      mateEquiv (upperStarLowerStarAdjunction A j') (upperStarLowerStarAdjunction A j)
        (TwoSquare.mk _ _ _ _ (Functor.whiskerLeft (g'')_*[A]
          (ProEtale.upperStarIsoLocalizationRestriction A j inferInstance).hom ≫
          ProEtale.localizationRestrictionBaseChangeMap A sq ≫
          Functor.whiskerRight
            (ProEtale.upperStarIsoLocalizationRestriction A j' inferInstance).inv
              (g')_*[A])) := by
    refine Eq.trans ?_ h.symm
    exact (ProEtale.mateEquiv_localizationRestrictionBaseChangeMap A sq).symm
  rw [ProEtale.baseChangeMap, h', Equiv.symm_apply_apply]

/-- **Weakly étale base change for the pushforward**: for a cartesian square the base change
map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` is an isomorphism. -/
lemma ProEtale.isIso_baseChangeMap_of_isPullback (hsq : IsPullback g' j' j g'') :
    IsIso (ProEtale.baseChangeMap A hsq.toCommSq) := by
  have := ProEtale.isIso_localizationRestrictionBaseChangeMap_of_isPullback A hsq
  rw [ProEtale.baseChangeMap_eq A hsq.toCommSq]
  infer_instance

end AlgebraicGeometry
