/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!

# Étale base change for the pushforward

Consider a commutative square of schemes

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

with `j` and `j'` étale, i.e. `g' ≫ j = j' ≫ g''`. This file proves **étale base change for
the pushforward** (Stacks 0F4D, SGA 4 VIII): if the square is cartesian, the base change map

`j^* ∘ g''_* ⟶ g'_* ∘ j'^*`

on sheaves for the small étale sites is an isomorphism.

Along an étale morphism the pullback is computed by restriction along the localization
functor `Over.map` (`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`), so both
`g''_* ⋙ j^*` and `j'^* ⋙ g'_*` are composition with functors of small étale sites:
`Over.map j ⋙ Over.pullback g''` sends `T ⟶ U` to `T ×_Z Z' ⟶ Z'`, and
`Over.pullback g' ⋙ Over.map j'` sends it to `T ×_U U' ⟶ Z'`. The canonical comparison
`T ×_U U' ⟶ T ×_Z Z'` is `CategoryTheory.MorphismProperty.Over.pullbackMapComparison`, and it
is an isomorphism when the square is cartesian.

## Main definitions

- `AlgebraicGeometry.Etale.localizationRestrictionBaseChangeMap`: the map
  `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` induced by the comparison of site functors, with the
  pullbacks computed as restrictions.

## Main results

- `AlgebraicGeometry.Etale.mateEquiv_localizationRestrictionBaseChangeMap`: the mate of
  `localizationRestrictionBaseChangeMap` under `j'^* ⊣ j'_*` and `j^* ⊣ j_*` is the square
  isomorphism `j'_* ⋙ g''_* ≅ g'_* ⋙ j_*` of pushforwards.
- `AlgebraicGeometry.Etale.baseChangeMap_flip_eq`: the base change map of the flipped square
  is `localizationRestrictionBaseChangeMap`, transported along
  `upperStarIsoLocalizationRestriction`.
- `AlgebraicGeometry.Etale.isIso_baseChangeMap_flip_of_isPullback`: **étale base change for
  the pushforward**: for a cartesian square the base change map
  `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` is an isomorphism.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme MorphismProperty Etale

variable (A : Type u') [Category.{u + 1} A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [Etale j] [Etale j']

/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` on étale sheaves, with the pullbacks
along the étale morphisms `j` and `j'` computed as restrictions along the localization
functors

```
Sh(Z') --g''_*--> Sh(Z)
  |                 |
 j'^*      ⇙       j^*
  v                 v
Sh(U') --g'_*-->  Sh(U)
```

All functors involved are composition with functors of small étale sites, and the map is
the one induced by `CategoryTheory.MorphismProperty.Over.pullbackMapComparison`. -/
noncomputable def Etale.localizationRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    (g'')_*[A] ⋙ Etale.localizationRestriction A j inferInstance ⟶
      Etale.localizationRestriction A j' inferInstance ⋙ (g')_*[A] :=
  Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @Etale _ _ j)
      (inferInstance : @Etale _ _ j') sq) A
    (U.smallGrothendieckTopology @Etale) (Z'.smallGrothendieckTopology @Etale)

/-- If the square is cartesian, the base change map on restrictions is an isomorphism,
being induced by an isomorphism of site functors. -/
lemma Etale.isIso_localizationRestrictionBaseChangeMap_of_isPullback
    (hsq : IsPullback g' j' j g'') :
    IsIso (Etale.localizationRestrictionBaseChangeMap A hsq.toCommSq) :=
  have := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : @Etale _ _ j) (inferInstance : @Etale _ _ j') hsq
  inferInstanceAs (IsIso (Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @Etale _ _ j)
      (inferInstance : @Etale _ _ j') hsq.toCommSq) A
    (U.smallGrothendieckTopology @Etale) (Z'.smallGrothendieckTopology @Etale)))

/-- The mate of `Etale.localizationRestrictionBaseChangeMap` under the adjunctions
`j'^* ⊣ j'_*` and `j^* ⊣ j_*` is the square isomorphism `j'_* ⋙ g''_* ≅ g'_* ⋙ j_*` of
pushforwards (`Etale.squareLowerStarIso`)

```
Sh(U') --j'_*--> Sh(Z')
  |                 |
 g'_*      ⇙      g''_*
  v                 v
Sh(U)  --j_*-->  Sh(Z)
```
-/
lemma Etale.mateEquiv_localizationRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    (mateEquiv (Etale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (Etale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (Etale.localizationRestrictionBaseChangeMap A sq))) =
      (Etale.squareLowerStarIso A sq.flip).hom := by
  ext F ⟨b⟩
  simp only [Functor.comp_obj, mateEquiv, Etale.localizationRestrictionLowerStarAdjunction,
    Adjunction.sheafPushforwardContinuous, Functor.id_obj,
    Etale.localizationRestrictionBaseChangeMap, Functor.sheafPushforwardContinuousNatTrans,
    ObjectProperty.ι_obj, Equiv.coe_fn_mk, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.leftUnitor_hom_app, comp_id, id_comp,
    ObjectProperty.FullSubcategory.comp_hom, Adjunction.whiskerLeft_unit_app_app,
    Functor.op_obj, Adjunction.op_unit_app, NatTrans.op_app,
    MorphismProperty.Over.mapPullbackAdj_counit_app, Etale.lowerStar_map_hom_app,
    Adjunction.whiskerLeft_counit_app_app, Adjunction.op_counit_app,
    MorphismProperty.Over.mapPullbackAdj_unit_app, MorphismProperty.Over.pullback_obj_hom,
    Etale.squareLowerStarIso, Etale.lowerStarComp, Iso.trans_hom, Iso.symm_hom,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app]
  rw [Etale.lowerStar_obj_val_map, Etale.lowerStar_obj_val_map, Etale.lowerStar_obj_val_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  -- `simp` only applies `pullback.lift_fst` to the units of `Over.mapPullbackAdj` with the
  -- backward behaviour of the `defeq` attribute.
  set_option backward.defeqAttrib.useBackward true in
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp
  · simp

variable [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of the flipped square agrees with the map
`Etale.localizationRestrictionBaseChangeMap` induced by the comparison of site functors,
transported along the identifications `j^* ≅ j_{loc}^*` and `j'^* ≅ j'_{loc}^*` of
`Etale.upperStarIsoLocalizationRestriction`

```
Sh(Z') --g''_*--> Sh(Z)
  |                 |
 j'^*      ⇙       j^*
  v                 v
Sh(U') --g'_*-->  Sh(U)
```
-/
lemma Etale.baseChangeMap_flip_eq (sq : CommSq g' j' j g'') :
    Etale.baseChangeMap A sq.flip =
      Functor.whiskerLeft (g'')_*[A]
          (Etale.upperStarIsoLocalizationRestriction A j inferInstance).hom ≫
        Etale.localizationRestrictionBaseChangeMap A sq ≫
        Functor.whiskerRight (Etale.upperStarIsoLocalizationRestriction A j' inferInstance).inv
          (g')_*[A] := by
  -- Both sides are mates, under `j'^* ⊣ j'_*` and `j^* ⊣ j_*`, of the square isomorphism
  -- `j'_* ⋙ g''_* ≅ g'_* ⋙ j_*` of pushforwards.
  apply (mateEquiv (Etale.upperStarLowerStarAdjunction A j')
    (Etale.upperStarLowerStarAdjunction A j)).injective
  refine (Etale.mateEquiv_baseChangeSquare A sq.flip).trans ?_
  rw [Etale.upperStarIsoLocalizationRestriction, Etale.upperStarIsoLocalizationRestriction,
    mateEquiv_leftAdjointUniq]
  exact (Etale.mateEquiv_localizationRestrictionBaseChangeMap A sq).symm

/-- **Étale base change for the pushforward**: if the square is cartesian, the base change
map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of the flipped square is an isomorphism. By
`AlgebraicGeometry.Etale.baseChangeMap_flip_eq` it is induced by an isomorphism of site
functors. -/
lemma Etale.isIso_baseChangeMap_flip_of_isPullback (hsq : IsPullback g' j' j g'') :
    IsIso (Etale.baseChangeMap A hsq.toCommSq.flip) := by
  have := Etale.isIso_localizationRestrictionBaseChangeMap_of_isPullback A hsq
  rw [Etale.baseChangeMap_flip_eq A hsq.toCommSq]
  infer_instance

end AlgebraicGeometry
