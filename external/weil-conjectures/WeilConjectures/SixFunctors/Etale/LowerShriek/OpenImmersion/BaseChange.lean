/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!

# Base change for the extension by zero along a refinement

Let `j : X ⟶ C` and `k : X ⟶ D` be open immersions and let `q : C ⟶ D` be a morphism with
`j ≫ q = k`, so that `q` restricts to the identity of `X`. This file constructs the
canonical base change comparison

`j_! ⟶ k_! ∘ q^*`

on sheaves for the small étale sites, and proves that it is an isomorphism as soon as the
square

```
X --j--> C
|        |
𝟙        q
|        |
X --k--> D
```

is cartesian, i.e. `q ⁻¹ (X) = X`.

The comparison is the mate, under the adjunctions `j_! ⊣ j^*`, `k_! ⊣ k^*` and
`q^* ⊣ q_*`, of the base change map

`q_* ∘ k^* ≅ q_* ∘ q^* ∘ j^* ⟶ j^*`

of the right adjoints, given by the composition isomorphism `Etale.upperStarComp` followed
by the counit of `q^* ⊣ q_*`. Since a conjugate of an isomorphism is an isomorphism
(`CategoryTheory.conjugateEquiv_symm_iso`), it is enough to prove that this base change map
is one.

That in turn is a computation on the small étale sites. Both `q_*` and the pullback along
an open immersion are composition with a functor of small étale sites, namely base change
along `q` (`MorphismProperty.Over.pullback`) and the localization functor
(`MorphismProperty.Over.map`), so that `q_* ∘ k^*` is composition with
`Over.map k ⋙ Over.pullback q`, which sends `T ⟶ X` étale to `T ×_D C ⟶ C`, while `j^*` is
composition with `Over.map j`, which sends `T ⟶ X` to `T ⟶ C`. The comparison
`Etale.overMapPullbackComparison` is the canonical `T ⟶ T ×_D C`, and it is an isomorphism
when the square above is cartesian, since then `T ×_D C = T ×_X (X ×_D C) = T ×_X X = T`.

Identifying the counit description of the base change map with the one induced by
`Etale.overMapPullbackComparison` is `Etale.upperStarBaseChange_eq`. Both are mates of
natural transformations `j_* ⋙ q_* ⟶ k_*`, and `CategoryTheory.mateEquiv` is a bijection,
so it suffices to identify those two with the composition isomorphism
`Etale.lowerStarComp`; for the counit description this is formal, and for the site
description it is a computation with pullbacks of schemes.

The main application is to a refinement `r : c.Refinement d` of compactifications of a
morphism `f : S ⟶ Y` whose square over `S` is cartesian; this is part of the data of a
refinement of dense compactifications in the blueprint, and it is the geometric input for
the comparison of the two derived lower shrieks attached to `c` and to `d`.

## Main definitions

- `AlgebraicGeometry.Etale.overMapPullbackComparison`: the comparison
  `Over.map j ⟶ Over.map k ⋙ Over.pullback q` of functors of small étale sites.
- `AlgebraicGeometry.Etale.upperStarBaseChange`: the base change map
  `q_* ⋙ k^* ⟶ j^*` on étale sheaves, the composition isomorphism `k^* ≅ q^* ⋙ j^*`
  followed by the counit of `q^* ⊣ q_*`.
- `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChange`: the base change comparison
  `j_! ⟶ k_! ⋙ q^*`, the mate of `Etale.upperStarBaseChange`.
- `AlgebraicGeometry.Compactification.Refinement.openImmersionLowerShriekBaseChange`: the
  base change comparison `(c.i)_! ⟶ (d.i)_! ⋙ (r.hom)^*` attached to a refinement `r` of
  compactifications.

## Main results

- `AlgebraicGeometry.Etale.isIso_overMapPullbackComparison`: the comparison of site
  functors is an isomorphism when the square is cartesian.
- `AlgebraicGeometry.Etale.mateEquiv_upperStarBaseChange`: the mate of the base change map
  `q_* ⋙ k^* ⟶ j^*` is the composition isomorphism `j_* ⋙ q_* ≅ k_*`.
- `AlgebraicGeometry.Etale.upperStarBaseChange_eq`: the base change map defined by the
  counit of `q^* ⊣ q_*` is the one induced by the comparison of site functors.
- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChange`: **base change for the
  extension by zero**: `j_! ⟶ k_! ⋙ q^*` is an isomorphism when the square is cartesian.
- `AlgebraicGeometry.Compactification.Refinement.isIso_openImmersionLowerShriekBaseChange`:
  the same statement for a refinement of compactifications.
- `AlgebraicGeometry.Etale.upperStarBaseChange_id` and
  `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChange_id`: for `q = 𝟙 C` and
  `k = j` both base change maps are the canonical unitors, built from `Etale.lowerStarId`
  resp. `Etale.upperStarId`.
- `AlgebraicGeometry.Etale.upperStarBaseChange_comp` and
  `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChange_comp`: the **cocycle law**,
  expressing the base change map along a composite `q₁ ≫ q₂` as the composite of the base
  change maps along `q₁` and along `q₂`, reassociated through `Etale.lowerStarComp` resp.
  `Etale.upperStarComp`.
- `AlgebraicGeometry.Compactification.Refinement.openImmersionLowerShriekBaseChange_id` and
  `AlgebraicGeometry.Compactification.Refinement.openImmersionLowerShriekBaseChange_comp`:
  the two laws for the identity refinement and for a composite of refinements.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme MorphismProperty

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- For an étale morphism the localization functor between the small étale sites is
continuous. This is `CategoryTheory.GrothendieckTopology.isContinuous_overMap_of_le` for
`P = Q = @Etale`, registered as an instance. -/
instance Etale.isContinuous_overMap {V U : Scheme.{u}} {f : V ⟶ U} (hf : @Etale _ _ f) :
    (MorphismProperty.Over.map ⊤ hf).IsContinuous
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale) :=
  GrothendieckTopology.isContinuous_overMap_of_le hf le_rfl

variable {X C D : Scheme.{u}} (j : X ⟶ C) [IsOpenImmersion j] (q : C ⟶ D) (k : X ⟶ D)
  [IsOpenImmersion k] (hk : j ≫ q = k)

section Site

include hk

/-- The component at `b : X.Etale` of the comparison of site functors: the canonical
morphism `b ⟶ b ×_D C` over `C`, given by the identity of `b` and by `b ⟶ X ⟶ C`. -/
noncomputable def Etale.overMapPullbackComparisonApp (b : X.Etale) :
    (MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : @Etale _ _ j)).obj b ⟶
      (MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ k) ⋙
        MorphismProperty.Over.pullback @Etale ⊤ q).obj b :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 b.left) (b.hom ≫ j) (by cat_disch))
    (pullback.lift_snd _ _ _) trivial

@[simp]
lemma Etale.overMapPullbackComparisonApp_left (b : X.Etale) :
    (Etale.overMapPullbackComparisonApp j q k hk b).left =
      pullback.lift (𝟙 b.left) (b.hom ≫ j) (by cat_disch) := rfl

/-- The comparison `Over.map j ⟶ Over.map k ⋙ Over.pullback q` of functors of small étale
sites, sending `T ⟶ X` étale to the canonical morphism `T ⟶ T ×_D C` over `C`. -/
noncomputable def Etale.overMapPullbackComparison :
    MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : @Etale _ _ j) ⟶
      MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ k) ⋙
        MorphismProperty.Over.pullback @Etale ⊤ q where
  app b := Etale.overMapPullbackComparisonApp j q k hk b
  naturality b b' f := by
    ext
    simp only [MorphismProperty.Comma.comp_left, MorphismProperty.Over.map_map_left,
      Etale.overMapPullbackComparisonApp_left, Functor.comp_map,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · simp

/-- If the square is cartesian, the underlying morphism of schemes of the comparison of
site functors is an isomorphism: for `T ⟶ X` étale, pasting the cartesian square with the
trivial square over `T ⟶ X` identifies `T` with `T ×_D C`. -/
lemma Etale.isIso_overMapPullbackComparisonApp_left (hcart : IsPullback j (𝟙 X) q k)
    (b : X.Etale) :
    IsIso (Etale.overMapPullbackComparisonApp j q k hk b).left := by
  have h : IsPullback (b.hom ≫ j) (𝟙 b.left) q
      ((MorphismProperty.Over.map (P := @Etale) ⊤
        (inferInstance : @Etale _ _ k)).obj b).hom := by
    rw [MorphismProperty.Over.map_obj_hom]
    exact (IsPullback.id_vert b.hom).paste_horiz hcart
  have heq : (Etale.overMapPullbackComparisonApp j q k hk b).left = h.flip.isoPullback.hom := by
    apply pullback.hom_ext <;> simp
  rw [heq]
  infer_instance

/-- If the square is cartesian, the comparison of site functors is an isomorphism: a
morphism of the small étale site is an isomorphism as soon as the underlying morphism of
schemes is. -/
lemma Etale.isIso_overMapPullbackComparison (hcart : IsPullback j (𝟙 X) q k) :
    IsIso (Etale.overMapPullbackComparison j q k hk) := by
  have (b : X.Etale) : IsIso ((Etale.overMapPullbackComparison j q k hk).app b) := by
    have : IsIso ((MorphismProperty.Over.forget @Etale ⊤ C ⋙ CategoryTheory.Over.forget C).map
        ((Etale.overMapPullbackComparison j q k hk).app b)) :=
      Etale.isIso_overMapPullbackComparisonApp_left j q k hk hcart b
    exact isIso_of_reflects_iso _
      (MorphismProperty.Over.forget @Etale ⊤ C ⋙ CategoryTheory.Over.forget C)
  exact NatIso.isIso_of_isIso_app _

end Site

section Sheaf

open Etale

include hk in
/-- The base change map `q_* ⋙ k^* ⟶ j^*` on étale sheaves, with both pullbacks along the
open immersions computed as restrictions along the localization functors. All three
functors involved are composition with a functor of small étale sites, and the map is the
one induced by `Etale.overMapPullbackComparison`. -/
noncomputable def Etale.openImmersionRestrictionBaseChange :
    (q)_*[A] ⋙ Etale.openImmersionRestriction A k ⟶ Etale.openImmersionRestriction A j :=
  Functor.sheafPushforwardContinuousNatTrans (Etale.overMapPullbackComparison j q k hk) A
    (X.smallGrothendieckTopology @Etale) (C.smallGrothendieckTopology @Etale)

include hk in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- If the square is cartesian, the base change map on restrictions is an isomorphism,
being induced by an isomorphism of the site functors. -/
lemma Etale.isIso_openImmersionRestrictionBaseChange (hcart : IsPullback j (𝟙 X) q k) :
    IsIso (Etale.openImmersionRestrictionBaseChange A j q k hk) := by
  have := Etale.isIso_overMapPullbackComparison j q k hk hcart
  have : IsIso (Functor.sheafPushforwardContinuousIso
      (asIso (Etale.overMapPullbackComparison j q k hk)) A
      (X.smallGrothendieckTopology @Etale) (C.smallGrothendieckTopology @Etale)).inv :=
    inferInstance
  exact this

include hk in
/-- The composition isomorphism `k^* ≅ q^* ⋙ j^*` of pullbacks, for `j ≫ q = k`. -/
noncomputable def Etale.upperStarCompIso :
    (k)^*[A] ≅ (q)^*[A] ⋙ (j)^*[A] :=
  eqToIso (congrArg (fun g : X ⟶ D => (g)^*[A]) hk.symm) ≪≫ Etale.upperStarComp A j q

omit [IsOpenImmersion j] [HasSmallSiteSheafify A] in
@[simp]
lemma Etale.upperStarCompIso_rfl :
    Etale.upperStarCompIso A j q (j ≫ q) rfl = Etale.upperStarComp A j q := by
  simp [Etale.upperStarCompIso]

include hk in
/-- The base change map `q_* ⋙ k^* ⟶ j^*` on étale sheaves: the composition isomorphism
`k^* ≅ q^* ⋙ j^*` followed by the counit of `q^* ⊣ q_*`. -/
noncomputable def Etale.upperStarBaseChange :
    (q)_*[A] ⋙ (k)^*[A] ⟶ (j)^*[A] :=
  Functor.whiskerLeft (q)_*[A] (Etale.upperStarCompIso A j q k hk).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Etale.upperStarLowerStarAdjunction A q).counit (j)^*[A] ≫
    (Functor.leftUnitor _).hom

include hk in
omit [IsOpenImmersion j] [IsOpenImmersion k] in
/-- The mate of the base change map `q_* ⋙ k^* ⟶ j^*` under the adjunctions `j^* ⊣ j_*` and
`k^* ⊣ k_*` is the composition isomorphism `j_* ⋙ q_* ≅ k_*` of pushforwards

```
Sh(X) --j_*--> Sh(C)
  |              |
  𝟭      ⇙      q_*
  v              v
Sh(X) --k_*--> Sh(D)
```
-/
lemma Etale.mateEquiv_upperStarBaseChange :
    (mateEquiv (Etale.upperStarLowerStarAdjunction A j) (Etale.upperStarLowerStarAdjunction A k)
      (TwoSquare.mk ((q)_*[A]) ((j)^*[A]) ((k)^*[A]) (𝟭 _)
        (Etale.upperStarBaseChange A j q k hk))) =
      (Etale.lowerStarComp A j q k hk.symm).hom ≫ (Functor.leftUnitor _).inv := by
  subst hk
  have hconj : conjugateEquiv ((Etale.upperStarLowerStarAdjunction A q).comp
        (Etale.upperStarLowerStarAdjunction A j))
      (Etale.upperStarLowerStarAdjunction A (j ≫ q)) (Etale.upperStarComp A j q).hom =
      (Etale.lowerStarComp A j q).hom :=
    congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarComp A j q)
  have hmate : TwoSquare.mk ((q)_*[A]) ((j)^*[A]) ((j ≫ q)^*[A]) (𝟭 _)
      (Etale.upperStarBaseChange A j q (j ≫ q) rfl) =
      mateEquiv (Etale.upperStarLowerStarAdjunction A q) Adjunction.id
        (TwoSquare.mk ((j ≫ q)^*[A]) ((q)^*[A]) (𝟭 _) ((j)^*[A])
          (Etale.upperStarComp A j q).hom) := by
    ext F
    simp [mateEquiv, Etale.upperStarBaseChange]
  rw [hmate, iterated_mateEquiv_conjugateEquiv]
  refine NatTrans.ext (funext fun F => ?_)
  have := congrArg (fun t => NatTrans.app t F) hconj
  simp only [conjugateEquiv_apply_app, Adjunction.comp_unit_app, Adjunction.comp_counit_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc, Functor.id_obj,
    Functor.id_map, Category.comp_id, NatTrans.comp_app,
    Functor.leftUnitor_inv_app] at this ⊢
  simpa [Adjunction.id] using this

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
include hk in
/-- The base change map `q_* ⋙ k^* ⟶ j^*` built from the counit of `q^* ⊣ q_*` agrees with
the map `Etale.openImmersionRestrictionBaseChange` induced by the comparison of site
functors.

Both are mates, under the adjunctions `j^* ⊣ j_*` and `k^* ⊣ k_*`, of natural
transformations `j_* ⋙ q_* ⟶ k_*`, and `CategoryTheory.mateEquiv` is a bijection, so it
suffices to identify those with the composition isomorphism `Etale.lowerStarComp`. For the
counit description this is formal: it is `CategoryTheory.iterated_mateEquiv_conjugateEquiv`
together with the construction of `Etale.upperStarComp` as a conjugate of
`Etale.lowerStarComp`. For the site description it is a computation on the small étale
sites, where all functors and both adjunctions come from the sites. -/
lemma Etale.upperStarBaseChange_eq :
    Etale.upperStarBaseChange A j q k hk =
      Functor.whiskerLeft (q)_*[A] (Etale.upperStarIsoOpenImmersionRestriction A k).hom ≫
        Etale.openImmersionRestrictionBaseChange A j q k hk ≫
        (Etale.upperStarIsoOpenImmersionRestriction A j).inv := by
  subst hk
  have hsite : (mateEquiv (Etale.openImmersionRestrictionLowerStarAdjunction A j)
      (Etale.openImmersionRestrictionLowerStarAdjunction A (j ≫ q))
      (TwoSquare.mk ((q)_*[A]) (Etale.openImmersionRestriction A j)
        (Etale.openImmersionRestriction A (j ≫ q)) (𝟭 _)
        (Etale.openImmersionRestrictionBaseChange A j q (j ≫ q) rfl))) =
      (Etale.lowerStarComp A j q).hom ≫ (Functor.leftUnitor _).inv := by
    ext F b
    obtain ⟨b⟩ := b
    simp only [mateEquiv, Equiv.coe_fn_mk, Etale.openImmersionRestrictionLowerStarAdjunction,
      Etale.openImmersionRestrictionBaseChange, Etale.lowerStarComp,
      Etale.localizationRestrictionLowerStarAdjunction]
    simp only [Functor.comp_obj, Functor.id_obj, Adjunction.sheafPushforwardContinuous,
      Adjunction.whiskerLeft, Functor.whiskeringLeft_obj_obj, Adjunction.op_unit_app,
      Adjunction.op_counit_app, Functor.sheafPushforwardContinuousNatTrans, ObjectProperty.ι_obj,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.id_map, Functor.leftUnitor_hom_app, comp_id, id_comp,
      ObjectProperty.FullSubcategory.comp_hom, assoc, Functor.leftUnitor_inv_app,
      Functor.op_obj, NatTrans.op_app, MorphismProperty.Over.mapPullbackAdj_counit_app,
      Etale.lowerStar_map_hom_app, MorphismProperty.Over.mapPullbackAdj_unit_app,
      MorphismProperty.Over.pullback_obj_left, MorphismProperty.Over.pullback_obj_hom,
      Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv]
    change F.obj.map _ ≫ F.obj.map _ ≫ 𝟙 _ ≫ F.obj.map _ = _
    rw [Category.id_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op, Functor.op_map]
    ext
    simp only [MorphismProperty.Comma.comp_left, MorphismProperty.Over.pullback_map_left,
      MorphismProperty.Over.homMk_hom, Etale.overMapPullbackComparisonApp_left,
      Etale.overMapPullbackComparison]
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp
    · simp
  have hA := Etale.mateEquiv_upperStarBaseChange A j q (j ≫ q) rfl
  -- The site description is transported to the pullbacks by `mateEquiv_leftAdjointUniq`.
  have hB := mateEquiv_leftAdjointUniq (Etale.upperStarLowerStarAdjunction A j)
    (Etale.openImmersionRestrictionLowerStarAdjunction A j)
    (Etale.upperStarLowerStarAdjunction A (j ≫ q))
    (Etale.openImmersionRestrictionLowerStarAdjunction A (j ≫ q))
    (TwoSquare.mk ((q)_*[A]) (Etale.openImmersionRestriction A j)
      (Etale.openImmersionRestriction A (j ≫ q)) (𝟭 _)
      (Etale.openImmersionRestrictionBaseChange A j q (j ≫ q) rfl))
  exact (mateEquiv (Etale.upperStarLowerStarAdjunction A j)
    (Etale.upperStarLowerStarAdjunction A (j ≫ q))).injective
    (hA.trans (hsite.symm.trans (hB).symm))

include hk in
/-- If the square is cartesian, the base change map `q_* ⋙ k^* ⟶ j^*` is an isomorphism. -/
lemma Etale.isIso_upperStarBaseChange (hcart : IsPullback j (𝟙 X) q k) :
    IsIso (Etale.upperStarBaseChange A j q k hk) := by
  have := Etale.isIso_openImmersionRestrictionBaseChange A j q k hk hcart
  rw [Etale.upperStarBaseChange_eq]
  infer_instance

include hk in
/-- The base change comparison `j_! ⟶ k_! ⋙ q^*` for the extension by zero along an open
immersion: the mate of `Etale.upperStarBaseChange` under the adjunctions `j_! ⊣ j^*` and
`k_! ⋙ q^* ⊣ q_* ⋙ k^*`. -/
noncomputable def Etale.openImmersionLowerShriekBaseChange :
    (j)_!open[A] ⟶ (k)_!open[A] ⋙ (q)^*[A] :=
  (conjugateEquiv ((Etale.openImmersionLowerShriekUpperStarAdjunction A k).comp
      (Etale.upperStarLowerStarAdjunction A q))
    (Etale.openImmersionLowerShriekUpperStarAdjunction A j)).symm
    (Etale.upperStarBaseChange A j q k hk)

include hk in
/-- **Base change for the extension by zero**: if the square is cartesian, the comparison
`j_! ⟶ k_! ⋙ q^*` is an isomorphism, being the conjugate of the isomorphism
`Etale.upperStarBaseChange`. -/
lemma Etale.isIso_openImmersionLowerShriekBaseChange (hcart : IsPullback j (𝟙 X) q k) :
    IsIso (Etale.openImmersionLowerShriekBaseChange A j q k hk) := by
  have := Etale.isIso_upperStarBaseChange A j q k hk hcart
  exact conjugateEquiv_symm_iso _ _ _

end Sheaf

section Coherence

open Etale

variable {X C D E : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- The composition isomorphism `Etale.upperStarCompIso` is the instance at `k` of the
generalized composition isomorphism `Etale.upperStarComp`; in this form the unit and
associativity laws of `Etale.upperStarComp` apply to it. -/
lemma Etale.upperStarCompIso_eq_upperStarComp (j : X ⟶ C) (q : C ⟶ D) (k : X ⟶ D)
    (hk : j ≫ q = k) :
    Etale.upperStarCompIso A j q k hk = Etale.upperStarComp A j q k hk.symm := by
  subst hk
  simp

omit [HasSmallSiteSheafify A] in
/-- The component at a sheaf `F` of the base change map `q_* ⋙ k^* ⟶ j^*`: the composition
isomorphism evaluated at `q_* F`, followed by the pullback along `j` of the counit of
`q^* ⊣ q_*`. -/
lemma Etale.upperStarBaseChange_app (j : X ⟶ C) (q : C ⟶ D) (k : X ⟶ D) (hk : j ≫ q = k)
    (F : Sheaf C.smallEtaleTopology A) :
    (Etale.upperStarBaseChange A j q k hk).app F =
      (Etale.upperStarComp A j q k hk.symm).hom.app (((q)_*[A]).obj F) ≫
        ((j)^*[A]).map ((Etale.upperStarLowerStarAdjunction A q).counit.app F) := by
  simp [Etale.upperStarBaseChange, Etale.upperStarCompIso_eq_upperStarComp]

/-- **Identity law for the base change map on pullbacks**: for `q = 𝟙 C` and `k = j` the
base change map `(𝟙 C)_* ⋙ j^* ⟶ j^*` is the unitor built from `Etale.lowerStarId`. -/
lemma Etale.upperStarBaseChange_id (j : X ⟶ C) (hj : j ≫ 𝟙 C = j) :
    Etale.upperStarBaseChange A j (𝟙 C) j hj =
      Functor.whiskerRight (Etale.lowerStarId A C).hom (j)^*[A] ≫
        ((j)^*[A]).leftUnitor.hom := by
  ext F
  rw [Etale.upperStarBaseChange_app, Etale.upperStarComp_id_right A j]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_obj, Functor.id_obj,
    id_comp, comp_id, Functor.leftUnitor_hom_app]
  rw [← Functor.map_comp, Etale.upperStarId_inv_app_counit_app]

/-- **Cocycle law for the base change map on pullbacks**: for `j ≫ q₁ = k` and
`k ≫ q₂ = l`, the base change map along `q₁ ≫ q₂` is the composite of the base change maps
along `q₂` and along `q₁`, reassociated through `Etale.lowerStarComp`. -/
lemma Etale.upperStarBaseChange_comp (j : X ⟶ C) (q₁ : C ⟶ D) (q₂ : D ⟶ E) (k : X ⟶ D)
    (l : X ⟶ E) (hk : j ≫ q₁ = k) (hl : k ≫ q₂ = l) (hjl : j ≫ (q₁ ≫ q₂) = l) :
    Etale.upperStarBaseChange A j (q₁ ≫ q₂) l hjl =
      Functor.whiskerRight (Etale.lowerStarComp A q₁ q₂).inv (l)^*[A] ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (q₁)_*[A] (Etale.upperStarBaseChange A k q₂ l hl) ≫
        Etale.upperStarBaseChange A j q₁ k hk := by
  subst hk hl
  refine NatTrans.ext (funext fun F => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Etale.upperStarBaseChange_app, Functor.comp_obj, id_comp, assoc]
  rw [(Etale.upperStarComp A (j ≫ q₁) q₂ ((j ≫ q₁) ≫ q₂) rfl).hom.naturality_assoc,
    Functor.comp_map, ← Functor.map_comp_assoc]
  have hb := (Etale.upperStarComp A j q₁ (j ≫ q₁) rfl).hom.naturality_assoc
    (((q₂)^*[A]).map ((Etale.lowerStarComp A q₁ q₂).inv.app F) ≫
      (Etale.upperStarLowerStarAdjunction A q₂).counit.app (((q₁)_*[A]).obj F))
    (((j)^*[A]).map ((Etale.upperStarLowerStarAdjunction A q₁).counit.app F))
  simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map] at hb
  rw [hb]
  have hc := NatTrans.congr_app (congrArg Iso.hom
    (Etale.upperStarComp_assoc A j q₁ q₂ ((j ≫ q₁) ≫ q₂) (Category.assoc j q₁ q₂)))
    (((q₁ ≫ q₂)_*[A]).obj F)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.comp_obj, comp_id] at hc
  rw [← reassoc_of% hc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  rw [Functor.map_comp, assoc,
    ← Etale.upperStarComp_inv_app_counit_app A q₁ q₂ F (q₁ ≫ q₂) rfl,
    Iso.hom_inv_id_app_assoc]

/-- **Identity law for the base change comparison of the extension by zero**: for
`q = 𝟙 C` and `k = j` the comparison `j_! ⟶ j_! ⋙ (𝟙 C)^*` is the unitor built from
`Etale.upperStarId`. -/
lemma Etale.openImmersionLowerShriekBaseChange_id (j : X ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ 𝟙 C = j) :
    Etale.openImmersionLowerShriekBaseChange A j (𝟙 C) j hj =
      ((j)_!open[A]).rightUnitor.inv ≫
        Functor.whiskerLeft (j)_!open[A] (Etale.upperStarId A C).inv := by
  have hconj : conjugateEquiv (Etale.upperStarLowerStarAdjunction A (𝟙 C))
      (Adjunction.id (C := Sheaf C.smallEtaleTopology A))
      (Etale.upperStarId A C).inv = (Etale.lowerStarId A C).hom :=
    congrArg Iso.inv (Etale.conjugateIsoEquiv_upperStarId A C)
  have hru : conjugateEquiv
      ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).comp
        (Adjunction.id (C := Sheaf C.smallEtaleTopology A)))
      (Etale.openImmersionLowerShriekUpperStarAdjunction A j)
      ((j)_!open[A]).rightUnitor.inv = ((j)^*[A]).leftUnitor.hom :=
    congrArg Iso.inv (conjugateIsoEquiv_rightUnitor
      (Etale.openImmersionLowerShriekUpperStarAdjunction A j))
  rw [Etale.openImmersionLowerShriekBaseChange, Equiv.symm_apply_eq,
    Etale.upperStarBaseChange_id,
    ← conjugateEquiv_comp _ ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).comp
      (Adjunction.id (C := Sheaf C.smallEtaleTopology A))) _,
    conjugateEquiv_whiskerLeft, hconj, hru]

/-- **Cocycle law for the base change comparison of the extension by zero**: for
`j ≫ q₁ = k` and `k ≫ q₂ = l`, the comparison along `q₁ ≫ q₂` is the composite of the
comparisons along `q₁` and along `q₂`, reassociated through `Etale.upperStarComp`. -/
lemma Etale.openImmersionLowerShriekBaseChange_comp (j : X ⟶ C) [IsOpenImmersion j]
    (q₁ : C ⟶ D) (q₂ : D ⟶ E) (k : X ⟶ D) [IsOpenImmersion k] (l : X ⟶ E)
    [IsOpenImmersion l] (hk : j ≫ q₁ = k) (hl : k ≫ q₂ = l) (hjl : j ≫ (q₁ ≫ q₂) = l) :
    Etale.openImmersionLowerShriekBaseChange A j (q₁ ≫ q₂) l hjl =
      Etale.openImmersionLowerShriekBaseChange A j q₁ k hk ≫
        Functor.whiskerRight (Etale.openImmersionLowerShriekBaseChange A k q₂ l hl) (q₁)^*[A] ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (l)_!open[A] (Etale.upperStarComp A q₁ q₂).inv := by
  have hconj : conjugateEquiv (Etale.upperStarLowerStarAdjunction A (q₁ ≫ q₂))
      ((Etale.upperStarLowerStarAdjunction A q₂).comp
        (Etale.upperStarLowerStarAdjunction A q₁))
      (Etale.upperStarComp A q₁ q₂).inv = (Etale.lowerStarComp A q₁ q₂).inv :=
    congrArg Iso.inv (Etale.conjugateIsoEquiv_upperStarComp A q₁ q₂)
  simp only [Etale.openImmersionLowerShriekBaseChange]
  rw [Equiv.symm_apply_eq, Etale.upperStarBaseChange_comp A j q₁ q₂ k l hk hl hjl,
    ← conjugateEquiv_comp _ ((Etale.openImmersionLowerShriekUpperStarAdjunction A k).comp
      (Etale.upperStarLowerStarAdjunction A q₁)) _,
    ← conjugateEquiv_comp _ (((Etale.openImmersionLowerShriekUpperStarAdjunction A l).comp
      (Etale.upperStarLowerStarAdjunction A q₂)).comp
      (Etale.upperStarLowerStarAdjunction A q₁)) _,
    ← conjugateEquiv_comp _ ((Etale.openImmersionLowerShriekUpperStarAdjunction A l).comp
      ((Etale.upperStarLowerStarAdjunction A q₂).comp
        (Etale.upperStarLowerStarAdjunction A q₁))) _,
    conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    hconj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [Category.assoc]

end Coherence

section Refinement

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {S Y : Scheme.{u}} {f : S ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

open Etale

/-- The base change comparison `(c.i)_! ⟶ (d.i)_! ⋙ (r.hom)^*` attached to a refinement
`r` of the compactification `d` by the compactification `c`. -/
noncomputable def Compactification.Refinement.openImmersionLowerShriekBaseChange :
    (c.i)_!open[A] ⟶ (d.i)_!open[A] ⋙ (r.hom)^*[A] :=
  Etale.openImmersionLowerShriekBaseChange A c.i r.hom d.i r.i_hom

/-- If the square of a refinement `r` over `S` is cartesian, i.e. `r.hom ⁻¹ (S) = S`, then
the base change comparison `(c.i)_! ⟶ (d.i)_! ⋙ (r.hom)^*` is an isomorphism.
(blueprint: `BA43-DENSE-DATA`) -/
lemma Compactification.Refinement.isIso_openImmersionLowerShriekBaseChange
    (hcart : IsPullback c.i (𝟙 S) r.hom d.i) :
    IsIso (r.openImmersionLowerShriekBaseChange A) :=
  Etale.isIso_openImmersionLowerShriekBaseChange A c.i r.hom d.i r.i_hom hcart

/-- **Identity law**: the base change comparison attached to the identity refinement of a
compactification `c` is the unitor built from `Etale.upperStarId`. -/
lemma Compactification.Refinement.openImmersionLowerShriekBaseChange_id
    (c : Compactification f) :
    (Compactification.Refinement.id c).openImmersionLowerShriekBaseChange A =
      ((c.i)_!open[A]).rightUnitor.inv ≫
        Functor.whiskerLeft (c.i)_!open[A] (Etale.upperStarId A c.Z).inv :=
  Etale.openImmersionLowerShriekBaseChange_id A c.i _

/-- **Cocycle law**: the base change comparison attached to a composite of refinements is
the composite of the two comparisons, reassociated through `Etale.upperStarComp`. -/
lemma Compactification.Refinement.openImmersionLowerShriekBaseChange_comp
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    (r.comp s).openImmersionLowerShriekBaseChange A =
      r.openImmersionLowerShriekBaseChange A ≫
        Functor.whiskerRight (s.openImmersionLowerShriekBaseChange A) (r.hom)^*[A] ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (e.i)_!open[A] (Etale.upperStarComp A r.hom s.hom).inv :=
  Etale.openImmersionLowerShriekBaseChange_comp A c.i r.hom s.hom d.i e.i r.i_hom s.i_hom _

end Refinement

end AlgebraicGeometry
