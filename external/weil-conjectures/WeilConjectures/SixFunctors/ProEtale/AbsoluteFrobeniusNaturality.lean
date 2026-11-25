/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FrobeniusPoint

/-!
# Naturality of the absolute Frobenius trivialization on the small pro-étale site

Let `g : T ⟶ X` be a morphism of schemes in which the prime `p` vanishes, and `F_X`, `F_T` the
`p ^ n`-power absolute Frobenii, so that `g ≫ F_X = F_T ≫ g`. For an object `V` of the small
pro-étale site of `X`, the relative Frobenius maps of `V` and of its base change `V ×_X T` are
compatible with the base change along `g`: both send `(v, t)` to `((F_V v, g t), t)`. Hence the
trivializations `F_{X*} ≅ 𝟭` and `F_{T*} ≅ 𝟭` of the pushforwards of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.lowerStarIterateFrobeniusIso`) are compatible with the pushforward
`g_*`.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.overPullbackIterateFrobeniusIso_inv_app_naturality`,
  `pullbackComp_hom_app_comp_map_overPullbackIterateFrobeniusIso_hom_app`:
  the site-level statements.
- `AlgebraicGeometry.ProEtale.lowerStarIterateFrobeniusIso_inv_app_comp_lowerStarComp_hom_app`:
  the two morphisms `g_* ⟶ (g ≫ F_X)_*` through `F_{X*} ≅ 𝟭` and through `F_{T*} ≅ 𝟭` agree.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

/-- The inverse of the comparison of base changes along equal morphisms `f = g` commutes with the
first projections. -/
@[reassoc (attr := simp)]
lemma CategoryTheory.MorphismProperty.Over.pullbackCongr_inv_app_left_fst
    {C : Type*} [Category C] {P Q : MorphismProperty C} [P.IsStableUnderBaseChange]
    [Q.IsStableUnderBaseChange] [Q.IsMultiplicative] [HasPullbacks C] {Y Z : C} {f g : Y ⟶ Z}
    (h : f = g)
    (A : P.Over Q Z) :
    ((MorphismProperty.Over.pullbackCongr h).inv.app A).left ≫ pullback.fst A.hom f =
      pullback.fst A.hom g := by
  subst h
  simp

/-- The inverse of the comparison of base changes along equal morphisms `f = g` commutes with the
second projections. -/
@[reassoc (attr := simp)]
lemma CategoryTheory.MorphismProperty.Over.pullbackCongr_inv_app_left_snd
    {C : Type*} [Category C] {P Q : MorphismProperty C} [P.IsStableUnderBaseChange]
    [Q.IsStableUnderBaseChange] [Q.IsMultiplicative] [HasPullbacks C] {Y Z : C} {f g : Y ⟶ Z}
    (h : f = g)
    (A : P.Over Q Z) :
    ((MorphismProperty.Over.pullbackCongr h).inv.app A).left ≫ pullback.snd A.hom f =
      pullback.snd A.hom g := by
  subst h
  simp

namespace AlgebraicGeometry

open Scheme

variable {T X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
  (hT : (p : Γ(T, ⊤)) = 0) (n : ℕ) (g : T ⟶ X)

namespace Scheme.ProEt

/-- The relative Frobenius maps are natural under base change along `g : T ⟶ X`: the relative
Frobenius of `V ×_X T` over `T`, read through `(V ×_X T) ×_{T, F_T} T ≅ V ×_{X, F_T ≫ g} T =
V ×_{X, g ≫ F_X} T ≅ (V ×_{X, F_X} X) ×_X T`, is the base change along `g` of the relative
Frobenius of `V` over `X`. -/
lemma overPullbackIterateFrobeniusIso_inv_app_naturality (V : X.ProEt) :
    (overPullbackIterateFrobeniusIso hp hT n).inv.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) ≫
      (MorphismProperty.Over.pullbackComp (T.iterateFrobenius hp hT n) g).inv.app V ≫
      (MorphismProperty.Over.pullbackCongr (comp_iterateFrobenius hp g hX hT n)).inv.app V ≫
      (MorphismProperty.Over.pullbackComp g (X.iterateFrobenius hp hX n)).hom.app V =
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
      ((overPullbackIterateFrobeniusIso hp hX n).inv.app V) := by
  ext : 1
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj,
        MorphismProperty.Comma.comp_hom, Comma.comp_left, Category.assoc,
        overPullbackIterateFrobeniusIso_inv_app_left,
        MorphismProperty.Over.pullbackComp_inv_app_left,
        MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
        MorphismProperty.Over.pullback_map_left, Category.id_comp]
      erw [pullbackLeftPullbackSndIso_inv_fst, MorphismProperty.Over.pullbackCongr_inv_app_left_fst
        (P := @WeaklyEtale) (Q := ⊤) (comp_iterateFrobenius hp g hX hT n) V,
        pullbackLeftPullbackSndIso_hom_fst, relativeIterateFrobenius_fst_assoc]
      erw [pullback.lift_fst_assoc, Category.assoc, relativeIterateFrobenius_fst]
      exact (comp_iterateFrobenius hp _ _ _ n).symm
    · simp only [Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj,
        MorphismProperty.Comma.comp_hom, Comma.comp_left, Category.assoc,
        overPullbackIterateFrobeniusIso_inv_app_left,
        MorphismProperty.Over.pullbackComp_inv_app_left,
        MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
        MorphismProperty.Over.pullback_map_left, Category.id_comp]
      erw [pullbackLeftPullbackSndIso_inv_fst_snd,
        MorphismProperty.Over.pullbackCongr_inv_app_left_snd_assoc
        (P := @WeaklyEtale) (Q := ⊤) (comp_iterateFrobenius hp g hX hT n) V,
        pullbackLeftPullbackSndIso_hom_snd_assoc, relativeIterateFrobenius_snd_assoc]
      erw [pullback.lift_fst_assoc, Category.assoc, relativeIterateFrobenius_snd]
      exact pullback.condition.symm
  · simp only [Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj,
      MorphismProperty.Comma.comp_hom, Comma.comp_left, Category.assoc,
      overPullbackIterateFrobeniusIso_inv_app_left,
      MorphismProperty.Over.pullbackComp_inv_app_left,
      MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
      MorphismProperty.Over.pullback_map_left, Category.id_comp]
    erw [pullbackLeftPullbackSndIso_inv_snd_snd,
      MorphismProperty.Over.pullbackCongr_inv_app_left_snd
      (P := @WeaklyEtale) (Q := ⊤) (comp_iterateFrobenius hp g hX hT n) V,
      pullbackLeftPullbackSndIso_hom_snd, relativeIterateFrobenius_snd, pullback.lift_snd]
    rfl

/-- The base change form of `AlgebraicGeometry.ProEtale.lowerStarIterateFrobeniusIso_naturality`,
with the inverses of the relative Frobenius maps: the two isomorphisms
`V ×_{X, g ≫ F_X} T ≅ V ×_X T` built from `g ≫ F_X = F_T ≫ g` agree. -/
lemma pullbackComp_hom_app_comp_map_overPullbackIterateFrobeniusIso_hom_app (V : X.ProEt) :
    (MorphismProperty.Over.pullbackComp g (X.iterateFrobenius hp hX n)).hom.app V ≫
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
          ((overPullbackIterateFrobeniusIso hp hX n).hom.app V) =
      (MorphismProperty.Over.pullbackCongr (comp_iterateFrobenius hp g hX hT n)).hom.app V ≫
        (MorphismProperty.Over.pullbackComp (T.iterateFrobenius hp hT n) g).hom.app V ≫
        (overPullbackIterateFrobeniusIso hp hT n).hom.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) := by
  rw [← cancel_epi ((overPullbackIterateFrobeniusIso hp hT n).inv.app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) ≫
    (MorphismProperty.Over.pullbackComp (T.iterateFrobenius hp hT n) g).inv.app V ≫
    (MorphismProperty.Over.pullbackCongr (comp_iterateFrobenius hp g hX hT n)).inv.app V)]
  simp only [Category.assoc]
  rw [reassoc_of% (overPullbackIterateFrobeniusIso_inv_app_naturality hp hX hT n g V),
    ← Functor.map_comp, Iso.inv_hom_id_app]
  simp

end Scheme.ProEt

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A]

/-- The pushforward form of the naturality of the Frobenius trivializations `F_* ≅ 𝟭` under
pushforward along `g : T ⟶ X`, with `g ≫ F_X = F_T ≫ g`: the two morphisms
`g_* ⟶ (g ≫ F_X)_*` through `F_{X*} ≅ 𝟭` and through `F_{T*} ≅ 𝟭` agree. -/
lemma lowerStarIterateFrobeniusIso_inv_app_comp_lowerStarComp_hom_app
    (G : Sheaf (ProEt.topology T) A) :
    (lowerStarIterateFrobeniusIso A hp hX n).inv.app ((g)_*[A].obj G) ≫
        (lowerStarComp A g (X.iterateFrobenius hp hX n)).hom.app G =
      (g)_*[A].map ((lowerStarIterateFrobeniusIso A hp hT n).inv.app G) ≫
        (lowerStarComp A (T.iterateFrobenius hp hT n) g).hom.app G ≫
        (lowerStarCongr A (comp_iterateFrobenius hp g hX hT n)).inv.app G := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ?_))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStarComp_hom_app_hom_app, lowerStarIterateFrobeniusIso_inv_app_hom_app,
    lowerStar_obj_obj_map', lowerStarCongr_inv_app_hom_app, lowerStar_map_hom_app',
    Quiver.Hom.unop_op, ← Functor.map_comp, ← op_comp]
  rw [ProEt.pullbackComp_hom_app_comp_map_overPullbackIterateFrobeniusIso_hom_app hp hX hT,
    Category.assoc]

end ProEtale

end AlgebraicGeometry
