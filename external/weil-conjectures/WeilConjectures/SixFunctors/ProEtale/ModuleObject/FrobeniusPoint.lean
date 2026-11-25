/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.AbsoluteFrobeniusLocallyConstant
public import WeilConjectures.SixFunctors.ProEtale.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!
# The Frobenius trivialization on sheaves pulled back from the point

Let `X` be a scheme in which the prime `p` vanishes, `F = F_X` its `p ^ n`-power absolute
Frobenius and `π_X : X ⟶ Spec ℤ` its structure morphism. On pro-étale abelian sheaves pulled
back from the condensed point, `p_X^* H = π_X^* p^* H`, there are two isomorphisms
`F^* p_X^* H ≅ p_X^* H`: the trivialization `F^* ≅ 𝟭` given by the relative Frobenius
isomorphisms (`AlgebraicGeometry.ProEtale.upperStarIterateFrobeniusIso`), and the canonical
comparison `F^* π_X^* ≅ (F ≫ π_X)^* = π_X^*`
(`AlgebraicGeometry.ProEtale.upperStarFromPointComp`). This file shows that they agree.

Both are conjugate, under the adjunctions `p^* ⊣ p_*` and `g^* ⊣ g_*`, to morphisms of
pushforwards, whose components at a profinite set `S` are restriction maps along two morphisms
`X[S] ×_{X, F} X ⟶ X[S]`, where `X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X`. These morphisms agree: the
inverse of the relative Frobenius `r = (F_{X[S]}, pr_X)` is the canonical isomorphism, since
the absolute Frobenius of `X[S]` does not change the projection to `Spec LC(S, ℤ)`
(`AlgebraicGeometry.Scheme.iterateFrobenius_comp_locallyConstant`, Fermat's little theorem).

## Main results

- `AlgebraicGeometry.ProEtale.upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint`: the
  trivialization `F^* ≅ 𝟭` agrees with `upperStarFromPointComp F` on sheaves pulled back from
  the point.
- `AlgebraicGeometry.ProEtale.whiskerLeft_upperStarFromPoint_upperStarIterateFrobeniusIso_hom`:
  the same statement as an equality of natural transformations.
- `AlgebraicGeometry.Scheme.ProEt.overPullbackIterateFrobeniusIso_hom_app_profiniteToProEtOf`:
  the site-level statement, on the test objects `X[S]`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)

namespace Scheme.ProEt

open ProEtale in
/-- On the profinite test object `X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X`, the inverse of the relative
Frobenius `X[S] ≅ X[S] ×_{X, F_X} X` is the canonical isomorphism
`X[S] ×_{X, F_X} X ≅ Spec LC(S, ℤ) ×_{Spec ℤ, F_X ≫ π_X} X = X[S]`. -/
lemma overPullbackIterateFrobeniusIso_hom_app_profiniteToProEtOf (S : Profinite.{u}) :
    (overPullbackIterateFrobeniusIso hp hX n).hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).obj
          (profiniteToProEt.obj S)) =
      (MorphismProperty.Over.pullbackComp (X.iterateFrobenius hp hX n) (toSpecZ X)).inv.app
          (profiniteToProEt.obj S) ≫
        (MorphismProperty.Over.pullbackCongr
          (comp_toSpecZ (X.iterateFrobenius hp hX n))).hom.app (profiniteToProEt.obj S) := by
  rw [← cancel_epi ((overPullbackIterateFrobeniusIso hp hX n).inv.app _), Iso.inv_hom_id_app]
  ext : 1
  apply pullback.hom_ext
  · symm
    simp only [Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj,
      MorphismProperty.Comma.comp_hom, Comma.comp_left, Category.assoc,
      overPullbackIterateFrobeniusIso_inv_app_left,
      MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id,
      MorphismProperty.Over.pullbackCongr_hom_app_left_fst, Category.id_comp,
      pullbackLeftPullbackSndIso_hom_fst, MorphismProperty.Comma.id_hom, Comma.id_left]
    erw [relativeIterateFrobenius_fst_assoc]
    exact iterateFrobenius_comp_locallyConstant hp n _ _
  · symm
    simp only [Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj,
      MorphismProperty.Comma.comp_hom, Comma.comp_left, Category.assoc,
      overPullbackIterateFrobeniusIso_inv_app_left,
      MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id,
      MorphismProperty.Over.pullbackCongr_hom_app_left_snd, Category.id_comp,
      pullbackLeftPullbackSndIso_hom_snd, MorphismProperty.Comma.id_hom, Comma.id_left]
    erw [relativeIterateFrobenius_snd]
    rfl

end Scheme.ProEt

namespace ProEtale

section Coefficients

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the inverse of the trivialization `F_{X*} ≅ 𝟭` are the restriction maps
along the inverses of the relative Frobenius maps. -/
lemma lowerStarIterateFrobeniusIso_inv_app_hom_app (G : Sheaf (ProEt.topology X) A)
    (V : X.ProEtᵒᵖ) :
    ((lowerStarIterateFrobeniusIso A hp hX n).inv.app G).hom.app V =
      G.obj.map ((ProEt.overPullbackIterateFrobeniusIso hp hX n).hom.app V.unop).op := by
  simp [lowerStarIterateFrobeniusIso]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the inverse of `g_* ≅ g'_*` for `g = g'` are the restriction maps along
the canonical isomorphisms `V ×_{Y,g} Z ≅ V ×_{Y,g'} Z`. -/
lemma lowerStarCongr_inv_app_hom_app {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (G : Sheaf (ProEt.topology Z) A) (V : Y.ProEtᵒᵖ) :
    ((lowerStarCongr A h).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackCongr h).hom.app V.unop).op := by
  subst h
  simp
  rfl

/-- `ProEtale.upperStarCongr` is the `eqToHom` of the equality of the pullbacks. -/
lemma upperStarCongr_hom_eq_eqToHom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (upperStarCongr A h).hom = eqToHom (congrArg (upperStar A) h) := by
  subst h
  rfl

/-- The conjugate of the trivialization `F_X^* ≅ 𝟭`, whiskered by a pullback `t^*`, is the
inverse of the trivialization `F_{X*} ≅ 𝟭` whiskered by `t_*`. -/
lemma conjugateEquiv_whiskerLeft_upperStarIterateFrobeniusIso_hom {W : Scheme.{u}}
    (t : X ⟶ W) :
    conjugateEquiv (upperStarLowerStarAdjunction A t)
        ((upperStarLowerStarAdjunction A t).comp
          (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n)))
        (Functor.whiskerLeft (t)^*[A] (upperStarIterateFrobeniusIso A hp hX n).hom ≫
          (Functor.rightUnitor _).hom) =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (lowerStarIterateFrobeniusIso A hp hX n).inv (t)_*[A] := by
  rw [← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A t).comp Adjunction.id),
    conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft]
  congr 2
  simpa using congrArg Iso.hom (conjugateIsoEquiv_upperStarIterateFrobeniusIso A hp hX n)

/-- For `f ≫ t = g`, the comparison `t^* ⋙ f^* ≅ (f ≫ t)^* = g^*` is conjugate to the
comparison `g_* = (f ≫ t)_* ≅ f_* ⋙ t_*` of the pushforwards. -/
lemma conjugateEquiv_upperStarComp_inv_comp_upperStarCongr_hom {Y W : Scheme.{u}} (f : X ⟶ Y)
    (t : Y ⟶ W) (g : X ⟶ W) (h : f ≫ t = g) :
    conjugateEquiv (upperStarLowerStarAdjunction A g)
        ((upperStarLowerStarAdjunction A t).comp (upperStarLowerStarAdjunction A f))
        ((upperStarComp A f t).inv ≫ (upperStarCongr A h).hom) =
      (lowerStarCongr A h).inv ≫ (lowerStarComp A f t).inv := by
  rw [← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (f ≫ t))]
  congr 1
  · simpa using congrArg Iso.hom (conjugateIsoEquiv_upperStarCongr A h)
  · simpa using congrArg Iso.inv (conjugateIsoEquiv_upperStarComp A f t)

end Coefficients

/-- The sections of `p_* G` over a profinite set `S` are those of `G` over `Spec LC(S, ℤ)`,
also on morphisms. -/
lemma pointLowerStar_map_hom_app {G G' : Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1}}
    (φ : G ⟶ G') (S : Profinite.{u}ᵒᵖ) :
    (pointLowerStar.map φ).hom.app S = φ.hom.app (op (profiniteToProEt.obj S.unop)) :=
  rfl

/-- The components of `upperStarFromPointComp f : f^* p_Y^* ≅ p_X^*` are those of the
composition isomorphism `f^* π_Y^* ≅ (f ≫ π_Y)^*` followed by `f ≫ π_Y = π_X`. -/
lemma upperStarFromPointComp_hom_app {Y : Scheme.{u}} (f : X ⟶ Y)
    (H : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (upperStarFromPointComp f).hom.app H =
      (upperStarComp Ab.{u + 1} f (toSpecZ Y)).inv.app (pointUpperStar.obj H) ≫
        (upperStarCongr Ab.{u + 1} (comp_toSpecZ f)).hom.app (pointUpperStar.obj H) := by
  rw [upperStarCongr_hom_eq_eqToHom]
  have h : upperStarFromPointComp f =
      Functor.associator pointUpperStar (toSpecZ Y)^*[Ab.{u + 1}] (f)^*[Ab.{u + 1}] ≪≫
        Functor.isoWhiskerLeft pointUpperStar ((upperStarComp Ab.{u + 1} f (toSpecZ Y)).symm ≪≫
          eqToIso (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f))) := by
    unfold upperStarFromPointComp
    rfl
  rw [h]
  exact associator_isoWhiskerLeft_upperStarComp_hom_app Ab.{u + 1} pointUpperStar f _ _
    (comp_toSpecZ f) H

/-- The trivialization `F_X^* ≅ 𝟭` and the comparison `F_X^* π_X^* ≅ (F_X ≫ π_X)^* = π_X^*`
agree after precomposition with `p^*`. Their conjugates are restriction maps along the two
morphisms `X[S] ×_{X, F_X} X ⟶ X[S]` compared in
`AlgebraicGeometry.Scheme.ProEt.overPullbackIterateFrobeniusIso_hom_app_profiniteToProEtOf`. -/
lemma whiskerLeft_pointUpperStar_upperStarIterateFrobeniusIso_hom :
    Functor.whiskerLeft pointUpperStar
        (Functor.whiskerLeft (toSpecZ X)^*[Ab.{u + 1}]
          (upperStarIterateFrobeniusIso Ab.{u + 1} hp hX n).hom ≫ (Functor.rightUnitor _).hom) =
      Functor.whiskerLeft pointUpperStar
        ((upperStarComp Ab.{u + 1} (X.iterateFrobenius hp hX n) (toSpecZ X)).inv ≫
          (upperStarCongr Ab.{u + 1} (comp_toSpecZ (X.iterateFrobenius hp hX n))).hom) := by
  apply (conjugateEquiv (pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)))
    (pointUpperStarLowerStarAdjunction.comp
      ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (X.iterateFrobenius hp hX n))))).injective
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerLeft_upperStarIterateFrobeniusIso_hom,
    conjugateEquiv_upperStarComp_inv_comp_upperStarCongr_hom]
  refine NatTrans.ext (funext fun G ↦ Sheaf.hom_ext (NatTrans.ext (funext fun S ↦ ?_)))
  rw [Functor.whiskerRight_app, Functor.whiskerRight_app, pointLowerStar_map_hom_app,
    pointLowerStar_map_hom_app]
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.whiskerRight_app, lowerStar_map_hom_app',
    lowerStarIterateFrobeniusIso_inv_app_hom_app, lowerStarCongr_inv_app_hom_app,
    lowerStarComp_inv_app_hom_app, Functor.leftUnitor_inv_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  erw [Category.id_comp]
  rw [← Functor.map_comp, ← op_comp,
    ProEt.overPullbackIterateFrobeniusIso_hom_app_profiniteToProEtOf]

/-- On sheaves `p_X^* H` pulled back from the condensed point, the trivialization
`F_X^* ≅ 𝟭` of the pullback along the absolute Frobenius is the canonical comparison
`F_X^* p_X^* ≅ p_X^*` (`AlgebraicGeometry.ProEtale.upperStarFromPointComp`). -/
theorem upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint
    (H : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (upperStarIterateFrobeniusIso Ab.{u + 1} hp hX n).hom.app ((upperStarFromPoint X).obj H) =
      (upperStarFromPointComp (X.iterateFrobenius hp hX n)).hom.app H := by
  have h := congr_app (whiskerLeft_pointUpperStar_upperStarIterateFrobeniusIso_hom hp hX n) H
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.rightUnitor_hom_app] at h
  rw [upperStarFromPointComp_hom_app, ← h]
  exact (Category.comp_id _).symm

/-- The trivialization `F_X^* ≅ 𝟭`, restricted to sheaves pulled back from the condensed point,
is the canonical comparison `F_X^* p_X^* ≅ p_X^*`. -/
theorem whiskerLeft_upperStarFromPoint_upperStarIterateFrobeniusIso_hom :
    Functor.whiskerLeft (upperStarFromPoint X)
        (upperStarIterateFrobeniusIso Ab.{u + 1} hp hX n).hom =
      (upperStarFromPointComp (X.iterateFrobenius hp hX n)).hom := by
  refine NatTrans.ext (funext fun H ↦ ?_)
  exact upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint hp hX n H

end ProEtale

end AlgebraicGeometry
