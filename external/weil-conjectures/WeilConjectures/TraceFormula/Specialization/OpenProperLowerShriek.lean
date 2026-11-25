/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteClosedExtension
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF
public import WeilConjectures.TraceFormula.Specialization.OpenProperLowerShriekAbstract

/-!

# The lower shriek of an open immersion followed by a proper morphism

Let `ι₃ : Y ⟶ X₃` and `ι₁ : Y ⟶ X₁` be open immersions and `p : X₃ ⟶ X₁` a proper morphism with
`ι₃ ≫ p = ι₁`, such that `Y` is the inverse image of itself, `Y = X₃ ×_{X₁} Y` (a refinement of
compactifications). The identifications of the lower shrieks give an isomorphism
```
E : ι₁! ≅ Rι₁_! ≅ Rι₃_! ⋙ Rp_! ≅ ι₃! ⋙ Rp_*
```
(`ProEtale.CondensedRing.openProperLowerShriekIso`). This file proves:

* `ProEtale.CondensedRing.unit_comp_upperStarComp_comp_map_openProperLowerShriekIso`: the adjoint
  `E♭ : Lp^* ι₁! ⟶ ι₃!` of `E` is the inverse of the extension-by-zero base change of the cartesian
  square, in the form: `η_{ι₁} ≫ (Lι₁^* ≅ Lι₃^* Lp^*) ≫ Lι₃^*(E♭) = η_{ι₃}`;
* `ProEtale.CondensedRing.isIso_map_openProperLowerShriekIso_comp_counit`: `E♭` is invertible;
* `ProEtale.CondensedRing.compactificationLowerShriekIso_hom_app_comp_map_openProperLowerShriekIso`:
  for a proper `a₁ : X₁ ⟶ S`, the factorizations `Rf_! ≅ ι₁! ⋙ Ra₁_*` and
  `Rf_! ≅ ι₃! ⋙ R(p ≫ a₁)_*` of the lower shriek (`compactificationLowerShriekIso`) are related
  by `E`.

They are the inputs of the refinement step of the independence of the compact-support exchange
of nearby cycles from the compactification (blueprint `prose-E-15`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

attribute [local instance] isOpenImmersion_over_id_left isProper_over_id_left

/-- A commutative square in `Over S` is a pullback square if the underlying square of schemes
is. -/
lemma isPullback_of_isPullback_left {S : Scheme.{u}} {P X Y Z : Over S} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : IsPullback fst.left snd.left f.left g.left) : IsPullback fst snd f g :=
  IsPullback.of_map (Over.forget S) w h

section Identity

variable {B C P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- The pullback comparison of the square `g ≫ h = 𝟙 ≫ (g ≫ h)` is `L(𝟙)^* ≅ 𝟭` followed by
`L(g ≫ h)^* ≅ Lg^* Lh^*`. -/
lemma pullbackSquareComparison_flip_hom_app (g : B ⟶ C) (h : C ⟶ P)
    (sq : CommSq g (𝟙 B) h (g ≫ h)) (Z : Dᵇc(P.left)⟦Λℓ⟧) :
    (boundedConstructiblePullbackSquareComparison Λℓ ℓ sq).hom.app Z =
      (boundedConstructibleUpperStarId Λℓ ℓ B).hom.app
          ((boundedConstructibleUpperStar Λℓ ℓ (g ≫ h)).obj Z) ≫
        (boundedConstructibleUpperStarComp Λℓ ℓ g h).hom.app Z := by
  rw [boundedConstructiblePullbackSquareComparison_hom_app,
    ← cancel_epi ((boundedConstructibleUpperStarComp Λℓ ℓ (𝟙 B) (g ≫ h)).hom.app Z),
    Iso.hom_inv_id_app_assoc, reassoc_of% boundedConstructibleUpperStarComp_id_left_app]

/-- The composition isomorphism of the square `𝟙 ≫ (g ≫ h) = g ≫ h` is `R(g ≫ h)_!(R(𝟙)_! ≅ 𝟭)`
followed by `R(g ≫ h)_! ≅ Rg_! Rh_!`. -/
lemma lowerShriekSquareIso_id_hom_app (g : B ⟶ C) (h : C ⟶ P)
    (w : 𝟙 B ≫ (g ≫ h) = g ≫ h) (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app N =
      (boundedConstructibleLowerShriek ℓ (g ≫ h)).map
          ((boundedConstructibleLowerShriekId ℓ B).hom.app N) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).hom.app N := by
  simp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, boundedConstructibleLowerShriekId,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 B) (g ≫ h)).hom.app N),
    Iso.hom_inv_id_app_assoc, reassoc_of% boundedConstructibleLowerShriekComp_padicAlgCl_id_left]

variable (B) in
/-- The counit of `L(𝟙)^* ⊣ R(𝟙)_!` is trivialized by `L(𝟙)^* ≅ 𝟭` and `R(𝟙)_! ≅ 𝟭`. -/
lemma upperStarLowerShriekAdjunction_id_counit_app (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (𝟙 B)).counit.app N =
      (boundedConstructibleUpperStarId Λℓ ℓ B).hom.app
          ((boundedConstructibleLowerShriek ℓ (𝟙 B)).obj N) ≫
        (boundedConstructibleLowerShriekId ℓ B).hom.app N := by
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app, Iso.symm_inv,
    boundedConstructibleLowerShriekId, Iso.trans_hom, boundedConstructibleLowerStarId_hom_app]
  have n := (boundedConstructibleUpperStarId Λℓ ℓ B).hom.naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 B)).hom.app N)
  simp only [Functor.id_map] at n
  rw [← reassoc_of% n, Iso.hom_inv_id_app_assoc]

end Identity

variable {Y X₃ X₁ : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  (ι₃ : Y ⟶ X₃) (p : X₃ ⟶ X₁) (ι₁ : Y ⟶ X₁) [IsOpenImmersion ι₃.left] [IsProper p.left]
  [IsOpenImmersion ι₁.left]

/-- The isomorphism `ι₁! ≅ Rι₁_! ≅ Rι₃_! ⋙ Rp_! ≅ ι₃! ⋙ Rp_*` for `ι₃ ≫ p = ι₁`, with `ι₁`, `ι₃`
open immersions and `p` proper. -/
noncomputable def openProperLowerShriekIso (w : ι₃ ≫ p = ι₁) :
    boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ ι₁ ≅
      boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ ι₃ ⋙ boundedConstructibleLowerStar ℓ p :=
  (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι₁).symm ≪≫
    lowerShriekCompOfEq ℓ ι₃ p w ≪≫
    Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl
      ℓ ι₃) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p)

/-- The components of `openProperLowerShriekIso` for `ι₁ = ι₃ ≫ p`:
`ι₁! ≅ Rι₁_! ≅ Rp_! Rι₃_! ≅ Rp_! ι₃! ≅ Rp_* ι₃!`. -/
lemma openProperLowerShriekIso_hom_app_rfl [IsOpenImmersion (ι₃ ≫ p).left]
    (K : Dᵇc(Y.left)⟦Λℓ⟧) :
    (openProperLowerShriekIso ℓ ι₃ p (ι₃ ≫ p) rfl).hom.app K =
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (ι₃ ≫ p)).inv.app K ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ ι₃ p).hom.app K ≫
        (boundedConstructibleLowerShriek ℓ p).map
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι₃).hom.app K) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ ι₃).obj K) := by
  simp [openProperLowerShriekIso]

/-- **The adjoint of `E` inverts the extension-by-zero base change**, on `Dᵇc`: for the cartesian
square `𝟙 ≫ (ι₃ ≫ p) = ι₃ ≫ p`, the extension-by-zero base change `L(𝟙)^* ι₃! ⟶ Lp^* ι₁!`
followed by `E♭ = Lp^*(E) ≫ ε_p` is `ι₃!(L(𝟙)^* ≅ 𝟭)`. -/
theorem openImmersionLowerShriekBaseChange'_app_comp_map_openProperLowerShriekIso
    [IsOpenImmersion (ι₃ ≫ p).left] (sq : IsPullback (𝟙 Y) ι₃ (ι₃ ≫ p) p)
    (K : Dᵇc(Y.left)⟦Λℓ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λℓ ℓ sq.toCommSq).app K ≫
        (boundedConstructibleUpperStar Λℓ ℓ p).map
          ((openProperLowerShriekIso ℓ ι₃ p _ rfl).hom.app K) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).counit.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ ι₃).obj K) =
      (boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ ι₃).map
        ((boundedConstructibleUpperStarId Λℓ ℓ Y).hom.app K) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have hO := boundedConstructibleLowerShriekBaseChange_padicAlgCl_comp_isoOpen ℓ sq
  rw [openProperLowerShriekIso_hom_app_rfl]
  exact baseChange_comp_map_comp_counit_eq_map
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (𝟙 Y))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ p)
    (boundedConstructibleLowerShriekId ℓ Y) (boundedConstructibleUpperStarId Λℓ ℓ Y)
    (upperStarLowerShriekAdjunction_id_counit_app ℓ Y)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (ι₃ ≫ p))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι₃)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ ι₃ p)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ sq.w).hom
    (lowerShriekSquareIso_id_hom_app ℓ ι₃ p sq.w)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ sq)
    (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λℓ ℓ sq.toCommSq)
    (fun K ↦ by simpa using congr_app hO K) K

/-- **The unit identity of the adjoint of `E`**, on `Dᵇc`: the unit of `ι₁! ⊣ Lι₁^*`, followed by
`Lι₁^* ≅ Lι₃^* Lp^*` and `Lι₃^*(Lp^*(E) ≫ ε_p)`, is the unit of `ι₃! ⊣ Lι₃^*`. -/
theorem unit_comp_upperStarComp_comp_map_openProperLowerShriekIso_bdc
    [IsOpenImmersion (ι₃ ≫ p).left] (sq : IsPullback (𝟙 Y) ι₃ (ι₃ ≫ p) p)
    (K : Dᵇc(Y.left)⟦Λℓ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ (ι₃ ≫ p)).unit.app K ≫
        (boundedConstructibleUpperStarComp Λℓ ℓ ι₃ p).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ (ι₃ ≫ p)).obj K) ≫
        (boundedConstructibleUpperStar Λℓ ℓ ι₃).map
          ((boundedConstructibleUpperStar Λℓ ℓ p).map
            ((openProperLowerShriekIso ℓ ι₃ p _ rfl).hom.app K) ≫
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).counit.app
            ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ ι₃).obj K)) =
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ ι₃).unit.app K :=
  unit_comp_map_eq_unit_of_exchangeLeft
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ (ι₃ ≫ p))
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ ι₃)
    (boundedConstructibleUpperStarId Λℓ ℓ Y) (boundedConstructibleUpperStarComp Λℓ ℓ ι₃ p)
    (boundedConstructiblePullbackSquareComparison Λℓ ℓ sq.toCommSq.flip)
    (pullbackSquareComparison_flip_hom_app ℓ ι₃ p sq.toCommSq.flip)
    (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λℓ ℓ sq.toCommSq)
    (boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft Λℓ ℓ sq.toCommSq) K _
    (openImmersionLowerShriekBaseChange'_app_comp_map_openProperLowerShriekIso ℓ ι₃ p sq K)

/-- **The adjoint of `E : ι₁! ≅ ι₃! ⋙ Rp_*` is the inverse of the extension-by-zero base change**
of the cartesian square `Y = X₃ ×_{X₁} Y`, on the ambient derived categories: the unit of
`ι₁! ⊣ Lι₁^*`, followed by `Lι₁^* ≅ Lι₃^* Lp^*` and `Lι₃^*` of the adjoint
`Lp^*(E) ≫ ε_p : Lp^* ι₁! ⟶ ι₃!`, is the unit of `ι₃! ⊣ Lι₃^*`. -/
theorem unit_comp_upperStarComp_comp_map_openProperLowerShriekIso (w : ι₃ ≫ p = ι₁)
    (sq : IsPullback ι₃.left (𝟙 Y.left) p.left ι₁.left) (K : Dᵇc(Y.left)⟦Λℓ⟧) :
    (openImmersionAdjunction ℓ ι₁.left).unit.app K.obj ≫
        (leftDerivedUpperStarCompOfEq Λℓ (congrArg CommaMorphism.left w)).hom.app
          (D((ι₁.left)_!open⟦Λℓ⟧).obj K.obj) ≫
        L((ι₃.left)^*⟦Λℓ⟧).map
          (L((p.left)^*⟦Λℓ⟧).map ((openProperLowerShriekIso ℓ ι₃ p ι₁ w).hom.app K).hom ≫
            (derivedUpperStarLowerStarAdjunction Λℓ p.left).counit.app
              (D((ι₃.left)_!open⟦Λℓ⟧).obj K.obj)) =
      (openImmersionAdjunction ℓ ι₃.left).unit.app K.obj := by
  subst w
  have h := congrArg (fun x ↦ x.hom)
    (unit_comp_upperStarComp_comp_map_openProperLowerShriekIso_bdc ℓ ι₃ p
      (isPullback_of_isPullback_left (by simp) sq.flip) K)
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    openImmersionLowerShriekUpperStarAdjunction_unit_app_hom, boundedConstructibleUpperStar_map_hom,
    boundedConstructibleUpperStarComp_hom_app_hom,
    boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom] at h
  exact h

/-- The adjoint `Lp^*(E) ≫ ε_p : Lp^* ι₁! ⟶ ι₃!` of `E : ι₁! ≅ ι₃! ⋙ Rp_*` is an isomorphism (it is
the inverse of the extension-by-zero base change of the cartesian square `Y = X₃ ×_{X₁} Y`). -/
theorem isIso_map_openProperLowerShriekIso_comp_counit (w : ι₃ ≫ p = ι₁)
    (sq : IsPullback ι₃.left (𝟙 Y.left) p.left ι₁.left) (K : Dᵇc(Y.left)⟦Λℓ⟧) :
    IsIso (L((p.left)^*⟦Λℓ⟧).map ((openProperLowerShriekIso ℓ ι₃ p ι₁ w).hom.app K).hom ≫
      (derivedUpperStarLowerStarAdjunction Λℓ p.left).counit.app
        (D((ι₃.left)_!open⟦Λℓ⟧).obj K.obj)) := by
  subst w
  have sq' : IsPullback (𝟙 Y) ι₃ (ι₃ ≫ p) p := isPullback_of_isPullback_left (by simp) sq.flip
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' Λℓ ℓ sq'
  have h := openImmersionLowerShriekBaseChange'_app_comp_map_openProperLowerShriekIso ℓ ι₃ p sq' K
  rw [← IsIso.eq_inv_comp] at h
  have : IsIso ((boundedConstructibleUpperStar Λℓ ℓ p).map
      ((openProperLowerShriekIso ℓ ι₃ p _ rfl).hom.app K) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).counit.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ ι₃).obj K)) := by
    rw [h]
    infer_instance
  have hψ := (ObjectProperty.ι _).map_isIso ((boundedConstructibleUpperStar Λℓ ℓ p).map
      ((openProperLowerShriekIso ℓ ι₃ p _ rfl).hom.app K) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).counit.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ ι₃).obj K))
  simp only [boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom,
    ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleUpperStar_map_hom] at hψ
  exact hψ

/-- **The factorizations of `Rf_!` through `ι₁` and `ι₃` are related by `E`**: for a proper
`a₁ : X₁ ⟶ S` and `a₃ = p ≫ a₁`, the factorization `Rf_! ≅ ι₁! ⋙ Ra₁_*`
(`compactificationLowerShriekIso`) followed by `Ra₁_*(E)` and `Rp_* ⋙ Ra₁_* ≅ Ra₃_*` is the
factorization `Rf_! ≅ ι₃! ⋙ Ra₃_*`. -/
theorem compactificationLowerShriekIso_hom_app_comp_map_openProperLowerShriekIso
    {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsSeparated S.hom] {f : Y ⟶ S} (a₁ : X₁ ⟶ S) (a₃ : X₃ ⟶ S) [IsProper a₁.left]
    [IsProper a₃.left] (w : ι₃ ≫ p = ι₁) (wa : p ≫ a₁ = a₃) (w₁ : ι₁ ≫ a₁ = f)
    (w₃ : ι₃ ≫ a₃ = f) (K : Dᵇc(Y.left)⟦Λℓ⟧) :
    (compactificationLowerShriekIso ℓ ι₁ a₁ w₁).hom.app K ≫
        (boundedConstructibleLowerStar ℓ a₁).map
          ((openProperLowerShriekIso ℓ ι₃ p ι₁ w).hom.app K) ≫
        (boundedConstructibleLowerStarCompOfEq ℓ p a₁ wa).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ ι₃).obj K) =
      (compactificationLowerShriekIso ℓ ι₃ a₃ w₃).hom.app K := by
  subst w wa
  simp only [compactificationLowerShriekIso, openProperLowerShriekIso, lowerShriekCompOfEq,
    boundedConstructibleLowerStarCompOfEq, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc, Functor.map_comp, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id, eqToHom_app]
  have n₁ := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a₁).hom.naturality
    ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (ι₃ ≫ p)).inv.app K ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ ι₃ p).hom.app K ≫
      (boundedConstructibleLowerShriek ℓ p).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι₃).hom.app K))
  simp only [Functor.map_comp, Category.assoc] at n₁
  rw [← reassoc_of% n₁, ← Functor.map_comp_assoc (boundedConstructibleLowerShriek ℓ a₁)
    ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (ι₃ ≫ p)).hom.app K)]
  simp only [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have n₂ := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ p a₁).inv.naturality
    ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι₃).hom.app K)
  simp only [Functor.comp_map] at n₂
  simp only [isoLowerStar_hom_app_comp_map_comp_lowerStarComp_hom ℓ p a₁, reassoc_of% n₂,
    reassoc_of% (boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ ι₃ p a₁ K),
    Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
