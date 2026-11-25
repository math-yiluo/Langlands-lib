/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition

/-!
# Composition of the transition maps of the base-change map

The transition maps between the targets of the derived base-change maps over `T` and over
`T'` compose, and along a universal homeomorphism they are isomorphisms. As a consequence,
whether a cokernel element lies in the image of the base-change map does not change along a
universal homeomorphism of the base.

## Main definitions

- `AlgebraicGeometry.Etale.targetTransitionPlus`: the derived transition map between the
  targets of the derived base-change maps.

## Main statements

- `AlgebraicGeometry.Etale.targetTransitionPlus_comp`: the transition maps compose.
- `AlgebraicGeometry.Etale.isIso_targetTransitionPlus`: along a universal homeomorphism the
  transition map is an isomorphism.
- `AlgebraicGeometry.Etale.mem_range_iff_of_isUniversalHomeomorphism`: membership in the image
  of the base-change map is invariant under universal homeomorphisms of the base.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section TransitionComposition

/-- The transition maps `AlgebraicGeometry.Etale.lowerStarPlusTransition` are natural in the
complex. -/
lemma Etale.lowerStarPlusTransition_naturality {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    (h : Y ⟶ X) (h' : Y' ⟶ X) (w : a ≫ h = h')
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ K') :
    R+((h)_*[ModuleCat.{u + 1} Λ]).map f ≫ Etale.lowerStarPlusTransition Λ a h h' w K' =
      Etale.lowerStarPlusTransition Λ a h h' w K ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map (D+((a)^*[ModuleCat.{u + 1} Λ]).map f) := by
  have sq : CommSq a h' h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' w sq,
    Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' w sq]
  have hn := (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.naturality
    (R+((h)_*[ModuleCat.{u + 1} Λ]).map f)
  have hb := (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).naturality f
  simp only [Functor.id_map, Functor.comp_map] at hn hb
  rw [reassoc_of% hn, hb, Category.assoc]

/-- The transition maps `AlgebraicGeometry.Etale.lowerStarPlusTransition` compose: along
`a₁ : Y₁ ⟶ Y₂` and `a₂ : Y₂ ⟶ Y`, the composite of the two transition maps, followed by the
composition isomorphism of the pullbacks, is the transition map along `a₁ ≫ a₂`. Both sides are
derived base-change maps of degenerate squares, which paste horizontally. -/
lemma Etale.lowerStarPlusTransition_comp {X Y Y₂ Y₁ : Scheme.{u}} (a₂ : Y₂ ⟶ Y)
    (a₁ : Y₁ ⟶ Y₂) (a : Y₁ ⟶ Y) (ha : a₁ ≫ a₂ = a) (h : Y ⟶ X) (h₂ : Y₂ ⟶ X) (h₁ : Y₁ ⟶ X)
    (w₂ : a₂ ≫ h = h₂) (w₁ : a₁ ≫ h₂ = h₁) (w : a ≫ h = h₁)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.lowerStarPlusTransition Λ a₂ h h₂ w₂ K ≫
        Etale.lowerStarPlusTransition Λ a₁ h₂ h₁ w₁ (D+((a₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).inv.app K) =
      Etale.lowerStarPlusTransition Λ a h h₁ w K := by
  have sq₂ : CommSq a₂ h₂ h (𝟙 X) := ⟨by rw [w₂, Category.comp_id]⟩
  have sq₁ : CommSq a₁ h₁ h₂ (𝟙 X) := ⟨by rw [w₁, Category.comp_id]⟩
  have sq : CommSq a h₁ h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a₂ h h₂ w₂ sq₂,
    Etale.lowerStarPlusTransition_eq_baseChange Λ a₁ h₂ h₁ w₁ sq₁,
    Etale.lowerStarPlusTransition_eq_baseChange Λ a h h₁ w sq,
    Etale.baseChange_app_paste_horiz_of_eq Λ sq₂ sq₁ sq ha (Category.comp_id _) K]
  have hn := (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.naturality
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₂).app K)
  have hn' := (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.naturality
    ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app
      (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))
  have hc := Etale.upperStarCompDerivedPlus_id_right_inv_app (ModuleCat.{u + 1} Λ) (𝟙 X)
    (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)
  have hC : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.comp_id _).symm).hom.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) =
      D+((𝟙 X)^*[ModuleCat.{u + 1} Λ]).map ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ)
        X).inv.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)) := by
    rw [← cancel_mono ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.comp_id _).symm).inv.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)),
      Iso.hom_inv_id_app, hc]
    rfl
  simp only [Functor.id_map, Functor.id_obj] at hn hn'
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hn', hC]

/-- The derived base-change map of the degenerate square with sides `a`, `h'`, `h` and `𝟙 X` is
an isomorphism when `a` is a universal homeomorphism. The square is the vertical pasting of the
square with sides `a`, `a`, `𝟙 Y` and `𝟙 Y`, whose pushforwards are exact (`a_*` is an
equivalence) and whose underived base-change map is an isomorphism, with an identity square. -/
lemma Etale.isIso_baseChange_app_of_isUniversalHomeomorphism {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    [IsUniversalHomeomorphism a] (h : Y ⟶ X) (h' : Y' ⟶ X) (sq : CommSq a h' h (𝟙 X))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) := by
  have key : ∀ (f₀ : Y ⟶ X) (hf : 𝟙 Y ≫ h = f₀) (sq : CommSq a h' f₀ (𝟙 X)),
      IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq) := by
    rintro _ rfl sq
    have sq₁ : CommSq a a (𝟙 Y) (𝟙 Y) := ⟨by simp⟩
    have sq₂ : CommSq (𝟙 Y) h h (𝟙 X) := ⟨by simp⟩
    have := Etale.isEquivalence_lowerStar (ModuleCat.{u + 1} Λ) a
    have := Etale.isEquivalence_lowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y)
    have : IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁) :=
      Etale.isIso_derivedBaseChangeMapPlus_of_isIso_baseChangeMap _ sq₁
    have : IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂) := by
      rw [Etale.derivedBaseChangeMapPlus_id]
      infer_instance
    exact Etale.isIso_derivedBaseChangeMapPlus_of_paste_vert _ sq₁ sq₂ sq
      (by simpa using sq.w.symm)
  have := key h (Category.id_comp h) sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  infer_instance

/-- The transition map `Rh_*(e^* K) ⟶ Rh'_*(e'^*(π^* K))` between the targets of the derived
base-change maps over `T` and over `T'`, for `π : T' ⟶ T` covered by `a : Y' ⟶ Y` over `X`: the
transition map `AlgebraicGeometry.Etale.lowerStarPlusTransition` along `a`, followed by the
identification `a^* e^* ≅ e'^* π^*` of the derived pullbacks. In degree `q`, at a sheaf placed in
degree `0`, it is `AlgebraicGeometry.Etale.baseChangeTargetTransition`. -/
noncomputable def Etale.targetTransitionPlus {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).obj (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ⟶
      R+((h')_*[ModuleCat.{u + 1} Λ]).obj
        (D+((e')^*[ModuleCat.{u + 1} Λ]).obj (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K)) :=
  Etale.lowerStarPlusTransition Λ a h h' wh _ ≫
    R+((h')_*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).hom.app K)

/-- The identification `a^* e^* ≅ e'^* π^*` of derived pullbacks along a commutative square,
written with the composition isomorphisms along the diagonal, is the one written with
`AlgebraicGeometry.Etale.upperStarPlusComp` and an `eqToHom`. -/
lemma Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app {Y' Y T T' : Scheme.{u}}
    (a : Y' ⟶ Y) (e : Y ⟶ T) (e' : Y' ⟶ T') (π : T' ⟶ T) (wa : a ≫ e = e' ≫ π)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).hom.app K =
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app K ≫ eqToHom (by rw [wa]) ≫
        (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app K := by
  rw [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans,
    Etale.upperStarCompDerivedPlus_eq_eqToIso_trans, eqToIso_refl, Iso.refl_trans,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]

/-- The transition map `AlgebraicGeometry.Etale.baseChangeTargetTransition` is the degree-`q`
homology of `AlgebraicGeometry.Etale.targetTransitionPlus` at the sheaf placed in degree `0`,
followed by the identification `π^*(F[0]) ≅ (π^* F)[0]`. -/
lemma Etale.baseChangeTargetTransition_eq {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) (q : ℤ) (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.baseChangeTargetTransition Λ e h q π a e' h' wa wh F =
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.targetTransitionPlus Λ e h π a e' h' wa wh _ ≫
          R+((h')_*[ModuleCat.{u + 1} Λ]).map (D+((e')^*[ModuleCat.{u + 1} Λ]).map
            ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))) := by
  rw [Etale.baseChangeTargetTransition, Etale.targetTransitionPlus,
    Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app]
  simp only [Functor.map_comp, Category.assoc]

/-- The coherence of the identifications of derived pullbacks entering the composition law
`AlgebraicGeometry.Etale.targetTransitionPlus_comp`, for two stacked commutative squares
`a₂ ≫ e = e₂ ≫ π₂` and `a₁ ≫ e₂ = e₁ ≫ π₁`. It follows from three instances of the
associativity law `AlgebraicGeometry.Etale.upperStarCompDerivedPlus_assoc`. -/
lemma Etale.upperStarCompDerivedPlus_coherence {T T₂ T₁ Y Y₂ Y₁ : Scheme.{u}} (e : Y ⟶ T)
    (e₂ : Y₂ ⟶ T₂) (e₁ : Y₁ ⟶ T₁) (π₂ : T₂ ⟶ T) (π₁ : T₁ ⟶ T₂) (π : T₁ ⟶ T)
    (a₂ : Y₂ ⟶ Y) (a₁ : Y₁ ⟶ Y₂) (a : Y₁ ⟶ Y) (ha : a₁ ≫ a₂ = a) (hπ : π₁ ≫ π₂ = π)
    (wa₂ : a₂ ≫ e = e₂ ≫ π₂) (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁) (wa : a ≫ e = e₁ ≫ π)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).hom.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).inv.app K ≫
          (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).hom.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ e₂ (a₁ ≫ e₂) rfl).inv.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π₁ (a₁ ≫ e₂) wa₁).hom.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₁ π₂ π hπ.symm).inv.app K) =
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π (a ≫ e) wa).hom.app K := by
  have A1 := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    a₁ a₂ e a (a₂ ≫ e) (a ≫ e) ha.symm rfl rfl) K
  have A2 := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    a₁ e₂ π₂ (a₁ ≫ e₂) (a₂ ≫ e) (a ≫ e) rfl wa₂ (by simp only [← ha, Category.assoc, wa₂])) K
  have A3 := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    e₁ π₁ π₂ (a₁ ≫ e₂) π (a ≫ e) wa₁ hπ.symm (by simp only [← ha, Category.assoc, wa₂])) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A1 A2 A3
  have A1' : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).hom.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).inv.app K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ (a₂ ≫ e) (a ≫ e)
        (by simp only [← ha, Category.assoc])).hom.app K := by
    rw [← cancel_mono (D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).hom.app K)),
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
    rw [Category.assoc, A1, Iso.inv_hom_id_app_assoc]
  have A2' : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ (a₂ ≫ e) (a ≫ e)
        (by simp only [← ha, Category.assoc])).hom.app K ≫
      D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).hom.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ e₂ (a₁ ≫ e₂) rfl).inv.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a₁ ≫ e₂) π₂ (a ≫ e)
        (by simp only [← ha, Category.assoc, wa₂])).hom.app K := by
    rw [reassoc_of% A2, Iso.hom_inv_id_app, Category.comp_id]
  have A3' : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a₁ ≫ e₂) π₂ (a ≫ e)
        (by simp only [← ha, Category.assoc, wa₂])).hom.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π₁ (a₁ ≫ e₂) wa₁).hom.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₁ π₂ π hπ.symm).inv.app K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π (a ≫ e) wa).hom.app K := by
    rw [← reassoc_of% A3, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [Functor.map_comp, Category.assoc, reassoc_of% A1', reassoc_of% A2', A3']

/-- **The transition maps of the targets compose.** The transition map from `T` to `T₂` followed
by the one from `T₂` to `T₁` is, modulo the composition isomorphism `π₁^* π₂^* ≅ π^*`, the
transition map from `T` to `T₁`. -/
lemma Etale.targetTransitionPlus_comp {X T T₂ T₁ Y Y₂ Y₁ : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X)
    (π₂ : T₂ ⟶ T) (a₂ : Y₂ ⟶ Y) (e₂ : Y₂ ⟶ T₂) (h₂ : Y₂ ⟶ X) (wa₂ : a₂ ≫ e = e₂ ≫ π₂)
    (wh₂ : a₂ ≫ h = h₂) (π₁ : T₁ ⟶ T₂) (a₁ : Y₁ ⟶ Y₂) (e₁ : Y₁ ⟶ T₁) (h₁ : Y₁ ⟶ X)
    (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁) (wh₁ : a₁ ≫ h₂ = h₁) (π : T₁ ⟶ T) (a : Y₁ ⟶ Y)
    (ha : a₁ ≫ a₂ = a) (hπ : π₁ ≫ π₂ = π) (wa : a ≫ e = e₁ ≫ π) (wh : a ≫ h = h₁)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.targetTransitionPlus Λ e h π₂ a₂ e₂ h₂ wa₂ wh₂ K ≫
        Etale.targetTransitionPlus Λ e₂ h₂ π₁ a₁ e₁ h₁ wa₁ wh₁
          (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map (D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₁ π₂ π hπ.symm).inv.app K)) =
      Etale.targetTransitionPlus Λ e h π a e₁ h₁ wa wh K := by
  have hc := Etale.lowerStarPlusTransition_comp Λ a₂ a₁ a ha h h₂ h₁ wh₂ wh₁ wh
    (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)
  have hc' : Etale.lowerStarPlusTransition Λ a₂ h h₂ wh₂ (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        Etale.lowerStarPlusTransition Λ a₁ h₂ h₁ wh₁
          (D+((a₂)^*[ModuleCat.{u + 1} Λ]).obj (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)) =
      Etale.lowerStarPlusTransition Λ a h h₁ wh (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).hom.app
            (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)) := by
    rw [← hc, Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  simp only [Etale.targetTransitionPlus, Category.assoc]
  rw [reassoc_of% (Etale.lowerStarPlusTransition_naturality Λ a₁ h₂ h₁ wh₁
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).hom.app K)),
    reassoc_of% hc',
    ← Etale.upperStarCompDerivedPlus_coherence Λ e e₂ e₁ π₂ π₁ π a₂ a₁ a ha hπ wa₂ wa₁ wa K]
  simp only [Functor.map_comp, Category.assoc]

/-- The form of `AlgebraicGeometry.Etale.baseChange_app_comp_lowerStarPlusTransition` with the
transition map `AlgebraicGeometry.Etale.targetTransitionPlus` and a base `g'` of the second square
which is only equal to `π ≫ g`. -/
lemma Etale.baseChange_app_comp_targetTransitionPlus {X S T Y T' Y' : Scheme.{u}} {p : X ⟶ S}
    {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} (sq : CommSq e h g p) (π : T' ⟶ T) {e' : Y' ⟶ T'}
    {h' : Y' ⟶ X} (g' : T' ⟶ S) (hg : π ≫ g = g') (sq' : CommSq e' h' g' p) (a : Y' ⟶ Y)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K ≫
        Etale.targetTransitionPlus Λ e h π a e' h' wa wh K =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.lowerStarPlusTransition Λ π g g' hg K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
          (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  subst hg
  rw [Etale.targetTransitionPlus, Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app]
  exact Etale.baseChange_app_comp_lowerStarPlusTransition Λ sq π sq' a wa wh K

/-- The transition map `AlgebraicGeometry.Etale.lowerStarPlusTransition` along a universal
homeomorphism is an isomorphism. -/
lemma Etale.isIso_lowerStarPlusTransition {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    [IsUniversalHomeomorphism a] (h : Y ⟶ X) (h' : Y' ⟶ X) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Etale.lowerStarPlusTransition Λ a h h' w K) := by
  have sq : CommSq a h' h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' w sq]
  have := Etale.isIso_baseChange_app_of_isUniversalHomeomorphism Λ a h h' sq K
  infer_instance

/-- The transition map `AlgebraicGeometry.Etale.targetTransitionPlus` along a universal
homeomorphism `a` is an isomorphism. -/
lemma Etale.isIso_targetTransitionPlus {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) (π : T' ⟶ T) (a : Y' ⟶ Y) [IsUniversalHomeomorphism a] (e' : Y' ⟶ T')
    (h' : Y' ⟶ X) (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Etale.targetTransitionPlus Λ e h π a e' h' wa wh K) := by
  have := Etale.isIso_lowerStarPlusTransition Λ a h h' wh (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)
  rw [Etale.targetTransitionPlus]
  infer_instance

omit [CommRing Λ] in
/-- In a commutative square of modules whose horizontal sides are isomorphisms, an element is
in the range of the left side if and only if its image is in the range of the right side. -/
private lemma mem_range_iff_of_comm {R : Type*} [Ring R] {A B C D : ModuleCat R}
    (f : A ⟶ B) (g : C ⟶ D) (s : A ⟶ C) (t : B ⟶ D) [IsIso s] [IsIso t] (w : f ≫ t = s ≫ g)
    (y : B) : y ∈ Set.range f.hom ↔ t.hom y ∈ Set.range g.hom := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨s.hom z, by rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← w,
      ModuleCat.hom_comp, LinearMap.comp_apply]⟩
  · rintro ⟨z, hz⟩
    refine ⟨(inv s).hom z, ((ConcreteCategory.isIso_iff_bijective t).1 inferInstance).1 ?_⟩
    change (f ≫ t).hom _ = _
    rw [w, ← hz, ModuleCat.hom_comp, LinearMap.comp_apply, ← LinearMap.comp_apply s.hom,
      ← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply]

/-- The degree-`q` base-change map is the degree-`q` homology of the derived base-change map at
the sheaf placed in degree `0`. -/
lemma Etale.baseChangeHomologyMap_eq_homologyFunctor_map {X S T Y : Scheme.{u}} {p : X ⟶ S}
    {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.baseChangeHomologyMap Λ sq q F = (DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  rw [Etale.baseChangeHomologyMap, Etale.baseChangeHomologyNatTrans_eq,
    Functor.whiskerLeft_whiskerRight_app]

omit [CommRing Λ] in
/-- The naturality of a natural transformation `β` along the inverse of an isomorphism
`E ⋙ G ≅ G' ⋙ E'`, stated for abstract functors so that its instances at the concrete derived
functors are checked syntactically. -/
@[reassoc]
private lemma natTrans_app_comp_map_map_iso_inv_app {𝒜 𝒜' ℬ ℬ' 𝒞 𝒞' 𝒟 : Type*} [Category* 𝒜]
    [Category* 𝒜'] [Category* ℬ] [Category* ℬ'] [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟]
    {E : 𝒜 ⥤ ℬ} {G : ℬ ⥤ ℬ'} {G' : 𝒜 ⥤ 𝒜'} {E' : 𝒜' ⥤ ℬ'} (s : E ⋙ G ≅ G' ⋙ E')
    {P₁ : ℬ' ⥤ 𝒞} {P₂ : 𝒞 ⥤ 𝒟} {Q₁ : ℬ' ⥤ 𝒞'} {Q₂ : 𝒞' ⥤ 𝒟} (β : P₁ ⋙ P₂ ⟶ Q₁ ⋙ Q₂)
    (F : 𝒜) :
    β.app (E'.obj (G'.obj F)) ≫ Q₂.map (Q₁.map (s.inv.app F)) =
      P₂.map (P₁.map (s.inv.app F)) ≫ β.app (G.obj (E.obj F)) :=
  (β.naturality (s.inv.app F)).symm

omit [CommRing Λ] in
/-- The naturality of a natural transformation `β` along the inverse of an isomorphism
`H ≅ G₁ ⋙ G₂`, stated for abstract functors. -/
@[reassoc]
private lemma natTrans_app_comp_map_map_comp_iso_inv_app {𝒜 ℬ ℬ' 𝒞 𝒞' 𝒟 : Type*} [Category* 𝒜]
    [Category* ℬ] [Category* ℬ'] [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟]
    {H : 𝒜 ⥤ ℬ'} {G₁ : 𝒜 ⥤ ℬ} {G₂ : ℬ ⥤ ℬ'} (s : H ≅ G₁ ⋙ G₂)
    {P₁ : ℬ' ⥤ 𝒞} {P₂ : 𝒞 ⥤ 𝒟} {Q₁ : ℬ' ⥤ 𝒞'} {Q₂ : 𝒞' ⥤ 𝒟} (β : P₁ ⋙ P₂ ⟶ Q₁ ⋙ Q₂)
    (F : 𝒜) :
    β.app (G₂.obj (G₁.obj F)) ≫ Q₂.map (Q₁.map (s.inv.app F)) =
      P₂.map (P₁.map (s.inv.app F)) ≫ β.app (H.obj F) :=
  (β.naturality (s.inv.app F)).symm

/-- The comparison underlying `AlgebraicGeometry.Etale.survivesBaseChange_comp_iff_of_surjective`,
for arbitrary Cartesian squares over `T₂` and over `T₁` and a universal homeomorphism
`i : T₁ ⟶ T₂` whose base change `a'` is a universal homeomorphism. The transitions from `T₂` to
`T₁` of the sources and of the targets of the base-change maps are isomorphisms, the transition
from `T` to `T₁` factors through the one to `T₂`, and the base-change maps commute with them, so
the image of `ξ` lies in the image of the base-change map over `T₁` if and only if it does over
`T₂`. -/
theorem Etale.mem_range_iff_of_isUniversalHomeomorphism {X S T Y T₂ Y₂ T₁ Y₁ : Scheme.{u}}
    {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    (f₂ : T₂ ⟶ T) {e₂ : Y₂ ⟶ T₂} {h₂ : Y₂ ⟶ X} (sq₂ : IsPullback e₂ h₂ (f₂ ≫ g) p)
    (a₂ : Y₂ ⟶ Y) (wa₂ : a₂ ≫ e = e₂ ≫ f₂) (wh₂ : a₂ ≫ h = h₂)
    (i : T₁ ⟶ T₂) [IsUniversalHomeomorphism i] {e₁ : Y₁ ⟶ T₁} {h₁ : Y₁ ⟶ X}
    (sq₁ : IsPullback e₁ h₁ ((i ≫ f₂) ≫ g) p) (a₁ : Y₁ ⟶ Y) (wa₁ : a₁ ≫ e = e₁ ≫ i ≫ f₂)
    (wh₁ : a₁ ≫ h = h₁) (a' : Y₁ ⟶ Y₂) [IsUniversalHomeomorphism a'] (wa' : a' ≫ e₂ = e₁ ≫ i)
    (wh' : a' ≫ h₂ = h₁) (ha : a' ≫ a₂ = a₁) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeTargetTransition Λ e h q (i ≫ f₂) a₁ e₁ h₁ wa₁ wh₁ F)).hom ξ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq₁ q (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F))).hom ↔
    ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeTargetTransition Λ e h q f₂ a₂ e₂ h₂ wa₂ wh₂ F)).hom ξ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq₂ q (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F))).hom := by
  obtain ⟨s, t, hs, ht, hst, htT⟩ : ∃ (s : (Etale.baseChangeSourceFunctor Λ p (f₂ ≫ g) q).obj
        (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ⟶ (Etale.baseChangeSourceFunctor Λ p
          ((i ≫ f₂) ≫ g) q).obj (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F))
      (t : (Etale.baseChangeTargetFunctor Λ e₂ h₂ q).obj (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ⟶
        (Etale.baseChangeTargetFunctor Λ e₁ h₁ q).obj (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F)),
      IsIso s ∧ IsIso t ∧
        Etale.baseChangeHomologyMap Λ sq₂ q (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ≫ t =
          s ≫ Etale.baseChangeHomologyMap Λ sq₁ q (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ∧
        Etale.baseChangeTargetTransition Λ e h q f₂ a₂ e₂ h₂ wa₂ wh₂ F ≫ t =
          Etale.baseChangeTargetTransition Λ e h q (i ≫ f₂) a₁ e₁ h₁ wa₁ wh₁ F := by
    refine ⟨(DerivedCategory.Plus.homologyFunctor _ q).map (D+((p)^*[ModuleCat.{u + 1} Λ]).map
        (R+((f₂ ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((((f₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F) ≫
        Etale.lowerStarPlusTransition Λ i (f₂ ≫ g) ((i ≫ f₂) ≫ g) (Category.assoc _ _ _).symm
          (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
        R+(((i ≫ f₂) ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) i f₂ (i ≫ f₂) rfl).inv.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
            ((((i ≫ f₂))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              F))),
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h₂)_*[ModuleCat.{u + 1} Λ]).map (D+((e₂)^*[ModuleCat.{u + 1} Λ]).map
          ((((f₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F)) ≫
        Etale.targetTransitionPlus Λ e₂ h₂ i a' e₁ h₁ wa' wh'
          (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map (D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) i f₂ (i ≫ f₂) rfl).inv.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
            ((((i ≫ f₂))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              F))), ?_, ?_, ?_, ?_⟩
    · have := Etale.isIso_lowerStarPlusTransition Λ i (f₂ ≫ g) ((i ≫ f₂) ≫ g)
        (Category.assoc _ _ _).symm
        (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
      infer_instance
    · have := Etale.isIso_targetTransitionPlus Λ e₂ h₂ i a' e₁ h₁ wa' wh'
        (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
      infer_instance
    · rw [Etale.baseChangeHomologyMap_eq_homologyFunctor_map,
        Etale.baseChangeHomologyMap_eq_homologyFunctor_map, ← Functor.map_comp, ← Functor.map_comp]
      congr 1
      have c := Etale.baseChange_app_comp_targetTransitionPlus Λ sq₂.toCommSq i ((i ≫ f₂) ≫ g)
        (Category.assoc _ _ _).symm sq₁.toCommSq a' wa' wh'
        (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
      rw [natTrans_app_comp_map_map_iso_inv_app_assoc, reassoc_of% c]
      simp only [Functor.map_comp, Category.assoc]
      rw [natTrans_app_comp_map_map_comp_iso_inv_app_assoc, natTrans_app_comp_map_map_iso_hom_app]
    · rw [Etale.baseChangeTargetTransition_eq, Etale.baseChangeTargetTransition_eq,
        ← Functor.map_comp]
      congr 1
      have hT := Etale.targetTransitionPlus_comp Λ e h f₂ a₂ e₂ h₂ wa₂ wh₂ i a' e₁ h₁ wa' wh'
        (i ≫ f₂) a₁ ha rfl wa₁ wh₁ ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
      simp only [Category.assoc, Functor.map_comp] at hT ⊢
      rw [← Functor.map_comp_assoc (R+((h₂)_*[ModuleCat.{u + 1} Λ])),
        ← Functor.map_comp (D+((e₂)^*[ModuleCat.{u + 1} Λ])), Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rw [reassoc_of% hT]
  have := hs
  have := ht
  rw [← htT, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact (mem_range_iff_of_comm _ _ ((X.uliftPointSmallEtale x).sheafFiber.map s)
    ((X.uliftPointSmallEtale x).sheafFiber.map t)
    (by rw [← Functor.map_comp, ← Functor.map_comp, hst]) _).symm

end TransitionComposition

end AlgebraicGeometry
