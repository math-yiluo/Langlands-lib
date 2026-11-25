/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions

/-!
# Transition maps of the base-change map

For a Cartesian square on `p : X ⟶ S` along `g : T ⟶ S` and a morphism `π : T' ⟶ T`, the
source and the target of the degree-`q` base-change map over `T` map to those over `T'`. This
file defines these transition maps and proves that they commute with the base-change maps.

## Main definitions

- `AlgebraicGeometry.Etale.baseChangeTargetTransition`: the map relating the targets of the
  base-change maps over `T` and over `T'`, for `π : T' ⟶ T`.
- `AlgebraicGeometry.Etale.baseChangeSourceTransition`: the same for the sources.

## Main statements

- `AlgebraicGeometry.Etale.baseChangeHomologyMap_comp_baseChangeTargetTransition`: the
  base-change maps over `T` and over `T'` commute with the transition maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section Transition

variable {X T Y T' Y' : Scheme.{u}}

/-- The map from the target of the base-change map over `T` to the target of the base-change
map over `T'`, for `π : T' ⟶ T` covered by `a : Y' ⟶ Y` over `X`: `H^q` applied to the
transition map `Rh_*(e^*(F[0])) ⟶ Rh'_*(a^* e^*(F[0])) ≅ Rh'_*(e'^*((π^* F)[0]))` of
`AlgebraicGeometry.Etale.lowerStarPlusTransition`. -/
noncomputable def Etale.baseChangeTargetTransition (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X) (wa : a ≫ e = e' ≫ π)
    (wh : a ≫ h = h') (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.baseChangeTargetFunctor Λ e h q).obj F ⟶
      (Etale.baseChangeTargetFunctor Λ e' h' q).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    (Etale.lowerStarPlusTransition Λ a h h' wh _ ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
          eqToHom (by rw [wa]) ≫
          (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app _ ≫
          D+((e')^*[ModuleCat.{u + 1} Λ]).map
            ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)))

end Transition

section TransitionCompat

variable {X S T Y T' Y' : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- For a commutative square with sides `a`, `a ≫ h`, `h` and `𝟙 X`, the composition isomorphism
`D(a ≫ h)^*⁺ ≅ Dh^*⁺ ⋙ Da^*⁺` is the identity isomorphism of `D(𝟙 X)^*⁺` followed by the
pullback comparison of the square. -/
lemma Etale.upperStarPlusComp_hom_app_eq_pullbackSquareComparison {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    (h : Y ⟶ X) (sq : CommSq a (a ≫ h) h (𝟙 X))
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom.app M =
      D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app M) ≫
        (Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq).hom.app M := by
  rw [Etale.pullbackSquareComparison_eq, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, ← Category.assoc,
    Etale.upperStarCompDerivedPlus_id_right_inv_app, Category.id_comp,
    Etale.upperStarCompDerivedPlus_eq_eqToIso_trans, eqToIso_refl, Iso.refl_trans]

/-- The transition map `Rh_* K ⟶ Rh'_* (a^* K)` of a triangle `a ≫ h = h'` is the derived
base-change map of the degenerate square with sides `a`, `h'`, `h` and `𝟙 X`, preceded by the
identity isomorphism `Rh_* K ≅ (𝟙 X)^* Rh_* K`. -/
lemma Etale.lowerStarPlusTransition_eq_baseChange {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    (h : Y ⟶ X) (h' : Y' ⟶ X) (w : a ≫ h = h') (sq : CommSq a h' h (𝟙 X))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.lowerStarPlusTransition Λ a h h' w K =
      (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app
          (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K := by
  subst w
  rw [Etale.baseChange_app, Etale.baseChangeUnitStep_app, Etale.baseChangeSquareStep_hom_app,
    Etale.baseChangeCounitStep_app, Etale.lowerStarPlusTransition, eqToIso_refl, Iso.refl_trans,
    Etale.upperStarPlusComp_hom_app_eq_pullbackSquareComparison Λ a h sq]
  have hu : (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app
        (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).unit.app
        ((R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K) =
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).unit.app
        (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map (D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app
          (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) :=
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).unit.naturality _
  conv_rhs => rw [← Category.assoc, hu]
  simp only [Functor.map_comp, Category.assoc]

/-- **Compatibility of the base-change map with the transition maps.** For a square `sq` on
`p` along `g`, a morphism `π : T' ⟶ T` and a square `sq'` on `p` along `π ≫ g` covering `π`
through `a`, the derived base-change map of `sq` followed by the transition map of the targets
is the pullback along `p` of the transition map of the sources followed by the derived
base-change map of `sq'`. Both composites are the derived base-change map of the square with
sides `e' ≫ π`, `h'`, `g` and `p`, by the pasting law, once the transition maps are written as
base-change maps of degenerate squares
(`AlgebraicGeometry.Etale.lowerStarPlusTransition_eq_baseChange`). -/
theorem Etale.baseChange_app_comp_lowerStarPlusTransition (sq : CommSq e h g p) (π : T' ⟶ T)
    {e' : Y' ⟶ T'} {h' : Y' ⟶ X} (sq' : CommSq e' h' (π ≫ g) p) (a : Y' ⟶ Y)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K ≫
        Etale.lowerStarPlusTransition Λ a h h' wh (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app K ≫
            eqToHom (by rw [wa]) ≫
            (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app K) =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.lowerStarPlusTransition Λ π g (π ≫ g) rfl K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
          (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  have degT : CommSq a h' h (𝟙 X) := ⟨by rw [wh, Category.comp_id]⟩
  have degS : CommSq π (π ≫ g) g (𝟙 S) := ⟨by rw [Category.comp_id]⟩
  have sqT : CommSq (e' ≫ π) h' g p := ⟨by rw [Category.assoc, sq'.w]⟩
  have h₁ := Etale.baseChange_app_paste_horiz_of_eq Λ sq degT sqT wa (Category.id_comp p) K
  have h₂ := Etale.baseChange_app_paste_horiz_of_eq Λ degS sq' sqT rfl (Category.comp_id p) K
  have hc : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (e' ≫ π) wa.symm).hom.app K ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app K ≫ eqToHom (by rw [wa]) ≫
        (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app K =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (e' ≫ π) rfl).hom.app K := by
    rw [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans,
      Etale.upperStarCompDerivedPlus_eq_eqToIso_trans, eqToIso_refl, Iso.refl_trans,
      Iso.trans_hom, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc, eqToIso.hom,
      eqToHom_app, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h₁' : D+((𝟙 X)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) degT).app (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (𝟙 X) p p
        (Category.id_comp p).symm).inv.app (R+((g)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sqT).app K ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (e' ≫ π)
          wa.symm).hom.app K) := by
    rw [h₁]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
      Iso.inv_hom_id_app_assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h₂' : D+((p)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) degS).app K) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) p (𝟙 S) p
        (Category.comp_id p).symm).inv.app (R+((g)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sqT).app K ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (e' ≫ π) rfl).hom.app K) := by
    rw [h₂]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
      Iso.inv_hom_id_app_assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.naturality
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K)
  rw [Functor.id_map] at hn
  rw [Etale.lowerStarPlusTransition_eq_baseChange Λ a h h' wh degT,
    Etale.lowerStarPlusTransition_eq_baseChange Λ π g (π ≫ g) rfl degS, Category.assoc,
    reassoc_of% hn]
  erw [reassoc_of% h₁']
  rw [(D+((p)^*[ModuleCat.{u + 1} Λ])).map_comp, Category.assoc, h₂',
    reassoc_of% Etale.upperStarCompDerivedPlus_id_left_inv_app,
    reassoc_of% Etale.upperStarCompDerivedPlus_id_right_inv_app, ← Functor.map_comp, hc]

/-- The map from the source of the base-change map over `T` to the source of the base-change
map over `T'`, for `π : T' ⟶ T`: `H^q` of the pullback along `p` of the transition map
`Rg_*(F[0]) ⟶ R(π ≫ g)_*(π^*(F[0])) ≅ R(π ≫ g)_*((π^* F)[0])` of
`AlgebraicGeometry.Etale.lowerStarPlusTransition`. -/
noncomputable def Etale.baseChangeSourceTransition (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
    (π : T' ⟶ T) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.baseChangeSourceFunctor Λ p g q).obj F ⟶
      (Etale.baseChangeSourceFunctor Λ p (π ≫ g) q).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    (D+((p)^*[ModuleCat.{u + 1} Λ]).map
      (Etale.lowerStarPlusTransition Λ π g (π ≫ g) rfl _ ≫
        R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)))

/- Generic forms of the identifications used below, stated for abstract functors so that their
instances at the concrete derived functors are checked syntactically (see the implementation
notes of `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality`). -/
omit [CommRing Λ] in
/-- The naturality of `β` along the hom of an isomorphism `E ⋙ G ≅ G' ⋙ E'`. -/
lemma natTrans_app_comp_map_map_iso_hom_app {𝒜 𝒜' ℬ ℬ' 𝒞 𝒞' 𝒟 : Type*} [Category* 𝒜]
    [Category* 𝒜'] [Category* ℬ] [Category* ℬ'] [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟]
    {E : 𝒜 ⥤ ℬ} {G : ℬ ⥤ ℬ'} {G' : 𝒜 ⥤ 𝒜'} {E' : 𝒜' ⥤ ℬ'} (s : E ⋙ G ≅ G' ⋙ E')
    {P₁ : ℬ' ⥤ 𝒞} {P₂ : 𝒞 ⥤ 𝒟} {Q₁ : ℬ' ⥤ 𝒞'} {Q₂ : 𝒞' ⥤ 𝒟} (β : P₁ ⋙ P₂ ⟶ Q₁ ⋙ Q₂)
    (F : 𝒜) :
    β.app (G.obj (E.obj F)) ≫ Q₂.map (Q₁.map (s.hom.app F)) =
      P₂.map (P₁.map (s.hom.app F)) ≫ β.app (E'.obj (G'.obj F)) :=
  (β.naturality (s.hom.app F)).symm

/-- The form of `AlgebraicGeometry.Etale.baseChange_app_comp_lowerStarPlusTransition` for a
sheaf placed in degree `0`, including the identifications `π^*(F[0]) ≅ (π^* F)[0]`. -/
theorem Etale.baseChange_app_single_comp_transition (sq : IsPullback e h g p)
    (π : T' ⟶ T) {e' : Y' ⟶ T'} {h' : Y' ⟶ X} (sq' : IsPullback e' h' (π ≫ g) p)
    (a : Y' ⟶ Y) (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (Etale.lowerStarPlusTransition Λ a h h' wh _ ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
            eqToHom (by rw [wa]) ≫
            (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app _ ≫
            D+((e')^*[ModuleCat.{u + 1} Λ]).map
              ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))) =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map
          (Etale.lowerStarPlusTransition Λ π g (π ≫ g) rfl _ ≫
            R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).map
              ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq'.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
  have hc := Etale.baseChange_app_comp_lowerStarPlusTransition Λ sq.toCommSq π sq'.toCommSq a
    wa wh ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  simp only [Functor.map_comp, Category.assoc] at hc ⊢
  rw [reassoc_of% hc, natTrans_app_comp_map_map_iso_hom_app]

/-- The degree-`q` base-change maps over `T` and over `T'` commute with the transition maps
`AlgebraicGeometry.Etale.baseChangeSourceTransition` and
`AlgebraicGeometry.Etale.baseChangeTargetTransition`. -/
theorem Etale.baseChangeHomologyMap_comp_baseChangeTargetTransition (sq : IsPullback e h g p)
    (q : ℤ) (π : T' ⟶ T) {e' : Y' ⟶ T'} {h' : Y' ⟶ X} (sq' : IsPullback e' h' (π ≫ g) p)
    (a : Y' ⟶ Y) (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.baseChangeHomologyMap Λ sq q F ≫
        Etale.baseChangeTargetTransition Λ e h q π a e' h' wa wh F =
      Etale.baseChangeSourceTransition Λ p g q π F ≫
        Etale.baseChangeHomologyMap Λ sq' q (((π)^*[ModuleCat.{u + 1} Λ]).obj F) := by
  rw [Etale.baseChangeHomologyMap, Etale.baseChangeHomologyMap,
    Etale.baseChangeHomologyNatTrans_eq, Etale.baseChangeHomologyNatTrans_eq,
    Functor.whiskerLeft_whiskerRight_app, Functor.whiskerLeft_whiskerRight_app,
    Etale.baseChangeTargetTransition, Etale.baseChangeSourceTransition, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1
  exact Etale.baseChange_app_single_comp_transition Λ sq π sq' a wa wh F

end TransitionCompat

end AlgebraicGeometry
