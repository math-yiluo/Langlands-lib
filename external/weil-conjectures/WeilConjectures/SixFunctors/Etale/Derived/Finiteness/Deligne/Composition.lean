/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.ClosedImmersion

/-!
# Generic constructibility of a direct image along a composite

For morphisms `v : V ⟶ X` and `j : X ⟶ Y` of `S`-schemes and a complex `M` on `V`: if the direct
images of `M` along `v` (over `S`, with `X` an `S`-scheme through `j`) and along `v ≫ j` are
bounded constructible and commute with base change over `U`, then so is the direct image of
`Rv_* M` along `j` (`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_comp`): after a base
change, `Rj_{T,*} (Rv_* M)_T ≅ Rj_{T,*} Rv_{T,*} M_T = R(v ≫ j)_{T,*} M_T`, and the base change
maps paste vertically.

The direct image along a closed immersion of a bounded constructible complex has the property over
every subset of the base
(`AlgebraicGeometry.Etale.hasDirectImageBaseChangeOnPlus_of_isClosedImmersion`), by finite base
change. Together these give the passage from a closed subscheme `i : W ⟶ X` to `X`
in the third step of the proof of `theorem-generic-constructibility-base-change-rj`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Vertical pasting, at an object, the other way**: for two squares pasted vertically, if the
derived base change map of the pasted square is an isomorphism at `K` and that of the upper square
is an isomorphism at `K`, then that of the lower square is an isomorphism at `Rf_* K`. -/
lemma isIso_derivedBaseChangeMapPlus_app_of_paste_vert {X' X Y' Y Z' Z : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z}
    {k : Z' ⟶ Z} (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' (f' ≫ e') (f ≫ e) k)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h₁ : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁).app K))
    (hsq : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K)) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂).app
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K)) := by
  have e := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_vert (ModuleCat.{u + 1} Λ) sq₁ sq₂ sq) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj] at e
  rw [e, isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff,
    isIso_comp_right_iff] at hsq
  exact hsq

/-- **Composition**: for `v : V ⟶ X` and `j : X ⟶ Y` over `S` and a complex `M` on `V`, if the
direct images of `M` along `v` and along `v ≫ j` are bounded constructible and commute with base
change over `U`, then so is the direct image of `Rv_* M` along `j`. -/
theorem HasDirectImageBaseChangeOnPlus.of_comp {S V X Y : Scheme.{u}} {fY : Y ⟶ S}
    (v : V ⟶ X) (j : X ⟶ Y)
    {M : _root_.DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {U : Set S} (hv : HasDirectImageBaseChangeOnPlus Λ (j ≫ fY) v M U)
    (hjv : HasDirectImageBaseChangeOnPlus Λ fY (v ≫ j) M U) :
    HasDirectImageBaseChangeOnPlus Λ fY j ((v)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj M)
      U := by
  intro T _ t ht YT XT gT fT gXT jT hYT sqT
  let VT := pullback v gXT
  let gVT : VT ⟶ V := pullback.fst v gXT
  let vT : VT ⟶ XT := pullback.snd v gXT
  have hV : IsPullback gVT vT v gXT := IsPullback.of_hasPullback v gXT
  obtain ⟨cv, iv⟩ := hv T t ht XT VT gXT (jT ≫ fT) gVT vT (sqT.paste_vert hYT) hV
  obtain ⟨cvj, ivj⟩ := hjv T t ht YT VT gT fT gVT (vT ≫ jT) hYT (hV.paste_vert sqT)
  refine ⟨ObjectProperty.prop_of_iso _ ?_ cvj, ?_⟩
  · exact _root_.DerivedCategory.Plus.ι.mapIso
      ((Functor.rightDerivedFunctorPlusCompIso' (vT)_*[ModuleCat.{u + 1} Λ]
          (jT)_*[ModuleCat.{u + 1} Λ] (lowerStarComp (ModuleCat.{u + 1} Λ) vT jT)).symm.app _ ≪≫
        (jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
          (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) hV.toCommSq).app M)).symm)
  · exact isIso_derivedBaseChangeMapPlus_app_of_paste_vert hV.toCommSq sqT.toCommSq _ M iv ivj

/-- **Closed immersions**: for a closed immersion `i : W ⟶ X` into a locally finite type
`S`-scheme and a bounded constructible complex `M` on `W`, the direct image of `M` along `i` is
bounded constructible and commutes with base change over every `U ⊆ S`. -/
theorem hasDirectImageBaseChangeOnPlus_of_isClosedImmersion {S W X : Scheme.{u}} {fX : X ⟶ S}
    [LocallyOfFiniteType fX] (i : W ⟶ X) [IsClosedImmersion i]
    {M : _root_.DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) W
      (_root_.DerivedCategory.Plus.ι.obj M)) (U : Set S) :
    HasDirectImageBaseChangeOnPlus Λ fX i M U := by
  intro T _ t _ XT WT gXT fT gWT iT hXT sqT
  have : LocallyOfFiniteType fT := MorphismProperty.of_isPullback hXT inferInstance
  have : IsLocallyNoetherian XT := LocallyOfFiniteType.isLocallyNoetherian fT
  have : IsClosedImmersion iT := MorphismProperty.of_isPullback sqT inferInstance
  refine ⟨ObjectProperty.prop_of_iso _
    ((iT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app _).symm
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion iT
      (hM.mapDerivedCategory_upperStar gWT)), ?_⟩
  have : IsFinite i := ((IsClosedImmersion.iff_isFinite_and_mono i).1 inferInstance).1
  have : IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sqT.toCommSq) :=
    IsBaseChangeIso.isIso _ _ _ sqT
  infer_instance

end Etale

end AlgebraicGeometry
