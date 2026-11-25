/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteDerived
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Plus

/-!
# Generic constructibility of a direct image along a composite with a closed immersion

If `j : X ⟶ Z` is a morphism and `i : Z ⟶ Y` a closed immersion of `S`-schemes, the direct
image along `j ≫ i` is the direct image along `j` followed by the exact direct image along `i`,
which preserves bounded constructibility and commutes with every base change (`i` is finite,
`lemma-weil-pbc-finite-exchange`). Hence the generic constructibility and base change property
of `Rj_* K` over `S` implies that of `R(j ≫ i)_* K`
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.comp_isClosedImmersion`). This is the
reduction to a dense open immersion in the proof of
`theorem-generic-constructibility-base-change-rj`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The direct image along a closed immersion into a locally noetherian scheme preserves bounded
constructibility: it is exact, so it commutes with the homology sheaves, and it preserves
constructible sheaves (`proposition-proper-direct-image-finite-coefficients`). -/
lemma boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion {Z Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (i : Z ⟶ Y) [IsClosedImmersion i]
    {K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  have : IsFinite i := ((IsClosedImmersion.iff_isFinite_and_mono i).1 inferInstance).1
  let e (q : ℤ) : (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj K) ≅
        (i)_*[ModuleCat.{u + 1} Λ].obj ((_root_.DerivedCategory.homologyFunctor _ q).obj K) :=
    (_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory _ i).app K) ≪≫
      (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).symm.app K
  have hz (q : ℤ) (h : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R((i)_*[ModuleCat.{u + 1} Λ])).obj K)) :=
    (((i)_*[ModuleCat.{u + 1} Λ]).map_isZero h).of_iso (e q)
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦ ?_⟩
  · exact (_root_.DerivedCategory.isGE_iff _ a).2
      fun q hq ↦ hz q ((_root_.DerivedCategory.isGE_iff _ a).1 ha q hq)
  · exact (_root_.DerivedCategory.isLE_iff _ b).2
      fun q hq ↦ hz q ((_root_.DerivedCategory.isLE_iff _ b).1 hb q hq)
  · have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj K) := hc q
    have := (isConstructibleSheaf_lowerStar_of_isClosedImmersion i
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K)).1
    exact IsConstructibleSheaf.of_iso (e q).symm

/-- The derived base change map of a commutative square only depends on its four arrows. -/
lemma isIso_derivedBaseChangeMapPlus_app_congr' {X' X Y' Y : Scheme.{u}} {g'₁ g'₂ : X' ⟶ X}
    {f'₁ f'₂ : X' ⟶ Y'} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y' ⟶ Y} (h' : g'₁ = g'₂) (hf' : f'₁ = f'₂)
    (hf : f₁ = f₂) (h : g₁ = g₂) (sq₁ : CommSq g'₁ f'₁ f₁ g₁) (sq₂ : CommSq g'₂ f'₂ f₂ g₂)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁).app K) ↔
      IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂).app K) := by
  subst h' hf' hf h
  rfl

/-- **Vertical pasting, at an object**: for two squares pasted vertically, the derived base change
map of the pasted square at `K` is an isomorphism as soon as the one of the upper square is an
isomorphism at `K` and the one of the lower square is an isomorphism at `Rf_* K`. -/
lemma isIso_derivedBaseChangeMapPlus_app_paste_vert {X' X Y' Y Z' Z : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z}
    {k : Z' ⟶ Z} (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' (f' ≫ e') (f ≫ e) k)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h₁ : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁).app K))
    (h₂ : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂).app
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K) := by
  have e := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_vert (ModuleCat.{u + 1} Λ) sq₁ sq₂ sq) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj] at e
  rw [e]
  infer_instance

/-- **Composition with a closed immersion**: if `Rj_* K` is bounded constructible and its
formation commutes with base change over `U`, for `j : X ⟶ Z` and `Z` an `S`-scheme through a
closed immersion `i : Z ⟶ Y` into a locally finite type `S`-scheme `Y`, then the same holds for
`R(j ≫ i)_* K = Ri_* Rj_* K`. -/
theorem HasDirectImageBaseChangeOnPlus.comp_isClosedImmersion {S X Z Y : Scheme.{u}}
    {fY : Y ⟶ S} [LocallyOfFiniteType fY] (j : X ⟶ Z) (i : Z ⟶ Y) [IsClosedImmersion i]
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {U : Set S} (h : HasDirectImageBaseChangeOnPlus Λ (i ≫ fY) j K U) :
    HasDirectImageBaseChangeOnPlus Λ fY (j ≫ i) K U := by
  intro T _ t ht YT XT gT fT gXT jT hYT sqT
  have : LocallyOfFiniteType fT := MorphismProperty.of_isPullback hYT inferInstance
  have : IsLocallyNoetherian YT := LocallyOfFiniteType.isLocallyNoetherian fT
  -- the base change `Z_T = Z ×_Y Y_T` of the closed immersion `i`
  let ZT := pullback i gT
  let gZT : ZT ⟶ Z := pullback.fst i gT
  let iT : ZT ⟶ YT := pullback.snd i gT
  have hZ : IsPullback gZT iT i gT := IsPullback.of_hasPullback i gT
  have : IsClosedImmersion iT := MorphismProperty.pullback_snd i gT inferInstance
  let jT' : XT ⟶ ZT := pullback.lift (gXT ≫ j) jT (by rw [Category.assoc, sqT.w])
  have hjT : jT = jT' ≫ iT := (pullback.lift_snd _ _ _).symm
  have hX : IsPullback gXT jT' j gZT :=
    IsPullback.of_bot (hjT ▸ sqT) (pullback.lift_fst _ _ _).symm hZ
  obtain ⟨c₁, i₁⟩ := h T t ht ZT XT gZT (iT ≫ fT) gXT jT' (hZ.paste_vert hYT) hX
  refine ⟨?_, ?_⟩
  · have e : _root_.DerivedCategory.Plus.ι.obj
        ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) ≅
        (R((iT)_*[ModuleCat.{u + 1} Λ])).obj (_root_.DerivedCategory.Plus.ι.obj
          ((jT')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
            (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) :=
      eqToIso (by rw [hjT]) ≪≫ _root_.DerivedCategory.Plus.ι.mapIso
        ((Functor.rightDerivedFunctorPlusCompIso' (jT')_*[ModuleCat.{u + 1} Λ]
          (iT)_*[ModuleCat.{u + 1} Λ] (lowerStarComp (ModuleCat.{u + 1} Λ) jT' iT)).symm.app
            _) ≪≫ ((iT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app _)
    exact ObjectProperty.prop_of_iso _ e.symm
      (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion iT c₁)
  · have : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) hZ.toCommSq).app
        ((j)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K)) := by
      have : IsFinite i := ((IsClosedImmersion.iff_isFinite_and_mono i).1 inferInstance).1
      have : IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) hZ.toCommSq) :=
        IsBaseChangeIso.isIso _ _ _ hZ
      infer_instance
    have hpaste := isIso_derivedBaseChangeMapPlus_app_paste_vert hX.toCommSq hZ.toCommSq
      (⟨by rw [hX.w_assoc, hZ.w, Category.assoc]⟩ :
        CommSq gXT (jT' ≫ iT) (j ≫ i) gT) K i₁ this
    exact (isIso_derivedBaseChangeMapPlus_app_congr' rfl hjT.symm rfl rfl _ _ K).1 hpaste

end Etale

end AlgebraicGeometry
