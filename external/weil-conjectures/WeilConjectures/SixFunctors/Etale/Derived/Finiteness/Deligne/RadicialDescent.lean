/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphismDescent
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
public import WeilConjectures.SixFunctors.BaseChange.UniversalHomeomorphism
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Plus

/-!
# Descending generic constructibility through a finite radicial base change

Let `π : S' ⟶ S` be finite, surjective and radicial (universally injective), so that `π` and all
its base changes are universal homeomorphisms. If, after base change along `π`, the derived
direct image along `j : X ⟶ Y` is bounded constructible and commutes with every base change from
a noetherian scheme, then the same holds over `S`
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_isFinite_of_surjective`,
blueprint `lemma-universal-homeomorphism-base--1`).

For a noetherian `T` over `S`, the base change `T' = T ×_S S'` is noetherian and
`a : Y_{T'} ⟶ Y_T` is a universal homeomorphism, along which pullback is an equivalence of the
categories of étale sheaves. Pulled back along `a`, the derived base change map over `T` is
identified, by the pasting law for derived base change maps, with the one over `T'` for the base
change along `π`, the derived base change maps along the universal homeomorphisms
`Y_{T'} ⟶ Y_T` and `Y' ⟶ Y` being isomorphisms
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism`).
Bounded constructibility descends along `a`
(`AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_isUniversalHomeomorphism`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The derived pullback along a morphism whose underived pullback is an equivalence (e.g. a
universal homeomorphism) reflects isomorphisms on the bounded below derived categories: an
equivalence reflects isomorphisms, and the homology functors commute with exact functors. -/
lemma isIso_of_isIso_mapDerivedCategoryPlus_upperStar_map {Y Y' : Scheme.{u}} (a : Y' ⟶ Y)
    [((a)^*[ModuleCat.{u + 1} Λ]).IsEquivalence]
    {K L : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ L) (h : IsIso (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map φ)) :
    IsIso φ := by
  rw [_root_.DerivedCategory.Plus.isIso_iff]
  intro n
  have e := (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.naturality
    φ
  simp only [Functor.comp_obj, Functor.comp_map] at e
  have : IsIso (((a)^*[ModuleCat.{u + 1} Λ]).map
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map φ)) := by
    have : IsIso (((a)^*[ModuleCat.{u + 1} Λ]).map
        ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map φ) ≫
        ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app L)) := by
      rw [e]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app L)
  exact isIso_of_reflects_iso _ ((a)^*[ModuleCat.{u + 1} Λ])

/-- **Bounded constructibility descends along a universal homeomorphism** `a : Y' ⟶ Y`: a
complex `K` on `Y` whose pullback `a^* K` is bounded constructible is bounded constructible.
The pullback `a^*` is an exact equivalence, so it reflects boundedness, and it commutes with the
homology sheaves, along which constructibility descends
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_upperStar_of_isUniversalHomeomorphism`). -/
lemma boundedConstructible_of_upperStar_of_isUniversalHomeomorphism {Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) [IsUniversalHomeomorphism a]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y'
      (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K := by
  have := isEquivalence_upperStar (ModuleCat.{u + 1} Λ) a
  refine ⟨Functor.bounded_of_bounded_mapDerivedCategory_obj _ h.1, fun n ↦ ?_⟩
  have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ n).obj
      (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K)) := h.2 n
  have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).obj
      ((_root_.DerivedCategory.homologyFunctor _ n).obj K)) :=
    IsConstructibleSheaf.of_iso (F := (_root_.DerivedCategory.homologyFunctor _ n).obj
      (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K))
      ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app K).symm
  exact Scheme.IsConstructibleSheaf.of_upperStar_of_isUniversalHomeomorphism a _

/-- The derived base change map of a commutative square only depends on its four arrows: two
squares with equal arrows have derived base change maps which are isomorphisms at the same
objects. -/
lemma isIso_derivedBaseChangeMapPlus_app_congr {X' X Y' Y : Scheme.{u}} {g'₁ g'₂ : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g₁ g₂ : Y' ⟶ Y} (h' : g'₁ = g'₂) (h : g₁ = g₂)
    (sq₁ : CommSq g'₁ f' f g₁) (sq₂ : CommSq g'₂ f' f g₂)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁).app K) ↔
      IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂).app K) := by
  subst h' h
  rfl

/-- **Horizontal pasting, at an object**: for two squares pasted horizontally, the derived base
change map of the pasted square at `K` is an isomorphism as soon as the one of the right square is
an isomorphism at `K` and the one of the left square is an isomorphism at `g'^* K`; conversely,
if the pasted one is an isomorphism at `K` and the left one at `g'^* K`, then `h^*` of the right
one is an isomorphism at `K`. -/
lemma isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff {X'' X' X Y'' Y' Y : Scheme.{u}}
    {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'}
    {g : Y' ⟶ Y} (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h₂ : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂).app
      (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K) ↔
      IsIso (((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁).app K)) := by
  have e := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz (ModuleCat.{u + 1} Λ) sq₁ sq₂ sq) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj] at e
  rw [e, isIso_comp_left_iff, isIso_comp_right_iff]

/-- Blueprint `lemma-universal-homeomorphism-base--1`: Descending the exchange property through a
universal homeomorphism, for a bounded below complex.

Let `π : S' ⟶ S` be finite, surjective and radicial (universally injective), let `j : X ⟶ Y` be a
morphism of `S`-schemes and `K` a bounded below complex on `X`. Form the base changes
`Y' = Y ×_S S'` and `X' = X ×_Y Y'`, with `j' : X' ⟶ Y'`. If over `π⁻¹ U` the direct image
`Rj'_*(K|_{X'})` is bounded constructible and its formation commutes with every base change from a
noetherian scheme, then the same holds for `Rj_* K` over `U`. -/
theorem HasDirectImageBaseChangeOnPlus.of_isFinite_of_surjective
    {S S' X Y X' Y' : Scheme.{u}} (π : S' ⟶ S) [IsFinite π] [Surjective π]
    [UniversallyInjective π] (fY : Y ⟶ S) (j : X ⟶ Y) (g : Y' ⟶ Y)
    (fY' : Y' ⟶ S') (hY : IsPullback g fY' fY π) (g' : X' ⟶ X) (j' : X' ⟶ Y')
    (hX : IsPullback g' j' j g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {U : Set S}
    (h : HasDirectImageBaseChangeOnPlus Λ fY' j'
      (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) (π ⁻¹' U)) :
    HasDirectImageBaseChangeOnPlus Λ fY j K U := by
  have : IsUniversalHomeomorphism π := { }
  have : IsUniversalHomeomorphism g := MorphismProperty.of_isPullback hY.flip inferInstance
  intro T _ t ht YT XT gT fT gXT jT hYT sqT
  -- the base change `T' = T ×_S S'`, finite over the noetherian `T`
  let T' := pullback t π
  let p : T' ⟶ T := pullback.fst t π
  let t' : T' ⟶ S' := pullback.snd t π
  have hp : IsPullback p t' t π := IsPullback.of_hasPullback t π
  have : IsFinite p := MorphismProperty.pullback_fst t π inferInstance
  have : IsUniversalHomeomorphism p := MorphismProperty.pullback_fst t π inferInstance
  have : IsNoetherian T' :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian p
      __ := QuasiCompact.compactSpace_of_compactSpace p }
  have ht' : Set.range t' ⊆ π ⁻¹' U := by
    rintro _ ⟨x, rfl⟩
    change (t' ≫ π) x ∈ U
    rw [← hp.w]
    exact ht ⟨p x, rfl⟩
  -- the base change `Y_{T'} = Y_T ×_T T'`, which is also `Y' ×_{S'} T'`
  let YT' := pullback fT p
  let a : YT' ⟶ YT := pullback.fst fT p
  let fT' : YT' ⟶ T' := pullback.snd fT p
  have ha : IsPullback a fT' fT p := IsPullback.of_hasPullback fT p
  have : IsUniversalHomeomorphism a := MorphismProperty.pullback_fst fT p inferInstance
  have hs : IsPullback (a ≫ gT) fT' fY (t' ≫ π) := by
    rw [← hp.w]
    exact ha.paste_horiz hYT
  obtain ⟨b, hb, hbg⟩ : ∃ b : YT' ⟶ Y', IsPullback b fT' fY' t' ∧ b ≫ g = a ≫ gT :=
    ⟨_, IsPullback.of_right' hs hY, hY.lift_fst _ _ _⟩
  -- the base change `X_{T'} = X_T ×_{Y_T} Y_{T'}`, which is also `X' ×_{Y'} Y_{T'}`
  let XT' := pullback jT a
  let a' : XT' ⟶ XT := pullback.fst jT a
  let jT' : XT' ⟶ YT' := pullback.snd jT a
  have ha' : IsPullback a' jT' jT a := IsPullback.of_hasPullback jT a
  have : IsUniversalHomeomorphism a' := MorphismProperty.pullback_fst jT a inferInstance
  have hs' : IsPullback (a' ≫ gXT) jT' j (b ≫ g) := by
    rw [hbg]
    exact ha'.paste_horiz sqT
  obtain ⟨b', hb', hbg'⟩ : ∃ b' : XT' ⟶ X', IsPullback b' jT' j' b ∧ b' ≫ g' = a' ≫ gXT :=
    ⟨_, IsPullback.of_right' hs' hX, hX.lift_fst _ _ _⟩
  obtain ⟨c₁, i₁⟩ := h T' t' ht' YT' XT' b fT' b' jT' hb hb'
  -- the derived base change maps along the universal homeomorphisms are isomorphisms
  have iX := isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism
    (ModuleCat.{u + 1} Λ) hX
  have ia := isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism
    (ModuleCat.{u + 1} Λ) ha'
  have := isEquivalence_upperStar (ModuleCat.{u + 1} Λ) a
  refine ⟨?_, ?_⟩
  · -- bounded constructibility descends along `a`
    refine boundedConstructible_of_upperStar_of_isUniversalHomeomorphism a ?_
    refine ObjectProperty.prop_of_iso _ ?_ c₁
    exact _root_.DerivedCategory.Plus.ι.mapIso
      ((jT')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
          (((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b' g' (a' ≫ gXT) hbg'.symm).app
            K).symm ≪≫
            (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a' gXT (a' ≫ gXT) rfl).app K) ≪≫
        (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) ha'.toCommSq).app
          (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))).symm)
  · -- the derived base change map over `T` becomes an isomorphism after pullback along `a`
    have hII : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        (⟨by rw [Category.assoc, hX.w, ← Category.assoc, hb'.w, Category.assoc]⟩ :
          CommSq (b' ≫ g') jT' j (b ≫ g))).app K) :=
      (isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff hX.toCommSq hb'.toCommSq _ K i₁).2
        inferInstance
    have hI : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        (⟨by rw [Category.assoc, sqT.w, ← Category.assoc, ha'.w, Category.assoc]⟩ :
          CommSq (a' ≫ gXT) jT' j (a ≫ gT))).app K) :=
      (isIso_derivedBaseChangeMapPlus_app_congr hbg' hbg _ _ K).1 hII
    exact isIso_of_isIso_mapDerivedCategoryPlus_upperStar_map a _
      ((isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff sqT.toCommSq ha'.toCommSq _ K
        inferInstance).1 hI)

/-- Blueprint `lemma-universal-homeomorphism-base--1`: Descending the exchange property through a
universal homeomorphism, for a sheaf: the case of
`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_isFinite_of_surjective` for a sheaf
placed in degree `0`. -/
theorem HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective'
    {S S' X Y X' Y' : Scheme.{u}} (π : S' ⟶ S) [IsFinite π] [Surjective π]
    [UniversallyInjective π] (fY : Y ⟶ S) (j : X ⟶ Y) (g : Y' ⟶ Y)
    (fY' : Y' ⟶ S') (hY : IsPullback g fY' fY π) (g' : X' ⟶ X) (j' : X' ⟶ Y')
    (hX : IsPullback g' j' j g) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {U : Set S}
    (h : HasConstructibleDirectImageBaseChangeOn Λ fY' j'
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj F) (π ⁻¹' U)) :
    HasConstructibleDirectImageBaseChangeOn Λ fY j F U := by
  rw [hasConstructibleDirectImageBaseChangeOn_iff] at h ⊢
  exact HasDirectImageBaseChangeOnPlus.of_isFinite_of_surjective π fY j g fY' hY g' j' hX _
    (h.of_iso ((((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F).symm)

end Etale

end AlgebraicGeometry
