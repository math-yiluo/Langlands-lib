/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-!
# Exchange morphisms are compatible with further base change

Consider a square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with exchange morphism `BC_sq : p^* Rg_* ⟶ Rh_* e^*` (`AlgebraicGeometry.Etale.baseChange`), and
a morphism `u : S' ⟶ S`. Pulling all four corners back along `u` gives a cube

```
Y' --e'--> T'            Y' --uY--> Y            T' --uT--> T
|          |             |          |            |          |
h'   sq'   g'            h'   bX    h            g'   bT    g
v          v             v          v            v          v
X' --p'--> S'            X' --uX--> X            S' --u---> S
```

whose top face `sq'` is the pulled-back square. Pasting the faces `bT` and `sq'`, and the faces
`sq` and `bX`, give the same composite square `Y' ⟶ T` over `X' ⟶ S`, so the pasting law
`AlgebraicGeometry.Etale.baseChange_app_paste_horiz_of_eq` computes its exchange morphism in two
ways (`AlgebraicGeometry.Etale.baseChange_app_cube`, blueprint
`corollary-open-direct-image-over-field--2`):

`p'^*(BC_bT) ≫ BC_sq'(uT^* K) = uX^*(BC_sq K) ≫ BC_bX(e^* K)`

modulo the composition isomorphisms of the pullbacks. Hence, if `BC_bT` and `BC_bX` are
isomorphisms (for instance if `u` is étale, or if the pushforward along `g` commutes with the
base change along `u`), the exchange morphism `BC_sq'` of the pulled-back square is an
isomorphism if and only if the pullback along `uX` of the original exchange morphism is
(`AlgebraicGeometry.Etale.isIso_baseChange_app_iff_of_cube`); when the pullback along `uX`
reflects isomorphisms (for instance `uX` surjective), this detects the invertibility of the
original exchange morphism. The same holds degreewise
(`AlgebraicGeometry.Etale.isIso_homology_baseChange_app_iff_of_cube`) and for the degree-`q`
base change maps of sheaves (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff_of_cube`,
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_cube`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X S T Y X' S' T' Y' : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
  {u : S' ⟶ S} {uT : T' ⟶ T} {uX : X' ⟶ X} {uY : Y' ⟶ Y} {g' : T' ⟶ S'} {p' : X' ⟶ S'}
  {e' : Y' ⟶ T'} {h' : Y' ⟶ X'}

/-- Blueprint `corollary-open-direct-image-over-field--2`: base change maps are compatible with
further base change.

For a square `sq` on `p : X ⟶ S` along `g : T ⟶ S` and a cube over `u : S' ⟶ S` with top face
`sq'` (the pulled-back square) and side faces `bT` (on `g` along `u`) and `bX` (on `h` along
`uX`), the pullback along `uX` of the exchange morphism of `sq`, followed by the exchange morphism
of `bX`, is the pullback along `p'` of the exchange morphism of `bT`, followed by the exchange
morphism of `sq'`, modulo the composition isomorphisms of the pullbacks: both are the exchange
morphism of the composite square `Y' ⟶ T` over `X' ⟶ S`. -/
theorem Etale.baseChange_app_cube (sq : CommSq e h g p) (bT : CommSq uT g' g u)
    (sq' : CommSq e' h' g' p') (bX : CommSq uY h' h uX) (hp : p' ≫ u = uX ≫ p)
    (he : e' ≫ uT = uY ≫ e)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) p' u (uX ≫ p) hp.symm).hom.app
          (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K) ≫
        ((p')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
          (((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) ≫
        ((h')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' uT (uY ≫ e)
            he.symm).inv.app K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) uX p).hom.app
          (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K) ≫
        ((uX)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) bX).app
          (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) ≫
        ((h')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) uY e).inv.app K) := by
  have big : CommSq (uY ≫ e) h' g (uX ≫ p) :=
    ⟨by rw [Category.assoc, sq.w, ← Category.assoc, bX.w, Category.assoc]⟩
  rw [← Etale.baseChange_app_paste_horiz_of_eq Λ bT sq' big he hp,
    ← Etale.baseChange_app_paste_horiz_of_eq Λ sq bX big rfl rfl]

/-- The arrow form of `AlgebraicGeometry.Etale.baseChange_app_cube`: if the exchange morphism of
the face `bT` is an isomorphism at `K`, then the exchange morphism of the pulled-back square `sq'`
at `uT^* K` is isomorphic, as an arrow, to the pullback along `uX` of the exchange morphism of
`sq` at `K` followed by the exchange morphism of the face `bX` at `e^* K`. -/
noncomputable def Etale.baseChangeCubeArrowIso (sq : CommSq e h g p) (bT : CommSq uT g' g u)
    (sq' : CommSq e' h' g' p') (bX : CommSq uY h' h uX) (hp : p' ≫ u = uX ≫ p)
    (he : e' ≫ uT = uY ≫ e)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K)] :
    Arrow.mk ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
        (((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) ≅
      Arrow.mk (((uX)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) bX).app
          (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) :=
  Arrow.isoMk
    ((((p')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.mapIso
        (asIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K))).symm ≪≫
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) p' u (uX ≫ p) hp.symm).app
        (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K)).symm ≪≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) uX p).app
        (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K))
    (((h')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
      (((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' uT (uY ≫ e) he.symm).app
        K).symm ≪≫ (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) uY e).app K)) (by
    have H := Etale.baseChange_app_cube Λ sq bT sq' bX hp he K
    simp only [Arrow.mk_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      asIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc, Functor.map_comp]
    rw [← cancel_epi (((p')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K)),
      ← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) p' u (uX ≫ p)
        hp.symm).hom.app (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K))]
    rw [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% H]
    simp [← Functor.map_comp])

/-- If the exchange morphisms of the faces `bT` and `bX` of the cube are isomorphisms (at `K` and
at `e^* K`), then the exchange morphism of the pulled-back square `sq'` at `uT^* K` is an
isomorphism if and only if the pullback along `uX` of the exchange morphism of `sq` at `K` is. -/
theorem Etale.isIso_baseChange_app_iff_of_cube (sq : CommSq e h g p) (bT : CommSq uT g' g u)
    (sq' : CommSq e' h' g' p') (bX : CommSq uY h' h uX) (hp : p' ≫ u = uX ≫ p)
    (he : e' ≫ uT = uY ≫ e)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K)]
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bX).app
      (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))] :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
        (((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) ↔
      IsIso (((uX)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K)) := by
  rw [Arrow.isIso_iff_isIso_of_isIso (Etale.baseChangeCubeArrowIso Λ sq bT sq' bX hp he K).hom]
  exact isIso_comp_right_iff _ _

/-- An exact functor reflecting isomorphisms induces a functor on the bounded below derived
categories reflecting isomorphisms. -/
lemma _root_.CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategoryPlus {C D : Type*}
    [Category* C] [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C]
    [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F.ReflectsIsomorphisms] :
    F.mapDerivedCategoryPlus.ReflectsIsomorphisms where
  reflects φ _ := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro n
    have : IsIso (F.map ((DerivedCategory.Plus.homologyFunctor C n).map φ)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryPlusHomologyFunctorIso n) φ).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ F

/-- **Detecting the invertibility of an exchange morphism after base change.** If the exchange
morphisms of the faces `bT` and `bX` of the cube are isomorphisms, the pullback along `uX`
reflects isomorphisms (for instance if `uX` is surjective,
`AlgebraicGeometry.Etale.reflectsIsomorphisms_upperStar_of_surjective`), and the exchange
morphism of the pulled-back square `sq'` is an isomorphism at `uT^* K`, then the exchange
morphism of `sq` is an isomorphism at `K`. -/
theorem Etale.isIso_baseChange_app_of_cube (sq : CommSq e h g p) (bT : CommSq uT g' g u)
    (sq' : CommSq e' h' g' p') (bX : CommSq uY h' h uX) (hp : p' ≫ u = uX ≫ p)
    (he : e' ≫ uT = uY ≫ e) [((uX)^*[ModuleCat.{u + 1} Λ]).ReflectsIsomorphisms]
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K)]
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bX).app
      (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))]
    (hK : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
        (((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) := by
  have := ((uX)^*[ModuleCat.{u + 1} Λ]).reflectsIsomorphisms_mapDerivedCategoryPlus
  have := (Etale.isIso_baseChange_app_iff_of_cube Λ sq bT sq' bX hp he K).1 hK
  exact isIso_of_reflects_iso _ ((uX)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus

/-- **Exchange isomorphisms are stable under base change** when the pushforwards commute with
it: if the exchange morphisms of the faces `bT` and `bX` of the cube are isomorphisms and the
exchange morphism of `sq` is an isomorphism at `K`, then so is the exchange morphism of the
pulled-back square `sq'` at `uT^* K`. -/
theorem Etale.isIso_baseChange_app_cube_of_isIso (sq : CommSq e h g p) (bT : CommSq uT g' g u)
    (sq' : CommSq e' h' g' p') (bX : CommSq uY h' h uX) (hp : p' ≫ u = uX ≫ p)
    (he : e' ≫ uT = uY ≫ e)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K)]
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) bX).app
      (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))]
    (hK : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K)) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
        (((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) :=
  (Etale.isIso_baseChange_app_iff_of_cube Λ sq bT sq' bX hp he K).2 inferInstance

/-- The degreewise form of `AlgebraicGeometry.Etale.isIso_baseChange_app_iff_of_cube`: if the
exchange morphisms of the faces `bT` and `bX` of the cube are isomorphisms on `q`-th cohomology
sheaves (at `K` and at `e^* K`), then the exchange morphism of the pulled-back square `sq'` at
`uT^* K` is an isomorphism on `q`-th cohomology sheaves if and only if the pullback along `uX` of
the `q`-th cohomology of the exchange morphism of `sq` at `K` is an isomorphism. -/
theorem Etale.isIso_homology_baseChange_app_iff_of_cube (sq : CommSq e h g p)
    (bT : CommSq uT g' g u) (sq' : CommSq e' h' g' p') (bX : CommSq uY h' h uX)
    (hp : p' ≫ u = uX ≫ p) (he : e' ≫ uT = uY ≫ e)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ)
    (hT : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K)))
    (hX : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) bX).app
        (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
          (((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) ↔
      IsIso (((uX)^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.homologyFunctor _ q).map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K))) := by
  have H := congrArg (DerivedCategory.Plus.homologyFunctor _ q).map
    (Etale.baseChange_app_cube Λ sq bT sq' bX hp he K)
  simp only [Functor.map_comp] at H
  have : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      (((p')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K))) :=
    (NatIso.isIso_map_iff (((p')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
      q) _).1 (by dsimp; infer_instance)
  refine Iff.trans ?_ ((NatIso.isIso_map_iff
    (((uX)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q) _).symm.trans
      Iff.rfl)
  rw [Functor.comp_map, ← isIso_comp_left_iff (f := (DerivedCategory.Plus.homologyFunctor _ q).map
      (((p')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) bT).app K))),
    ← isIso_comp_left_iff (f := (DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) p' u (uX ≫ p) hp.symm).hom.app
        (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K))),
    ← isIso_comp_right_iff _ ((DerivedCategory.Plus.homologyFunctor _ q).map
      (((h')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' uT (uY ≫ e)
          he.symm).inv.app K))), Category.assoc, Category.assoc, H,
    isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

section Sheaves

/- Generic forms of the identifications between components of natural transformations at
different but isomorphic objects, stated for abstract functors so that their instances at the
concrete derived functors are checked syntactically (as in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality`). -/
omit [CommRing Λ] in
private lemma isIso_map_app_comp_obj_iff {𝒜 ℬ ℬ' 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* ℬ'] [Category* 𝒞] [Category* 𝒟] (E₁ : 𝒜 ⥤ ℬ') (E₂ : ℬ' ⥤ ℬ) {P Q : ℬ ⥤ 𝒞}
    (α : P ⟶ Q) (Hh : 𝒞 ⥤ 𝒟) (Z : 𝒜) :
    IsIso (Hh.map (α.app ((E₁ ⋙ E₂).obj Z))) ↔ IsIso (Hh.map (α.app (E₂.obj (E₁.obj Z)))) :=
  Iff.rfl

omit [CommRing Λ] in
private lemma isIso_map_app_iff_of_iso {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* 𝒞] [Category* 𝒟] {E₁ E₂ : 𝒜 ⥤ ℬ} (ι : E₁ ≅ E₂) {P Q : ℬ ⥤ 𝒞} (α : P ⟶ Q)
    (Hh : 𝒞 ⥤ 𝒟) (Z : 𝒜) :
    IsIso (Hh.map (α.app (E₁.obj Z))) ↔ IsIso (Hh.map (α.app (E₂.obj Z))) :=
  NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight α Hh) (ι.app Z)

/-- The `q`-th cohomology of the exchange morphism of a square on `p'` along `g'` at the pullback
`uT^* F[0]` of a sheaf placed in degree `0` is an isomorphism if and only if the degree-`q` base
change map at `uT⁻¹ F` is. -/
private lemma isIso_baseChangeHomologyMap_upperStar_iff (sq' : IsPullback e' h' g' p') (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq' q ((uT)^*[ModuleCat.{u + 1} Λ].obj F)) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq'.toCommSq).app
          (((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  rw [Etale.isIso_baseChangeHomologyMap_iff]
  exact (isIso_map_app_comp_obj_iff (uT)^*[ModuleCat.{u + 1} Λ]
    (DerivedCategory.Plus.singleFunctor _ 0) _ _ F).symm.trans ((isIso_map_app_iff_of_iso
      ((((uT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)) _ _ _).symm.trans
      (isIso_map_app_comp_obj_iff _ _ _ _ _))

/-- Blueprint `corollary-open-direct-image-over-field--2`, for the degree-`q` base change maps of a
sheaf `F`: in a cube of cartesian squares over `u : S' ⟶ S` as in
`AlgebraicGeometry.Etale.baseChange_app_cube`, if the degree-`q` base change maps of the faces `bT`
(at `F`) and `bX` (at `e⁻¹ F`) are isomorphisms, then the degree-`q` base change map
`p'⁻¹ R^q g'_* (uT⁻¹ F) ⟶ R^q h'_* e'⁻¹ uT⁻¹ F` of the pulled-back square is an isomorphism if and
only if the pullback along `uX` of the base change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of the
original square is. -/
theorem Etale.isIso_baseChangeHomologyMap_iff_of_cube (sq : IsPullback e h g p)
    (bT : IsPullback uT g' g u) (sq' : IsPullback e' h' g' p') (bX : IsPullback uY h' h uX)
    (hp : p' ≫ u = uX ≫ p) (he : e' ≫ uT = uY ≫ e) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hT : IsIso (Etale.baseChangeHomologyMap Λ bT q F))
    (hX : IsIso (Etale.baseChangeHomologyMap Λ bX q ((e)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq' q ((uT)^*[ModuleCat.{u + 1} Λ].obj F)) ↔
      IsIso ((uX)^*[ModuleCat.{u + 1} Λ].map (Etale.baseChangeHomologyMap Λ sq q F)) := by
  rw [isIso_baseChangeHomologyMap_upperStar_iff]
  rw [Etale.isIso_baseChangeHomologyMap_iff] at hT
  rw [isIso_baseChangeHomologyMap_upperStar_iff] at hX
  exact Etale.isIso_homology_baseChange_app_iff_of_cube Λ sq.toCommSq bT.toCommSq sq'.toCommSq
    bX.toCommSq hp he _ q hT hX

/-- **Detecting degree-`q` base change after a further base change.** In a cube of cartesian
squares over `u : S' ⟶ S`, if the degree-`q` base change maps of the faces `bT` and `bX` are
isomorphisms, the pullback along `uX` reflects isomorphisms, and the degree-`q` base change map of
the pulled-back square at `uT⁻¹ F` is an isomorphism, then so is the degree-`q` base change map
of the original square at `F`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_cube (sq : IsPullback e h g p)
    (bT : IsPullback uT g' g u) (sq' : IsPullback e' h' g' p') (bX : IsPullback uY h' h uX)
    (hp : p' ≫ u = uX ≫ p) (he : e' ≫ uT = uY ≫ e)
    [(uX)^*[ModuleCat.{u + 1} Λ].ReflectsIsomorphisms]
    (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hT : IsIso (Etale.baseChangeHomologyMap Λ bT q F))
    (hX : IsIso (Etale.baseChangeHomologyMap Λ bX q ((e)^*[ModuleCat.{u + 1} Λ].obj F)))
    (hF : IsIso (Etale.baseChangeHomologyMap Λ sq' q ((uT)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  have := (Etale.isIso_baseChangeHomologyMap_iff_of_cube Λ sq bT sq' bX hp he q F hT hX).1 hF
  isIso_of_reflects_iso _ (uX)^*[ModuleCat.{u + 1} Λ]

/-- The form of `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_cube` for a surjective
`uX`, the pullback along which reflects isomorphisms. -/
theorem Etale.isIso_baseChangeHomologyMap_of_cube_of_surjective (sq : IsPullback e h g p)
    (bT : IsPullback uT g' g u) (sq' : IsPullback e' h' g' p') (bX : IsPullback uY h' h uX)
    (hp : p' ≫ u = uX ≫ p) (he : e' ≫ uT = uY ≫ e) (huX : Function.Surjective uX.base)
    (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hT : IsIso (Etale.baseChangeHomologyMap Λ bT q F))
    (hX : IsIso (Etale.baseChangeHomologyMap Λ bX q ((e)^*[ModuleCat.{u + 1} Λ].obj F)))
    (hF : IsIso (Etale.baseChangeHomologyMap Λ sq' q ((uT)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  have := Etale.reflectsIsomorphisms_upperStar_of_surjective Λ uX huX
  Etale.isIso_baseChangeHomologyMap_of_cube Λ sq bT sq' bX hp he q F hT hX hF

/-- **Stability of degree-`q` base change under a further base change** commuting with the
pushforwards: in a cube of cartesian squares over `u : S' ⟶ S`, if the degree-`q` base change
maps of the faces `bT` and `bX` and of the original square at `F` are isomorphisms, then so is
the degree-`q` base change map of the pulled-back square at `uT⁻¹ F`. -/
theorem Etale.isIso_baseChangeHomologyMap_cube_of_isIso (sq : IsPullback e h g p)
    (bT : IsPullback uT g' g u) (sq' : IsPullback e' h' g' p') (bX : IsPullback uY h' h uX)
    (hp : p' ≫ u = uX ≫ p) (he : e' ≫ uT = uY ≫ e)
    (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hT : IsIso (Etale.baseChangeHomologyMap Λ bT q F))
    (hX : IsIso (Etale.baseChangeHomologyMap Λ bX q ((e)^*[ModuleCat.{u + 1} Λ].obj F)))
    (hF : IsIso (Etale.baseChangeHomologyMap Λ sq q F)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq' q ((uT)^*[ModuleCat.{u + 1} Λ].obj F)) :=
  (Etale.isIso_baseChangeHomologyMap_iff_of_cube Λ sq bT sq' bX hp he q F hT hX).2 inferInstance

end Sheaves

end AlgebraicGeometry
