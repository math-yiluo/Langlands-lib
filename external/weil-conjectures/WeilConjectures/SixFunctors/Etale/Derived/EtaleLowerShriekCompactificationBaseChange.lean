/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification

/-!
# The candidate unit of the étale compactly supported direct image commutes with base change

Let `e : X ⟶ Y` be étale with a compactification `c = (X ⟶[j] Z ⟶[p] Y)`, and let
`g' ≫ e = e' ≫ g` be a cartesian square, with base-changed compactification `c'` of `e'`. The
candidate unit `η_c : 𝟭 ⟶ Le^* Rf_!(c)` (`AlgebraicGeometry.Etale.compactificationEtaleUnit`)
commutes with base change: `η_{c'}` at `Lg'^* N` is `Lg'^* η_c` followed by the canonical
isomorphism `Lg'^* Le^* ≅ Le'^* Lg^*` and `Le'^*` of the compact-support base change `Ex_!(c)`
(`AlgebraicGeometry.Etale.compactificationEtaleUnit_baseChange`).

The proof: proper base change on the cube of fibre products
`W' = Z' ×_{Y'} X' ⟶ W = Z ×_Y X` (`AlgebraicGeometry.Etale.derivedBaseChangeMap_cube`) reduces
it to the compatibility of the "restrict to the graph and extend by zero" maps with base change
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_clopenTransfer`), and then to the coherence
of the composition isomorphisms of the derived pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Compactification

variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y} {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e)

/-- The projection `Z' = Z ×_Y Y' ⟶ Z` of the base-changed compactification, typed with source
the scheme of `c.ofIsPullback sq`. -/
noncomputable abbrev ofIsPullbackFst : (c.ofIsPullback sq).Z ⟶ c.Z :=
  pullback.fst c.g g

/-- `AlgebraicGeometry.Compactification.isPullback_i_ofIsPullback`, with the projection typed by
`AlgebraicGeometry.Compactification.ofIsPullbackFst`. -/
lemma isPullback_i_ofIsPullback' :
    IsPullback g' (c.ofIsPullback sq).i c.i (c.ofIsPullbackFst sq) :=
  c.isPullback_i_ofIsPullback sq

/-- The fibre product square of the base-changed compactification, with its projection typed by
`AlgebraicGeometry.Compactification.ofIsPullbackFst`. -/
lemma isPullback_ofIsPullbackFst :
    IsPullback (c.ofIsPullbackFst sq) (c.ofIsPullback sq).g c.g g :=
  IsPullback.of_hasPullback c.g g

/-- The map `Z' ×_{Y'} X' ⟶ Z ×_Y X` between the fibre products attached to a compactification
and to its base change. -/
noncomputable def selfGraphBaseChange :
    pullback (c.ofIsPullback sq).g e' ⟶ pullback c.g e :=
  pullback.lift (pullback.fst _ _ ≫ c.ofIsPullbackFst sq) (pullback.snd _ _ ≫ g') (by
    have h₁ := pullback.condition (f := (c.ofIsPullback sq).g) (g := e')
    have h₂ := pullback.condition (f := c.g) (g := g)
    simp only [ofIsPullback_g] at h₁
    rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, Category.assoc, sq.w])

@[reassoc (attr := simp)]
lemma selfGraphBaseChange_fst :
    c.selfGraphBaseChange sq ≫ pullback.fst c.g e =
      pullback.fst (c.ofIsPullback sq).g e' ≫ c.ofIsPullbackFst sq :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma selfGraphBaseChange_snd :
    c.selfGraphBaseChange sq ≫ pullback.snd c.g e = pullback.snd (c.ofIsPullback sq).g e' ≫ g' :=
  pullback.lift_snd _ _ _

/-- The square `W' ⟶ W` over `g' : X' ⟶ X` is cartesian. -/
lemma isPullback_selfGraphBaseChange :
    IsPullback (c.selfGraphBaseChange sq) (pullback.snd (c.ofIsPullback sq).g e')
      (pullback.snd c.g e) g' := by
  have s := (IsPullback.of_hasPullback (c.ofIsPullback sq).g e').paste_horiz
    (IsPullback.of_hasPullback c.g g)
  rw [← selfGraphBaseChange_fst, ← sq.w] at s
  exact IsPullback.of_right s (selfGraphBaseChange_snd sq c) (IsPullback.of_hasPullback c.g e)

@[reassoc (attr := simp)]
lemma selfGraph_selfGraphBaseChange :
    (c.ofIsPullback sq).selfGraph ≫ c.selfGraphBaseChange sq = g' ≫ c.selfGraph := by
  ext
  · simp only [Category.assoc, selfGraphBaseChange_fst, selfGraph_fst_assoc, selfGraph_fst,
      ofIsPullback_i_fst]
  · simp only [Category.assoc, selfGraphBaseChange_snd, selfGraph_snd_assoc, selfGraph_snd,
      Category.comp_id]

/-- The graph of the base-changed compactification is the base change of the graph. -/
lemma isPullback_selfGraph :
    IsPullback g' (c.ofIsPullback sq).selfGraph c.selfGraph (c.selfGraphBaseChange sq) := by
  have s : IsPullback g' ((c.ofIsPullback sq).selfGraph ≫
      pullback.snd (c.ofIsPullback sq).g e') (c.selfGraph ≫ pullback.snd c.g e) g' := by
    rw [selfGraph_snd, selfGraph_snd]
    exact IsPullback.id_vert g'
  exact IsPullback.of_bot s (selfGraph_selfGraphBaseChange sq c).symm
    (isPullback_selfGraphBaseChange sq c)

end Compactification
namespace Etale

section Coherence

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The composite `Lf^* ⋙ L(a ≫ b)^* ⟶ ...` of composition isomorphisms does not depend on the
chosen composite `m = a ≫ b`. -/
lemma leftDerivedUpperStarComp_comp_map_congr {T S U R : Scheme.{u}} (f : T ⟶ S) (a : S ⟶ U)
    (b : U ⟶ R) (t : T ⟶ R) (m₁ m₂ : S ⟶ R) (h : m₁ = m₂) (p₁ : t = f ≫ m₁) (p₂ : t = f ≫ m₂)
    (q₁ : m₁ = a ≫ b) (q₂ : m₂ = a ≫ b)
    (K : _root_.DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A f m₁ t p₁).hom.app K ≫
        L((f)^*[A]).map ((leftDerivedUpperStarComp A a b m₁ q₁).hom.app K) =
      (leftDerivedUpperStarComp A f m₂ t p₂).hom.app K ≫
        L((f)^*[A]).map ((leftDerivedUpperStarComp A a b m₂ q₂).hom.app K) := by
  subst h
  rfl

/-- The square isomorphism of the derived pullbacks does not depend on the chosen composite. -/
lemma derivedSquareUpperStarIso_hom_app_eq {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) (d : X' ⟶ Y) (hd : d = g' ≫ f)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (derivedSquareUpperStarIso A sq).hom.app K =
      (leftDerivedUpperStarComp A f' g d (hd.trans sq.w)).inv.app K ≫
        (leftDerivedUpperStarComp A g' f d hd).hom.app K := by
  subst hd
  rfl

/-- **Coherence of the composition isomorphisms around an open piece**: the two identifications
`Lg'^* Lj^* ≅ Lσ'^* Lq_Z'^* Lgb^*` built from the faces of the commutative diagram
`j = σ ≫ q_Z`, `j' = σ' ≫ q_Z'`, `g' ≫ σ = σ' ≫ h`, `h ≫ q_Z = q_Z' ≫ gb` agree. -/
lemma leftDerivedUpperStarComp_square_coherence {X' X W' W Z' Z : Scheme.{u}} {g' : X' ⟶ X}
    {σ : X ⟶ W} {σ' : X' ⟶ W'} {h : W' ⟶ W} {qZ : W ⟶ Z} {qZ' : W' ⟶ Z'} {gb : Z' ⟶ Z}
    {j : X ⟶ Z} {j' : X' ⟶ Z'} (Sσ : CommSq g' σ' σ h) (S5 : CommSq h qZ' qZ gb)
    (Sj : CommSq g' j' j gb) (hj : j = σ ≫ qZ) (hj' : j' = σ' ≫ qZ')
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    L((g')^*[A]).map ((leftDerivedUpperStarComp A σ qZ j hj).hom.app M) ≫
        (derivedSquareUpperStarIso A Sσ).inv.app (L((qZ)^*[A]).obj M) ≫
        L((σ')^*[A]).map ((derivedSquareUpperStarIso A S5).inv.app M) =
      (derivedSquareUpperStarIso A Sj).inv.app M ≫
        (leftDerivedUpperStarComp A σ' qZ' j' hj').hom.app (L((gb)^*[A]).obj M) := by
  have ht₁ : g' ≫ j = (g' ≫ σ) ≫ qZ := by rw [hj, Category.assoc]
  have ht₂ : g' ≫ j = j' ≫ gb := Sj.w
  rw [← cancel_epi ((leftDerivedUpperStarComp A g' j (g' ≫ j) rfl).hom.app M)]
  simp only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [leftDerivedUpperStarComp_assoc'_app_assoc A g' σ qZ (g' ≫ σ) j (g' ≫ j) rfl hj ht₁,
    Iso.hom_inv_id_app_assoc,
    ← leftDerivedUpperStarComp_assoc'_app_assoc A σ' h qZ (g' ≫ σ) (h ≫ qZ) (g' ≫ j) Sσ.w rfl
      ht₁, ← Functor.map_comp_assoc (L((σ')^*[A])), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app_assoc,
    ← leftDerivedUpperStarComp_assoc'_app A σ' qZ' gb j' (qZ' ≫ gb) (g' ≫ j) hj' rfl ht₂]
  exact leftDerivedUpperStarComp_comp_map_congr A σ' qZ' gb (g' ≫ j) _ _ S5.w _ _ _ _ M

end Coherence

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Unfold

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)

omit [Finite Λ] [_root_.AlgebraicGeometry.Etale e] in
lemma compactificationEtaleGraphIso_hom_app
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    have : IsOpenImmersion c.i := c.isOpenImmersion
    (compactificationEtaleGraphIso Λ e c).hom.app N =
      (leftDerivedUpperStarCompSectionIso _ c.selfGraph (pullback.snd c.g e)
          c.selfGraph_snd).hom.app N ≫
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i).unit.app N ≫
        (leftDerivedUpperStarComp _ c.selfGraph (pullback.fst c.g e) c.i
          c.selfGraph_fst.symm).hom.app (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj N) := by
  simp only [compactificationEtaleGraphIso, Iso.trans_hom, NatTrans.comp_app, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.associator_inv_app]
  erw [Category.comp_id]

omit [Finite Λ] in
lemma compactificationEtaleGraphMap_app
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleGraphMap Λ e c).app N =
      clopenTransfer Λ ((compactificationEtaleGraphIso Λ e c).hom.app N) :=
  rfl

lemma compactificationEtaleUnit_app
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleUnit Λ e c).app N =
      (derivedUpperStarLowerStarAdjunction _ (pullback.snd c.g e)).unit.app N ≫
        R((pullback.snd c.g e)_*[ModuleCat.{u + 1} Λ]).map
          ((compactificationEtaleGraphMap Λ e c).app N) ≫
        inv ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (IsPullback.of_hasPullback c.g e).toCommSq).app
            (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj N)) := by
  simp only [compactificationEtaleUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    NatIso.isIso_inv_app]
  erw [Category.id_comp, Category.comp_id]

end Unfold

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y} {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e) [_root_.AlgebraicGeometry.Etale e]
  [_root_.AlgebraicGeometry.Etale e']

-- the derived functors involved are large terms
omit [Finite Λ] [_root_.AlgebraicGeometry.Etale e] [_root_.AlgebraicGeometry.Etale e'] in
/-- The coherence of the graph isomorphisms `Lq^* ⋙ Lσ^* ≅ Dj_! ⋙ Lq_Z^* ⋙ Lσ^*` with base
change. -/
lemma compactificationEtaleGraphIso_baseChange
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L(((c.ofIsPullback sq).selfGraph)^*[ModuleCat.{u + 1} Λ]).map
        ((derivedSquareUpperStarIso _ (c.isPullback_selfGraphBaseChange sq).toCommSq).hom.app N) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_selfGraph sq).toCommSq).hom.app
        (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} Λ]).obj N) ≫
      L((g')^*[ModuleCat.{u + 1} Λ]).map ((compactificationEtaleGraphIso Λ e c).hom.app N) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_selfGraph sq).toCommSq).inv.app
        (L((pullback.fst c.g e)^*[ModuleCat.{u + 1} Λ]).obj
          (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj N)) ≫
      L(((c.ofIsPullback sq).selfGraph)^*[ModuleCat.{u + 1} Λ]).map
        ((derivedSquareUpperStarIso _ (⟨c.selfGraphBaseChange_fst sq⟩ :
            CommSq (c.selfGraphBaseChange sq) (pullback.fst (c.ofIsPullback sq).g e')
              (pullback.fst c.g e) (c.ofIsPullbackFst sq))).inv.app
            (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj N) ≫
          L((pullback.fst (c.ofIsPullback sq).g e')^*[ModuleCat.{u + 1} Λ]).map
            ((derivedOpenImmersionLowerShriekBaseChangeIso _
              (c.isPullback_i_ofIsPullback' sq)).inv.app N)) =
    (compactificationEtaleGraphIso Λ e' (c.ofIsPullback sq)).hom.app
      (L((g')^*[ModuleCat.{u + 1} Λ]).obj N) := by
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsOpenImmersion (c.ofIsPullback sq).i := (c.ofIsPullback sq).isOpenImmersion
  -- the sections of `q` and `q'`
  have hpre := leftDerivedUpperStar_map_comp_compSectionIso (ModuleCat.{u + 1} Λ) g'
    (pullback.snd c.g e) (pullback.snd (c.ofIsPullback sq).g e') (c.selfGraphBaseChange sq)
    c.selfGraph (c.ofIsPullback sq).selfGraph (c.isPullback_selfGraphBaseChange sq).w
    (c.selfGraph_selfGraphBaseChange sq) c.selfGraph_snd (c.ofIsPullback sq).selfGraph_snd N
  rw [← derivedSquareUpperStarIso_hom_app_eq (ModuleCat.{u + 1} Λ)
    (c.isPullback_selfGraph sq).toCommSq _ (c.selfGraph_selfGraphBaseChange sq)] at hpre
  have hpre' : L(((c.ofIsPullback sq).selfGraph)^*[ModuleCat.{u + 1} Λ]).map
      ((derivedSquareUpperStarIso _ (c.isPullback_selfGraphBaseChange sq).toCommSq).hom.app N) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_selfGraph sq).toCommSq).hom.app
        (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} Λ]).obj N) ≫
      L((g')^*[ModuleCat.{u + 1} Λ]).map ((leftDerivedUpperStarCompSectionIso _ c.selfGraph
        (pullback.snd c.g e) c.selfGraph_snd).hom.app N) =
      (leftDerivedUpperStarCompSectionIso _ (c.ofIsPullback sq).selfGraph
        (pullback.snd (c.ofIsPullback sq).g e') (c.ofIsPullback sq).selfGraph_snd).hom.app
        (L((g')^*[ModuleCat.{u + 1} Λ]).obj N) := by
    exact (Iso.eq_inv_comp
      (L(((c.ofIsPullback sq).selfGraph)^*[ModuleCat.{u + 1} Λ]).mapIso
        ((derivedSquareUpperStarIso _ (c.isPullback_selfGraphBaseChange sq).toCommSq).app N))).1
      hpre.symm
  -- the open immersions `j` and `j'`
  have hJ := unit_map_derivedOpenImmersionLowerShriekBaseChangeIso' Λ
    (c.isPullback_i_ofIsPullback' sq) N
  have hpost := leftDerivedUpperStarComp_square_coherence (ModuleCat.{u + 1} Λ)
    (c.isPullback_selfGraph sq).toCommSq
    (⟨c.selfGraphBaseChange_fst sq⟩ : CommSq (c.selfGraphBaseChange sq)
      (pullback.fst (c.ofIsPullback sq).g e') (pullback.fst c.g e) (c.ofIsPullbackFst sq))
    (c.isPullback_i_ofIsPullback' sq).toCommSq c.selfGraph_fst.symm
    (c.ofIsPullback sq).selfGraph_fst.symm (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj N)
  have hnat := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq).selfGraph
    (pullback.fst (c.ofIsPullback sq).g e') (c.ofIsPullback sq).i
    (c.ofIsPullback sq).selfGraph_fst.symm).hom.naturality
      ((derivedOpenImmersionLowerShriekBaseChangeIso _ (c.isPullback_i_ofIsPullback' sq)).inv.app N)
  simp only [compactificationEtaleGraphIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  dsimp at hnat
  simp only [reassoc_of% hpre', reassoc_of% hpost, ← hnat, ← reassoc_of% hJ,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

omit [Finite Λ] in
/-- The "restrict to the graph and extend by zero" maps commute with base change. -/
lemma compactificationEtaleGraphMap_baseChange
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedSquareUpperStarIso _ (c.isPullback_selfGraphBaseChange sq).toCommSq).hom.app N ≫
      L((c.selfGraphBaseChange sq)^*[ModuleCat.{u + 1} Λ]).map
        ((compactificationEtaleGraphMap Λ e c).app N) ≫
      (derivedSquareUpperStarIso _ (⟨c.selfGraphBaseChange_fst sq⟩ :
          CommSq (c.selfGraphBaseChange sq) (pullback.fst (c.ofIsPullback sq).g e')
            (pullback.fst c.g e) (c.ofIsPullbackFst sq))).inv.app
          (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj N) ≫
      L((pullback.fst (c.ofIsPullback sq).g e')^*[ModuleCat.{u + 1} Λ]).map
        ((derivedOpenImmersionLowerShriekBaseChangeIso _
          (c.isPullback_i_ofIsPullback' sq)).inv.app N) =
    (compactificationEtaleGraphMap Λ e' (c.ofIsPullback sq)).app
      (L((g')^*[ModuleCat.{u + 1} Λ]).obj N) := by
  rw [compactificationEtaleGraphMap_app, compactificationEtaleGraphMap_app]
  rw [leftDerivedUpperStar_map_clopenTransfer Λ c.selfGraph (c.isPullback_selfGraph sq),
    ← clopenTransfer_comp]
  congr 1
  simp only [Category.assoc]
  exact compactificationEtaleGraphIso_baseChange Λ sq c N

omit [Finite Λ] [_root_.AlgebraicGeometry.Etale e] [_root_.AlgebraicGeometry.Etale e'] in
/-- The compact-support base change `Ex_!(c)` at `N`, with the squares of the base-changed
compactification typed by its scheme. -/
lemma rightDerivedLowerShriekOfCompactificationBaseChangeMap_app_eq
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c).app N =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (c.isPullback_ofIsPullbackFst sq).toCommSq).app
          (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj N) ≫
        R(((c.ofIsPullback sq).g)_*[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekBaseChangeIso _
            (c.isPullback_i_ofIsPullback' sq)).inv.app N) := by
  simp only [rightDerivedLowerShriekOfCompactificationBaseChangeMap, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp]
  erw [Category.comp_id]

-- the derived functors involved are large terms
/-- **The candidate unit of `Rf_!(c) ⊣ Le^*` commutes with base change**: for a cartesian square
`g' ≫ e = e' ≫ g` and the base change `c'` of the compactification `c`, the unit at
`Lg'^* N` for `c'` is `Lg'^*` of the unit at `N` for `c`, followed by the canonical isomorphism
`Lg'^* Le^* ≅ Le'^* Lg^*` and `Le'^*` of the compact-support base change `Ex_!(c)`. -/
theorem compactificationEtaleUnit_baseChange
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g')^*[ModuleCat.{u + 1} Λ]).map ((compactificationEtaleUnit Λ e c).app N) ≫
      (derivedSquareUpperStarIso _ sq.toCommSq).inv.app (Rf_!(c)[ModuleCat.{u + 1} Λ].obj N) ≫
      L((e')^*[ModuleCat.{u + 1} Λ]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq c).app N) =
    (compactificationEtaleUnit Λ e' (c.ofIsPullback sq)).app
      (L((g')^*[ModuleCat.{u + 1} Λ]).obj N) := by
  have hcube := derivedBaseChangeMap_cube (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback c.g e).toCommSq (c.isPullback_ofIsPullbackFst sq).toCommSq
    (c.isPullback_selfGraphBaseChange sq).toCommSq
    (IsPullback.of_hasPullback (c.ofIsPullback sq).g e').toCommSq sq.toCommSq
    (⟨c.selfGraphBaseChange_fst sq⟩ : CommSq (c.selfGraphBaseChange sq)
      (pullback.fst (c.ofIsPullback sq).g e') (pullback.fst c.g e) (c.ofIsPullbackFst sq))
    (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj N)
  have n₄ := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback (c.ofIsPullback sq).g e').toCommSq).naturality
      ((derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ)
        (c.isPullback_i_ofIsPullback' sq)).inv.app N)
  have n₃ := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (c.isPullback_selfGraphBaseChange sq).toCommSq).naturality
      ((compactificationEtaleGraphMap Λ e c).app N)
  have hu := map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} Λ)
    (c.isPullback_selfGraphBaseChange sq).toCommSq N
  dsimp at n₄ n₃ hu
  rw [compactificationEtaleUnit_app, compactificationEtaleUnit_app,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap_app_eq,
    ← cancel_mono ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback (c.ofIsPullback sq).g e').toCommSq).app _)]
  simp only [Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    Functor.comp_obj]
  rw [n₄, ← reassoc_of% hcube, ← Functor.map_comp_assoc (L((g')^*[ModuleCat.{u + 1} Λ]))
    (inv _), IsIso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% n₃, reassoc_of% hu, ← compactificationEtaleGraphMap_baseChange Λ sq c N]
  simp only [Functor.map_comp]

end BaseChange

end Etale

end AlgebraicGeometry
