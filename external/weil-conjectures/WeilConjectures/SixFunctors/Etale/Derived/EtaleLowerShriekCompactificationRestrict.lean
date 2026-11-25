/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationBaseChange

/-!
# The candidate unit of the étale compactly supported direct image under restriction

Let `e : X ⟶ Y` be étale with a compactification `c = (X ⟶[j] Z ⟶[p] Y)`, and let
`v : X₀ ⟶ X` be an open immersion, so that `c₀ = (X₀ ⟶[v ≫ j] Z ⟶[p] Y)` is a compactification
of `v ≫ e` (`AlgebraicGeometry.Compactification.restrictOpen`). The candidate unit
`η_{c₀} : 𝟭 ⟶ L(v ≫ e)^* Rf_!(c₀)` (`AlgebraicGeometry.Etale.compactificationEtaleUnit`) is the
restriction along `v` of `η_c` at `Dv_! N₀`
(`AlgebraicGeometry.Etale.compactificationEtaleUnit_precomp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Compactification

variable {X Y X₀ : Scheme.{u}} {e : X ⟶ Y} (c : Compactification e) (v : X₀ ⟶ X)
  [IsOpenImmersion v]

/-- The compactification `X₀ ⟶[v ≫ j] Z ⟶[p] Y` of `v ≫ e` for an open immersion `v`: the
same as `AlgebraicGeometry.Compactification.precomp`, with reducible fields. -/
abbrev restrictOpen : Compactification (v ≫ e) where
  Z := c.Z
  g := c.g
  i := v ≫ c.i
  comm := by rw [Category.assoc, ← c.comm]
  isProper := c.isProper
  isOpenImmersion := have := c.isOpenImmersion; inferInstance

/-- The open immersion `Z ×_Y X₀ ⟶ Z ×_Y X` induced by `v : X₀ ⟶ X`. -/
noncomputable def selfGraphRestrict : pullback (c.restrictOpen v).g (v ≫ e) ⟶ pullback c.g e :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ v) (by
    rw [Category.assoc, ← pullback.condition])

@[reassoc (attr := simp)]
lemma selfGraphRestrict_fst :
    c.selfGraphRestrict v ≫ pullback.fst c.g e = pullback.fst (c.restrictOpen v).g (v ≫ e) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma selfGraphRestrict_snd :
    c.selfGraphRestrict v ≫ pullback.snd c.g e = pullback.snd (c.restrictOpen v).g (v ≫ e) ≫ v :=
  pullback.lift_snd _ _ _

/-- The square `Z ×_Y X₀ ⟶ Z ×_Y X` over `v` is cartesian. -/
lemma isPullback_selfGraphRestrict :
    IsPullback (c.selfGraphRestrict v) (pullback.snd (c.restrictOpen v).g (v ≫ e))
      (pullback.snd c.g e) v := by
  have s : IsPullback (c.selfGraphRestrict v ≫ pullback.fst c.g e)
      (pullback.snd (c.restrictOpen v).g (v ≫ e)) c.g (v ≫ e) := by
    rw [selfGraphRestrict_fst]
    exact IsPullback.of_hasPullback (c.restrictOpen v).g (v ≫ e)
  exact IsPullback.of_right s (selfGraphRestrict_snd c v) (IsPullback.of_hasPullback c.g e)

@[reassoc (attr := simp)]
lemma selfGraph_restrictOpen_selfGraphRestrict :
    (c.restrictOpen v).selfGraph ≫ c.selfGraphRestrict v = v ≫ c.selfGraph := by
  ext
  · simp only [Category.assoc, selfGraphRestrict_fst, selfGraph_fst]
  · simp only [Category.assoc, selfGraphRestrict_snd, selfGraph_snd_assoc, selfGraph_snd,
      Category.comp_id]

/-- The graph of `c.restrictOpen v` is the restriction of the graph of `c`. -/
lemma isPullback_selfGraph_restrictOpen :
    IsPullback v (c.restrictOpen v).selfGraph c.selfGraph (c.selfGraphRestrict v) := by
  have s : IsPullback v ((c.restrictOpen v).selfGraph ≫ pullback.snd (c.restrictOpen v).g (v ≫ e))
      (c.selfGraph ≫ pullback.snd c.g e) v := by
    rw [selfGraph_snd, selfGraph_snd]
    exact IsPullback.id_vert v
  exact IsPullback.of_bot s (selfGraph_restrictOpen_selfGraphRestrict c v).symm
    (isPullback_selfGraphRestrict c v)

end Compactification
namespace Etale

section Coherence

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **Coherence of the composition isomorphisms around an open piece, restricted along an open
subscheme**: the variant of `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_square_coherence`
where the base `Z` does not move. -/
lemma leftDerivedUpperStarComp_triangle_coherence {X₀ X W₀ W Z : Scheme.{u}} {v : X₀ ⟶ X}
    {σ : X ⟶ W} {σ₀ : X₀ ⟶ W₀} {h₀ : W₀ ⟶ W} {qZ : W ⟶ Z} {qZ₀ : W₀ ⟶ Z} {j : X ⟶ Z}
    {j₀ : X₀ ⟶ Z} (Sσ : CommSq v σ₀ σ h₀) (h5 : qZ₀ = h₀ ≫ qZ) (hj : j = σ ≫ qZ)
    (hj₀ : j₀ = σ₀ ≫ qZ₀) (hjv : j₀ = v ≫ j)
    (T : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    L((v)^*[A]).map ((leftDerivedUpperStarComp A σ qZ j hj).hom.app T) ≫
        (derivedSquareUpperStarIso A Sσ).inv.app (L((qZ)^*[A]).obj T) ≫
        L((σ₀)^*[A]).map ((leftDerivedUpperStarComp A h₀ qZ qZ₀ h5).inv.app T) =
      (leftDerivedUpperStarComp A v j j₀ hjv).inv.app T ≫
        (leftDerivedUpperStarComp A σ₀ qZ₀ j₀ hj₀).hom.app T := by
  have ht₁ : j₀ = (v ≫ σ) ≫ qZ := by rw [hjv, hj, Category.assoc]
  rw [← cancel_epi ((leftDerivedUpperStarComp A v j j₀ hjv).hom.app T),
    Iso.hom_inv_id_app_assoc]
  simp only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Category.assoc]
  rw [leftDerivedUpperStarComp_assoc'_app_assoc A v σ qZ (v ≫ σ) j j₀ rfl hj ht₁,
    Iso.hom_inv_id_app_assoc,
    ← leftDerivedUpperStarComp_assoc'_app_assoc A σ₀ h₀ qZ (v ≫ σ) qZ₀ j₀ Sσ.w h5 ht₁,
    ← Functor.map_comp (L((σ₀)^*[A])), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end Coherence

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Restrict

attribute [local instance] Compactification.isOpenImmersion

variable {X Y X₀ : Scheme.{u}} {e : X ⟶ Y} (c : Compactification e) (v : X₀ ⟶ X)
  [IsOpenImmersion v] [_root_.AlgebraicGeometry.Etale e]

/-- The composition isomorphism `D((v ≫ j)_!) ≅ Dv_! ⋙ Dj_!` of the derived extensions by zero,
as the comparison of left adjoints of `L(v ≫ j)^* ≅ Lj^* ⋙ Lv^*`. -/
noncomputable def restrictOpenLowerShriekIso :
    D(((c.restrictOpen v).i)_!open[ModuleCat.{u + 1} Λ]) ≅
      D((v)_!open[ModuleCat.{u + 1} Λ]) ⋙ D((c.i)_!open[ModuleCat.{u + 1} Λ]) :=
  Adjunction.leftAdjointUniq
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (c.restrictOpen v).i)
    (((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ v).comp
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i)).ofNatIsoRight
        (leftDerivedUpperStarComp _ v c.i (c.restrictOpen v).i rfl).symm)

omit [Finite Λ] [_root_.AlgebraicGeometry.Etale e] in
/-- The unit property of `AlgebraicGeometry.Etale.restrictOpenLowerShriekIso`. -/
lemma unit_map_restrictOpenLowerShriekIso
    (N : _root_.DerivedCategory (Sheaf X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (c.restrictOpen v).i).unit.app
        N ≫
        L(((c.restrictOpen v).i)^*[ModuleCat.{u + 1} Λ]).map
          ((restrictOpenLowerShriekIso Λ c v).hom.app N) =
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ v).unit.app N ≫
        L((v)^*[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i).unit.app
            (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) ≫
        (leftDerivedUpperStarComp _ v c.i (c.restrictOpen v).i rfl).inv.app _ := by
  rw [restrictOpenLowerShriekIso, Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Adjunction.comp_unit_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
  rfl

-- the derived functors involved are large terms
omit [Finite Λ] [_root_.AlgebraicGeometry.Etale e] in
/-- The coherence of the graph isomorphisms `Lq^* ⋙ Lσ^* ≅ Dj_! ⋙ Lq_Z^* ⋙ Lσ^*` with the
restriction along `v`. -/
lemma compactificationEtaleGraphIso_restrictOpen
    (N : _root_.DerivedCategory (Sheaf X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleGraphIso Λ (v ≫ e) (c.restrictOpen v)).hom.app N ≫
      L(((c.restrictOpen v).selfGraph)^*[ModuleCat.{u + 1} Λ]).map
        (L((pullback.fst (c.restrictOpen v).g (v ≫ e))^*[ModuleCat.{u + 1} Λ]).map
          ((restrictOpenLowerShriekIso Λ c v).hom.app N)) =
    L(((c.restrictOpen v).selfGraph)^*[ModuleCat.{u + 1} Λ]).map
        (L((pullback.snd (c.restrictOpen v).g (v ≫ e))^*[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ v).unit.app N) ≫
        (derivedSquareUpperStarIso _ (c.isPullback_selfGraphRestrict v).toCommSq).hom.app
          (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_selfGraph_restrictOpen v).toCommSq).hom.app
        (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} Λ]).obj
          (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) ≫
      L((v)^*[ModuleCat.{u + 1} Λ]).map ((compactificationEtaleGraphIso Λ e c).hom.app
        (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_selfGraph_restrictOpen v).toCommSq).inv.app
        (L((pullback.fst c.g e)^*[ModuleCat.{u + 1} Λ]).obj
          (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N))) ≫
      L(((c.restrictOpen v).selfGraph)^*[ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarComp _ (c.selfGraphRestrict v) (pullback.fst c.g e)
          (pullback.fst (c.restrictOpen v).g (v ≫ e)) (c.selfGraphRestrict_fst v).symm).inv.app
            (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj
              (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N))) := by
  -- the sections of `q` and `q₀`
  have hpre := leftDerivedUpperStar_map_comp_compSectionIso (ModuleCat.{u + 1} Λ) v
    (pullback.snd c.g e) (pullback.snd (c.restrictOpen v).g (v ≫ e)) (c.selfGraphRestrict v)
    c.selfGraph (c.restrictOpen v).selfGraph (c.isPullback_selfGraphRestrict v).w
    (c.selfGraph_restrictOpen_selfGraphRestrict v) c.selfGraph_snd
    (c.restrictOpen v).selfGraph_snd (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)
  rw [← derivedSquareUpperStarIso_hom_app_eq (ModuleCat.{u + 1} Λ)
    (c.isPullback_selfGraph_restrictOpen v).toCommSq _
      (c.selfGraph_restrictOpen_selfGraphRestrict v)] at hpre
  have hpre' : L(((c.restrictOpen v).selfGraph)^*[ModuleCat.{u + 1} Λ]).map
      ((derivedSquareUpperStarIso _ (c.isPullback_selfGraphRestrict v).toCommSq).hom.app
        (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_selfGraph_restrictOpen v).toCommSq).hom.app
        (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} Λ]).obj
          (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) ≫
      L((v)^*[ModuleCat.{u + 1} Λ]).map ((leftDerivedUpperStarCompSectionIso _ c.selfGraph
        (pullback.snd c.g e) c.selfGraph_snd).hom.app (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) =
      (leftDerivedUpperStarCompSectionIso _ (c.restrictOpen v).selfGraph
        (pullback.snd (c.restrictOpen v).g (v ≫ e)) (c.restrictOpen v).selfGraph_snd).hom.app
        (L((v)^*[ModuleCat.{u + 1} Λ]).obj (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) := by
    exact (Iso.eq_inv_comp
      (L(((c.restrictOpen v).selfGraph)^*[ModuleCat.{u + 1} Λ]).mapIso
        ((derivedSquareUpperStarIso _ (c.isPullback_selfGraphRestrict v).toCommSq).app
          (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)))).1 hpre.symm
  -- the open immersions `j` and `v ≫ j`
  have hθ := unit_map_restrictOpenLowerShriekIso Λ c v N
  have hpost := leftDerivedUpperStarComp_triangle_coherence (ModuleCat.{u + 1} Λ)
    (c.isPullback_selfGraph_restrictOpen v).toCommSq (c.selfGraphRestrict_fst v).symm
    c.selfGraph_fst.symm (c.restrictOpen v).selfGraph_fst.symm rfl
    (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N))
  have hnat := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (c.restrictOpen v).selfGraph
    (pullback.fst (c.restrictOpen v).g (v ≫ e)) (c.restrictOpen v).i
    (c.restrictOpen v).selfGraph_fst.symm).hom.naturality
      ((restrictOpenLowerShriekIso Λ c v).hom.app N)
  have hsec := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ)
    (c.restrictOpen v).selfGraph (pullback.snd (c.restrictOpen v).g (v ≫ e))
    (c.restrictOpen v).selfGraph_snd).hom.naturality
      ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ v).unit.app N)
  dsimp at hnat hsec
  simp only [compactificationEtaleGraphIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  simp only [reassoc_of% hpre']
  simp only [hpost]
  simp only [← hnat]
  simp only [reassoc_of% hθ]
  simp only [reassoc_of% hsec]

omit [Finite Λ] in
/-- The "restrict to the graph and extend by zero" maps commute with restriction along `v`. -/
lemma compactificationEtaleGraphMap_restrictOpen
    (N : _root_.DerivedCategory (Sheaf X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleGraphMap Λ (v ≫ e) (c.restrictOpen v)).app N ≫
      L((pullback.fst (c.restrictOpen v).g (v ≫ e))^*[ModuleCat.{u + 1} Λ]).map
        ((restrictOpenLowerShriekIso Λ c v).hom.app N) =
    L((pullback.snd (c.restrictOpen v).g (v ≫ e))^*[ModuleCat.{u + 1} Λ]).map
        ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ v).unit.app N) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_selfGraphRestrict v).toCommSq).hom.app
        (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N) ≫
      L((c.selfGraphRestrict v)^*[ModuleCat.{u + 1} Λ]).map
        ((compactificationEtaleGraphMap Λ e c).app (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) ≫
      (leftDerivedUpperStarComp _ (c.selfGraphRestrict v) (pullback.fst c.g e)
          (pullback.fst (c.restrictOpen v).g (v ≫ e)) (c.selfGraphRestrict_fst v).symm).inv.app
        (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) := by
  simp only [compactificationEtaleGraphMap_app]
  simp only [leftDerivedUpperStar_map_clopenTransfer Λ c.selfGraph
      (c.isPullback_selfGraph_restrictOpen v)]
  simp only [← clopenTransfer_comp_left, ← clopenTransfer_comp_right]
  congr 1
  have h := compactificationEtaleGraphIso_restrictOpen Λ c v N
  simp only [Functor.map_comp, Category.assoc, Functor.comp_obj] at h ⊢
  exact h

-- the derived functors involved are large terms
/-- **The candidate unit of `Rf_!(c) ⊣ Le^*` under restriction to an open subscheme**: for an
open immersion `v : X₀ ⟶ X`, the unit for the compactification `c₀` of `v ≫ e` at `N₀` is, up
to `D(v ≫ j)_! ≅ Dv_! ⋙ Dj_!`, the unit of `Dv_! ⊣ Lv^*` followed by `Lv^*` of the unit for `c`
at `Dv_! N₀`. -/
theorem compactificationEtaleUnit_restrictOpen
    (N : _root_.DerivedCategory (Sheaf X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleUnit Λ (v ≫ e) (c.restrictOpen v)).app N ≫
      L((v ≫ e)^*[ModuleCat.{u + 1} Λ]).map
        (R((c.g)_*[ModuleCat.{u + 1} Λ]).map ((restrictOpenLowerShriekIso Λ c v).hom.app N)) =
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ v).unit.app N ≫
      L((v)^*[ModuleCat.{u + 1} Λ]).map ((compactificationEtaleUnit Λ e c).app
        (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) ≫
      (leftDerivedUpperStarComp _ v e (v ≫ e) rfl).inv.app
        (Rf_!(c)[ModuleCat.{u + 1} Λ].obj (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)) := by
  have hpaste := derivedBaseChangeMap_paste (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback c.g e).toCommSq (c.isPullback_selfGraphRestrict v).toCommSq
    (IsPullback.of_hasPullback (c.restrictOpen v).g (v ≫ e)).toCommSq
    (c.selfGraphRestrict_fst v).symm rfl
    (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N))
  have hκ := compactificationEtaleGraphMap_restrictOpen Λ c v N
  have n₁ := (inv (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback (c.restrictOpen v).g (v ≫ e)).toCommSq)).naturality
      ((restrictOpenLowerShriekIso Λ c v).hom.app N)
  have n₃ := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (c.isPullback_selfGraphRestrict v).toCommSq).naturality
      ((compactificationEtaleGraphMap Λ e c).app (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N))
  have hu := map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} Λ)
    (c.isPullback_selfGraphRestrict v).toCommSq (D((v)_!open[ModuleCat.{u + 1} Λ]).obj N)
  have hη := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.snd (c.restrictOpen v).g (v ≫ e))).unit.naturality
      ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ v).unit.app N)
  dsimp at n₁ n₃ hu hη
  simp only [compactificationEtaleUnit_app]
  rw [← cancel_mono ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback (c.restrictOpen v).g (v ≫ e)).toCommSq).app _)]
  have hκ' := congrArg
    (R((pullback.snd (c.restrictOpen v).g (v ≫ e))_*[ModuleCat.{u + 1} Λ]).map) hκ
  simp only [Functor.map_comp] at hκ'
  simp only [Functor.comp_obj, Functor.map_comp, Category.assoc] at hpaste ⊢
  simp only [NatIso.isIso_inv_app] at n₁
  simp only [← reassoc_of% n₁, IsIso.inv_hom_id, Category.comp_id]
  simp only [← hpaste, Iso.inv_hom_id_app_assoc, Functor.map_inv, IsIso.inv_hom_id_assoc]
  simp only [reassoc_of% n₃, reassoc_of% hu, reassoc_of% hη, hκ']

end Restrict

end Etale

end AlgebraicGeometry
