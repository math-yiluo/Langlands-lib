/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear

/-! # Evaluation of functions after a deck transformation -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

private theorem abstract_deck_counit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ D} {I : D ⥤ D}
    (af : F ⊣ G) (ag : H ⊣ I) (θ : F ≅ F ⋙ H) (M : D) (η : H.obj M ⟶ M) :
    F.map (G.map (ag.homEquiv _ _ η) ≫
      (conjugateIsoEquiv (af.comp ag) af θ).hom.app M) ≫ af.counit.app M =
    θ.hom.app (G.obj M) ≫ H.map (af.counit.app M) ≫ η := by
  have h := homEquiv_comp_conjugateEquiv_app (af.comp ag) af θ.hom
    (H.map (af.counit.app M) ≫ η)
  rw [Adjunction.comp_homEquiv] at h
  change af.homEquiv _ _ (ag.homEquiv _ _ (H.map (af.counit.app M) ≫ η)) ≫
      (conjugateEquiv (af.comp ag) af θ.hom).app M =
    af.homEquiv _ _ (θ.hom.app _ ≫ H.map (af.counit.app M) ≫ η) at h
  rw [ag.homEquiv_naturality_left, af.homEquiv_naturality_right] at h
  have hc : af.homEquiv _ _ (af.counit.app M) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact af.right_triangle_components M
  rw [hc, Category.id_comp] at h
  simp only [Functor.id_obj] at h
  calc
    _ = (af.homEquiv _ _).symm
        (G.map (ag.homEquiv _ _ η) ≫
          (conjugateEquiv (af.comp ag) af θ.hom).app M) :=
      (af.homEquiv_counit _ _ _).symm
    _ = _ := by rw [h, Equiv.symm_apply_apply]

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Pullback of regular sections by an endomorphism over the base.
Source: adjunction construction of deck pullback, latest blueprint
`prop-kernel-lisse.proof.md` (blueprint: lem-kernel-condensed-deck-evaluation). -/
def regularDeckEnd {X Y : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ X) (hg : g ≫ f = f) :
    End ((lowerStar Λ f).obj (Mod.regular (condensedRingObj Λ X))) :=
  End.of <| (lowerStar Λ f).map ((upperStarLowerStarAdjunction Λ g).homEquiv _ _
    (Functor.Monoidal.εIso (upperStar Λ g)).inv) ≫
      (lowerStarComp Λ g f).hom.app _ ≫ (lowerStarCongr Λ hg).hom.app _

private theorem deck_counit {X Y : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ X)
    (hg : g ≫ f = f) :
    (upperStar Λ f).map (regularDeckEnd Λ f g hg).asHom ≫
      (upperStarLowerStarAdjunction Λ f).counit.app (Mod.regular (condensedRingObj Λ X)) =
    stalkLowerStarProj Λ hg (Mod.regular (condensedRingObj Λ X)) ≫
      (Functor.Monoidal.εIso (upperStar Λ g)).inv := by
  let af := upperStarLowerStarAdjunction Λ f
  let ag := upperStarLowerStarAdjunction Λ g
  let ac := af.comp ag
  let θ : upperStar Λ f ≅ upperStar Λ f ⋙ upperStar Λ g :=
    upperStarCongr Λ hg.symm ≪≫ upperStarComp Λ g f
  have hθ : conjugateIsoEquiv ac af θ = lowerStarComp Λ g f ≪≫ lowerStarCongr Λ hg := by
    dsimp only [θ]
    rw [conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Λ (g ≫ f)) _,
      conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
      lowerStarCongr_symm]
  have h := abstract_deck_counit af ag θ (Mod.regular (condensedRingObj Λ X))
    (Functor.Monoidal.εIso (upperStar Λ g)).inv
  rw [hθ] at h
  simpa only [af, ag, regularDeckEnd, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    θ, stalkLowerStarProj_eq, Iso.app_hom, Mod.tensorUnit_eq_regular] using h

/-- Evaluating a regular pushforward section after a deck transformation is evaluation
on the translated sheet.

Source: latest blueprint `prop-kernel-lisse.proof.md`, translation of factors in the
splitting chart (blueprint: lem-kernel-condensed-deck-evaluation).

Proof. The conjugacy of the pullback and pushforward composition comparisons identifies
the adjoint of the deck pullback with evaluation on the corresponding sheet. Naturality
of the sheet projection moves the deck map inside pullback along any test map. The
composition formula for sheet evaluation and compatibility of the coefficient unit
comparisons then identify the result with evaluation on the composite sheet. -/
theorem regularDeckEnd_evaluation
    {X Y P : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ X) (hg : g ≫ f = f)
    (v : P ⟶ Y) (t : P ⟶ X) (ht : t ≫ f = v) :
    (upperStar Λ v).map (regularDeckEnd Λ f g hg).asHom ≫
        stalkLowerStarProj Λ ht (Mod.regular (condensedRingObj Λ X)) ≫
        (Functor.Monoidal.εIso (upperStar Λ t)).inv =
      stalkLowerStarProj Λ (show (t ≫ g) ≫ f = v by rw [Category.assoc, hg, ht])
        (Mod.regular (condensedRingObj Λ X)) ≫
          (Functor.Monoidal.εIso (upperStar Λ (t ≫ g))).inv := by
  let c := (upperStarCongr Λ ht.symm).hom.app
      ((lowerStar Λ f).obj (Mod.regular (condensedRingObj Λ X))) ≫
    (upperStarComp Λ t f).hom.app ((lowerStar Λ f).obj (Mod.regular (condensedRingObj Λ X)))
  have hn := (upperStarComp Λ t f).hom.naturality (regularDeckEnd Λ f g hg).asHom
  have hn' := (upperStarCongr Λ ht.symm).hom.naturality (regularDeckEnd Λ f g hg).asHom
  simp only [Functor.comp_map] at hn
  rw [stalkLowerStarProj_eq]
  simp only [Category.assoc]
  rw [reassoc_of% hn', reassoc_of% hn,
    ← Functor.map_comp_assoc, deck_counit, Functor.map_comp, Category.assoc]
  have hcomp := stalkLowerStarProj_comp_left Λ t hg
    (show (t ≫ g) ≫ f = t ≫ f by rw [Category.assoc, hg])
    (Mod.regular (condensedRingObj Λ X))
  have hp : (upperStarComp Λ t f).hom.app
        ((lowerStar Λ f).obj (Mod.regular (condensedRingObj Λ X))) ≫
      (upperStar Λ t).map (stalkLowerStarProj Λ hg
        (Mod.regular (condensedRingObj Λ X))) =
    stalkLowerStarProj Λ (show (t ≫ g) ≫ f = t ≫ f by rw [Category.assoc, hg])
      (Mod.regular (condensedRingObj Λ X)) ≫
        (upperStarComp Λ t g).hom.app (Mod.regular (condensedRingObj Λ X)) := by
    rw [hcomp]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  rw [reassoc_of% hp]
  have hu := upperStarComp_hom_app_unit Λ t g
  simp only [Mod.tensorUnit_eq_regular] at hu
  rw [hu]
  rw [upperStarCongr_hom_app_stalkLowerStarProj_assoc Λ ht.symm]

end AlgebraicGeometry.ProEtale.CondensedRing
