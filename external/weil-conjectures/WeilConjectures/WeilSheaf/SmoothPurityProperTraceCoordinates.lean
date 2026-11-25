/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityProperRelativeTrace
public import WeilConjectures.Tactic.ExactModProofs

/-!
# Proper trace in the levelwise pullback coordinates

Descent uses the derived functor of an exact pullback, while exceptional base
change uses its total left derived functor. Their comparison transports the
universal property of the smooth proper trace.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- Transport of an inverse only requires the equality of the forward maps. -/
lemma Functor.map_iso_inv_eq_of_map_hom_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (e : X ≅ Y) (e' : F.obj X ≅ F.obj Y)
    (h : F.map e.hom = e'.hom) : F.map e.inv = e'.inv := by
  apply (cancel_mono e'.hom).1
  calc
    F.map e.inv ≫ e'.hom = F.map e.inv ≫ F.map e.hom := by rw [h]
    _ = F.map (e.inv ≫ e.hom) := (F.map_comp _ _).symm
    _ = 𝟙 _ := by rw [Iso.inv_hom_id, F.map_id]
    _ = e'.inv ≫ e'.hom := e'.inv_hom_id.symm

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Restriction to full subcategories preserves the inverse exchange component. -/
lemma NearbyCyclesModel.liftExchange_inv_app_hom
    {DY DX DY' DX' : Type*} [Category DY] [Category DX] [Category DY'] [Category DX']
    {PY : ObjectProperty DY} {PX : ObjectProperty DX}
    {PY' : ObjectProperty DY'} {PX' : ObjectProperty DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'} {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'}
    (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf') [IsIso χ]
    (hR : ∀ Z : PX.FullSubcategory, PY ((PX.ι ⋙ Rf).obj Z))
    (hR' : ∀ Z : PX'.FullSubcategory, PY' ((PX'.ι ⋙ Rf').obj Z))
    (hN : ∀ Z : PY.FullSubcategory, PY' ((PY.ι ⋙ ΨN).obj Z))
    (hM : ∀ Z : PX.FullSubcategory, PX' ((PX.ι ⋙ ΨM).obj Z))
    [IsIso (NearbyCyclesModel.liftExchange χ hR hR' hN hM)] (Z : PX.FullSubcategory) :
    ((asIso (NearbyCyclesModel.liftExchange χ hR hR' hN hM)).inv.app Z).hom =
      (asIso χ).inv.app Z.obj := by
  apply Functor.map_iso_inv_eq_of_map_hom_eq PY'.ι
    ((asIso (NearbyCyclesModel.liftExchange χ hR hR' hN hM)).app Z)
    ((asIso χ).app Z.obj)
  exact NearbyCyclesModel.liftExchange_app_hom χ hR hR' hN hM Z

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y') [IsProper f.left] [IsProper f'.left]
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}
  (sq : IsPullback πX f'.left f.left πY) [WeaklyEtale πY] [WeaklyEtale πX]

omit [IsProper f'.left] in
/-- The bounded-constructible base-change inverse has the specified ambient inverse. -/
lemma boundedConstructibleBaseChangeOfMap_inv_app_hom
    (P : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧) :
    have := isIso_boundedConstructibleBaseChangeOfMap l sq
    have := isIso_baseChangeMap_of_weaklyEtale (Profinite.padicAlgClRingObj l) sq
    ((asIso (boundedConstructibleBaseChangeOfMap l sq.toCommSq)).inv.app P).hom =
      (asIso (baseChangeMap (Profinite.padicAlgClRingObj l) sq.toCommSq)).inv.app P.obj := by
  have hbcIso := isIso_boundedConstructibleBaseChangeOfMap l sq
  have := isIso_baseChangeMap_of_weaklyEtale (Profinite.padicAlgClRingObj l) sq
  dsimp only [boundedConstructibleBaseChangeOfMap] at hbcIso ⊢
  exact NearbyCyclesModel.liftExchange_inv_app_hom
    (baseChangeMap (Profinite.padicAlgClRingObj l) sq.toCommSq)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj l f K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj l f' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πY K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πX K.obj K.property) P

variable {P : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧}
  {N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧}
  (γ : P ⟶ (boundedConstructibleUpperShriek l f).obj N)

omit [IsProper f'.left] in
/-- Convert the ordinary trace to the levelwise pullback coordinates used by descent. -/
lemma baseChangedProperTrace_levelwise :
    (rightDerivedLowerStarBaseChangeIso (Profinite.padicAlgClRingObj l) sq).inv.app P.obj ≫
      (upperStar (Profinite.padicAlgClRingObj l) πY).mapDerivedCategory.map
        (((boundedConstructibleLowerStar l f).map γ ≫
          (lowerStarUpperShriekAdjunction l f).counit.app N).hom) =
    (lowerStar (Profinite.padicAlgClRingObj l) f'.left).rightDerivedFunctor.map
      ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πX).inv.app
        P.obj) ≫
      (baseChangedProperTrace l f f' sq γ
        (𝟙 ((boundedConstructibleUpperStarOfMap l πY).obj N))).hom ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πY).hom.app
        N.obj := by
  have := isIso_baseChangeMap_of_weaklyEtale (Profinite.padicAlgClRingObj l) sq
  simp only [rightDerivedLowerStarBaseChangeIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Iso.symm_inv, Category.assoc]
  rw [← NatTrans.naturality]
  have hbc := boundedConstructibleBaseChangeOfMap_inv_app_hom l f f' sq P
  simp only [baseChangedProperTrace, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, boundedConstructibleUpperStarOfMap_map,
    ObjectProperty.homMk_hom, Category.assoc, hbc]
  erw [Category.id_comp]
  simp only [Functor.id_obj]

/-- The base-changed proper trace is universal in the exact-pullback coordinates
when its exceptional base-change component is invertible. -/
theorem bijective_map_comp_properTrace_levelwise_of_isIso [IsIso γ]
    [IsIso ((upperShriekBaseChangeOfMap l sq).app N)]
    (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj l⟧) :
    Function.Bijective fun φ : K.obj ⟶
        (upperStar (Profinite.padicAlgClRingObj l) πX).mapDerivedCategory.obj P.obj ↦
      (lowerStar (Profinite.padicAlgClRingObj l) f'.left).rightDerivedFunctor.map φ ≫
      (rightDerivedLowerStarBaseChangeIso (Profinite.padicAlgClRingObj l) sq).inv.app P.obj ≫
      (upperStar (Profinite.padicAlgClRingObj l) πY).mapDerivedCategory.map
        (((boundedConstructibleLowerStar l f).map γ ≫
          (lowerStarUpperShriekAdjunction l f).counit.app N).hom) := by
  simp_rw [baseChangedProperTrace_levelwise l f f' sq γ]
  exact Functor.bijective_map_comp_iso_trace _
    ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πX).symm.app
      P.obj)
    ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πY).app N.obj)
    (baseChangedProperTrace l f f' sq γ
      (𝟙 ((boundedConstructibleUpperStarOfMap l πY).obj N))).hom
    (bijective_map_comp_baseChangedProperTrace_of_isIso l f f' sq γ
      (𝟙 ((boundedConstructibleUpperStarOfMap l πY).obj N)) K)

/-- The base-changed smooth proper trace is universal in the exact-pullback
coordinates used by the descended Weil trace. -/
theorem bijective_map_comp_properTrace_levelwise [IsIso γ]
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj l⟧) :
    Function.Bijective fun φ : K.obj ⟶
        (upperStar (Profinite.padicAlgClRingObj l) πX).mapDerivedCategory.obj P.obj ↦
      (lowerStar (Profinite.padicAlgClRingObj l) f'.left).rightDerivedFunctor.map φ ≫
      (rightDerivedLowerStarBaseChangeIso (Profinite.padicAlgClRingObj l) sq).inv.app P.obj ≫
      (upperStar (Profinite.padicAlgClRingObj l) πY).mapDerivedCategory.map
        (((boundedConstructibleLowerStar l f).map γ ≫
          (lowerStarUpperShriekAdjunction l f).counit.app N).hom) := by
  have := isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale l d sq N
  exact bijective_map_comp_properTrace_levelwise_of_isIso l f f' sq γ K

end AlgebraicGeometry.ProEtale.CondensedRing
