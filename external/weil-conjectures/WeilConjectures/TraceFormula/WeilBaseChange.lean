/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.TraceFormula.ShriekTraceFunction

/-!
# Compactly supported base change of Weil objects

For a cartesian square `g' ≫ f = f' ≫ g` of separated schemes of finite type over `Spec k`,
compatible with automorphisms of the four corners, the compact-support base-change isomorphism
`Ex_! : Lg^* Rf_! K ≅ Rf'_! Lg'^* K` is an isomorphism of Weil objects, so that both have the
same local traces
(`ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilUpperStar_weilLowerShriek`).
Its compatibility with the Frobenius structures is the pasting law of `Ex_!` (blueprint
`proposition-composition-base-change-rf-shriek`, item (2)) applied to the rectangles formed by the
square and the Frobenius squares, in the two possible orders
(`ProEtale.CondensedRing.weilUpperStarLowerShriekIso_comm`). The transport of the isomorphism to
Weil objects is the general `CategoryTheory.Endofunctor.IsoAlgebra.compMapOfNatIsoIsoOfIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D D' E : Type*} {_ : Category C} {_ : Category D} {_ : Category D'} {_ : Category E}
  {F : C ⥤ C} {G : D ⥤ D} {G' : D' ⥤ D'} {H : E ⥤ E}
  {L₁ : C ⥤ D} {L₂ : D ⥤ E} {M₁ : C ⥤ D'} {M₂ : D' ⥤ E}
  (e₁ : L₁ ⋙ G ≅ F ⋙ L₁) (e₂ : L₂ ⋙ H ≅ G ⋙ L₂) (e₁' : M₁ ⋙ G' ≅ F ⋙ M₁)
  (e₂' : M₂ ⋙ H ≅ G' ⋙ M₂) (α : L₁ ⋙ L₂ ⟶ M₁ ⋙ M₂) [IsIso α]
  (hα : ∀ X, H.map (α.app X) ≫ e₂'.hom.app (M₁.obj X) ≫ M₂.map (e₁'.hom.app X) =
    e₂.hom.app (L₁.obj X) ≫ L₂.map (e₁.hom.app X) ≫ α.app (F.obj X))

/-- An isomorphism `α : L₁ ⋙ L₂ ≅ M₁ ⋙ M₂` compatible with the commutation isomorphisms of the
four functors induces an isomorphism `mapOfNatIso e₁ ⋙ mapOfNatIso e₂ ≅
mapOfNatIso e₁' ⋙ mapOfNatIso e₂'` between the two-step transports, with components `α`: the
composite of `mapOfNatIsoCompIso` and `mapOfNatIsoIsoOfIso`. -/
noncomputable def compMapOfNatIsoIsoOfIso :
    mapOfNatIso e₁ ⋙ mapOfNatIso e₂ ≅ mapOfNatIso e₁' ⋙ mapOfNatIso e₂' :=
  mapOfNatIsoCompIso e₁ e₂ ≪≫ mapOfNatIsoIsoOfIso (asIso α) (by ext X; simpa using hα X) ≪≫
    (mapOfNatIsoCompIso e₁' e₂').symm

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X X' Y Y' : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {eX : X ≅ X} {eX' : X' ≅ X'} {eY : Y ≅ Y} {eY' : Y' ≅ Y'}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
  (hg' : eX'.hom ≫ g' = g' ≫ eX.hom) (hf' : eX'.hom ≫ f' = f' ≫ eY'.hom)
  (hf : eX.hom ≫ f = f ≫ eY.hom) (hg : eY'.hom ≫ g = g ≫ eY.hom)

/-- The compact-support base changes of two cartesian squares with the same vertical sides and
equal horizontal sides agree, through the casts of the pullbacks. -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_comp_map_eqToHom
    {g'₁ g'₂ : X' ⟶ X} {g₁ g₂ : Y' ⟶ Y} (sq₁ : IsPullback g'₁ f' f g₁)
    (sq₂ : IsPullback g'₂ f' f g₂) (h₁ : g'₁ = g'₂) (h₂ : g₁ = g₂)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app K ≫
        (boundedConstructibleLowerShriek ℓ f').map
          (eqToHom (by rw [h₁]) :
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'₁).obj K ⟶
              (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'₂).obj K) =
      (eqToHom (by rw [h₂]) :
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₁).obj
              ((boundedConstructibleLowerShriek ℓ f).obj K) ⟶
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₂).obj
              ((boundedConstructibleLowerShriek ℓ f).obj K)) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂).app K := by
  subst h₁ h₂
  simp

include sq in
/-- **The Frobenius compatibility of the compact-support base change**: for a cartesian square
compatible with automorphisms of the corners,
`Le_{Y'}^* Ex_! ≫ Ex_!(e) ≫ Rf'_!(b^*_{g'}) = b^*_g ≫ Lg^* Ex_!(e) ≫ Ex_!`, where `Ex_!(e)` are
the Frobenius comparisons of the lower shrieks and `b^*` those of the pullbacks. Both sides are
the exchange of the rectangle `e_{X'} ≫ g' = g' ≫ e_X` over `e_{Y'} ≫ g = g ≫ e_Y`, pasted in the
two orders (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz`). -/
lemma weilUpperStarLowerShriekIso_comm (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eY'.hom).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app M) ≫
      (weilLowerShriekComparison ℓ eX' eY' hf').hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj M) ≫
        (boundedConstructibleLowerShriek ℓ f').map
          ((weilUpperStarComparison ℓ eX'.hom eX.hom g' hg').hom.app M) =
    (weilUpperStarComparison ℓ eY'.hom eY.hom g hg).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj M) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((weilLowerShriekComparison ℓ eX eY hf).hom.app M) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).obj M) := by
  have h₁ := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ
    (weilFrobeniusSquare eX' eY' hf') sq M
  have h₂ := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ
    sq (weilFrobeniusSquare eX eY hf) M
  simp only [weilLowerShriekComparison_hom, weilUpperStarComparison_hom_app, Functor.map_comp]
  have key : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eY'.hom).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
        (weilFrobeniusSquare eX' eY' hf')).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj M) ≫
      (boundedConstructibleLowerShriek ℓ f').map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ eX'.hom g').inv.app
          M) =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ eY'.hom g).inv.app
        ((boundedConstructibleLowerShriek ℓ f).obj M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
        ((weilFrobeniusSquare eX' eY' hf').paste_horiz sq)).app M := by
    rw [h₁, Iso.inv_hom_id_app_assoc]
  have e₂ : (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g eY.hom).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj M) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
          (weilFrobeniusSquare eX eY hf)).app M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).obj M) =
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
        (sq.paste_horiz (weilFrobeniusSquare eX eY hf))).app M ≫
      (boundedConstructibleLowerShriek ℓ f').map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g' eX.hom).hom.app
          M) := by
    rw [h₂]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
      CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [Category.assoc]
  rw [reassoc_of% key, reassoc_of%
    boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_comp_map_eqToHom ℓ
      ((weilFrobeniusSquare eX' eY' hf').paste_horiz sq)
      (sq.paste_horiz (weilFrobeniusSquare eX eY hf)) hg' hg M, e₂]

include sq in
/-- **Compactly supported base change of Weil objects**: for a cartesian square
`g' ≫ f = f' ≫ g` compatible with automorphisms of the four corners, the local traces of
`Lg^* Rf_! K` and `Rf'_! Lg'^* K` agree. The base-change isomorphism
`Ex_! : Lg^* Rf_! K ≅ Rf'_! Lg'^* K` is an isomorphism of Weil objects
(`CategoryTheory.Endofunctor.IsoAlgebra.compMapOfNatIsoIsoOfIso` applied to `Ex_!`). -/
theorem weilStalkTraceAlternatingSum_weilUpperStar_weilLowerShriek [Finite k]
    (K : WeilBoundedConstructible ℓ eX.hom)
    (n : ℕ) (y : Spec (.of (AlgebraicClosure k)) ⟶ Y'.left)
    (hy : y ≫ (eY'.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ y) :
    weilStalkTraceAlternatingSum ℓ (n + 1) y hy
        ((weilUpperStar ℓ eY'.hom eY.hom g hg).obj ((weilLowerShriek ℓ eX eY hf).obj K)) =
      weilStalkTraceAlternatingSum ℓ (n + 1) y hy
        ((weilLowerShriek ℓ eX' eY' hf').obj ((weilUpperStar ℓ eX'.hom eX.hom g' hg').obj K)) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have iso : weilLowerShriek ℓ eX eY hf ⋙ weilUpperStar ℓ eY'.hom eY.hom g hg ≅
        weilUpperStar ℓ eX'.hom eX.hom g' hg' ⋙ weilLowerShriek ℓ eX' eY' hf' :=
    IsoAlgebra.compMapOfNatIsoIsoOfIso (weilLowerShriekComparison ℓ eX eY hf)
      (weilUpperStarComparison ℓ eY'.hom eY.hom g hg)
      (weilUpperStarComparison ℓ eX'.hom eX.hom g' hg') (weilLowerShriekComparison ℓ eX' eY' hf')
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
      (weilUpperStarLowerShriekIso_comm ℓ sq hg' hf' hf hg)
  exact weilStalkTraceAlternatingSum_congr ℓ n y hy (iso.app K)

end AlgebraicGeometry.ProEtale.CondensedRing

