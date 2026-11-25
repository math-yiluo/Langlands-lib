/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison
public import WeilConjectures.Mathlib.CategoryTheory.Functor.TwoSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeVertical

/-!

# Coherence of the compact-support base change on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`

This file records the pasting laws of the compact-support base change `Ex_!` and its comparison
with the direct-image base change `Ex_*` for proper vertical maps, and derives the compatibility
of `Ex_!` with the units of `Lf^* ⊣ Rf_!` for proper `f`.

## Main results

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz`,
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert`: the
  exchange of a pasted cartesian rectangle is the composite of the exchanges of the two squares
  (blueprint `proposition-composition-base-change-rf-shriek`, item (2)).
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper`: for
  proper vertical maps, `Ex_!` is `Ex_*` through `Rf_! ≅ Rf_*` (blueprint
  `def-exchange-projection`, the compactification `f = f ∘ 𝟙`).

All three are deduced from the description of `Ex_!` through any compactification and its base
change
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange`),
from the corresponding laws in the abstract exchange formalism
(`CategoryTheory.ExchangeFormalism`) and, for vertical pasting, from the description of the
composition isomorphism through any triangle of compactifications.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Pasting

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Over (Spec (.of k))}
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
  [LocallyOfFiniteType Y₃.hom] [QuasiCompact Y₃.hom] [IsSeparated Y₃.hom]

/-- **Horizontal pasting of `Ex_!`**, as an identity of 2-squares: the exchange of the outer
rectangle is the vertical composite of the exchanges of the two squares, after inserting the
composition isomorphisms of the pullbacks. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz'
    {g'₁ : X₁ ⟶ X₂} {g'₂ : X₂ ⟶ X₃} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {f : X₃ ⟶ Y₃}
    {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} (sq₁ : IsPullback g'₁ f₁ f₂ g₁) (sq₂ : IsPullback g'₂ f₂ f g₂) :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sq₁.paste_horiz sq₂) =
      TwoSquare.whiskerRight
        ((TwoSquare.vComp (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂)
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁)).whiskerLeft
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g'₁ g'₂).inv)
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g₁ g₂).hom := by
  have hi₂ := (compactificationOverField f).overBaseChange_isPullback_i sq₂
  have hp₂ := (compactificationOverField f).overBaseChange_isPullback_g sq₂
  have hi₁ := ((compactificationOverField f).ofIsPullback sq₂.overLeft).overBaseChange_isPullback_i
    sq₁
  have hp₁ := ((compactificationOverField f).ofIsPullback sq₂.overLeft).overBaseChange_isPullback_g
    sq₁
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ (sq₁.paste_horiz sq₂)
      (compactificationOverField f)
      (((compactificationOverField f).ofIsPullback sq₂.overLeft).ofIsPullback sq₁.overLeft) _
      (hi₁.paste_horiz hi₂) (hp₁.paste_horiz hp₂),
    boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ sq₂
      (compactificationOverField f) ((compactificationOverField f).ofIsPullback sq₂.overLeft) _
      hi₂ hp₂,
    boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ sq₁
      ((compactificationOverField f).ofIsPullback sq₂.overLeft)
      (((compactificationOverField f).ofIsPullback sq₂.overLeft).ofIsPullback sq₁.overLeft) _
      hi₁ hp₁,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl,
    ← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ
      ((compactificationOverField f).ofIsPullback sq₂.overLeft)]
  simp only [Iso.refl_hom, Functor.whiskerRight_id', Category.id_comp, Iso.symm_hom]
  exact TwoSquare.whiskerLeft_whiskerRight_vComp_conj _ _ _ _ _ _ _
    (boundedConstructibleLowerShriekOfCompactificationBaseChange_paste_horiz ℓ _ _ _ _ _
      hi₂ hp₂ hi₁ hp₁)

/-- **Horizontal pasting of `Ex_!`** (blueprint `proposition-composition-base-change-rf-shriek`,
item (2)): for cartesian squares `g'₁ ≫ f₂ = f₁ ≫ g₁` and `g'₂ ≫ f = f₂ ≫ g₂`, the exchange of the
outer rectangle is `L(g₁ ≫ g₂)^* Rf_! ≅ Lg₁^* Lg₂^* Rf_! ⟶ Lg₁^* Rf₂_! Lg'₂^* ⟶ Rf₁_! Lg'₁^* Lg'₂^*
≅ Rf₁_! L(g'₁ ≫ g'₂)^*`. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz
    {g'₁ : X₁ ⟶ X₂} {g'₂ : X₂ ⟶ X₃} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {f : X₃ ⟶ Y₃}
    {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} (sq₁ : IsPullback g'₁ f₁ f₂ g₁) (sq₂ : IsPullback g'₂ f₂ f g₂)
    (K : Dᵇc(X₃.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sq₁.paste_horiz sq₂)).app K =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g₁ g₂).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₁).map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂).app K) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'₂).obj K) ≫
        (boundedConstructibleLowerShriek ℓ f₁).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g'₁ g'₂).inv.app
            K) := by
  have h :=
    congr_app (boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz' ℓ sq₁ sq₂) K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc] at h
  exact h

/-- **Vertical pasting of `Ex_!`** (blueprint `proposition-composition-base-change-rf-shriek`, item
(2)): for cartesian squares `h ≫ v₂ = v₁ ≫ k` and `k ≫ w₂ = w₁ ≫ l`, the exchange of the outer
rectangle is `Ll^* R(v₂ ≫ w₂)_! ≅ Ll^* Rw₂_! Rv₂_! ⟶ Rw₁_! Lk^* Rv₂_! ⟶ Rw₁_! Rv₁_! Lh^*
≅ R(v₁ ≫ w₁)_! Lh^*`. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert
    {h : X₁ ⟶ X₂} {v₁ : X₁ ⟶ Y₁} {v₂ : X₂ ⟶ Y₂} {k : Y₁ ⟶ Y₂} {w₁ : Y₁ ⟶ X₃} {w₂ : Y₂ ⟶ Y₃}
    {l : X₃ ⟶ Y₃} (sq₁ : IsPullback h v₁ v₂ k) (sq₂ : IsPullback k w₁ w₂ l)
    (M : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sq₁.paste_vert sq₂)).app M =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ l).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ v₂ w₂).hom.app M) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂).app
          ((boundedConstructibleLowerShriek ℓ v₂).obj M) ≫
        (boundedConstructibleLowerShriek ℓ w₁).map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app M) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ v₁ w₁).inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj M) := by
  have hM :=
    congr_app (boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert' ℓ sq₁ sq₂) M
  simp only [TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc] at hM
  exact hM

end Pasting

section Proper

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **`Ex_!` for proper vertical maps is `Ex_*`**, as an identity of natural transformations. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper'
    (sq : IsPullback g' f' f g) [IsProper f.left] [IsProper f'.left] :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq ≫
        Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f').hom =
      Functor.whiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) ≫
        boundedConstructibleBaseChange ℓ sq.toCommSq := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ sq
      (Compactification.ofIsProper f.left) (Compactification.ofIsProper f'.left)
      (ofIsProperBaseChangeHom sq) (isPullback_ofIsProper_overI sq)
      (isPullback_ofIsProper_overG sq),
    boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq,
    boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq]
  have hc : Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (Compactification.ofIsProper f'.left) (compactificationOverField f')).hom ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (compactificationOverField f') (Compactification.ofIsProper f'.left)).hom = 𝟙 _ := by
    rw [← Functor.whiskerLeft_comp, ← Iso.trans_hom,
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans,
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl]
    simp
  simp only [Iso.trans_hom, Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [reassoc_of% hc]
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChange_ofIsProper ℓ sq]

/-- **`Ex_!` for proper vertical maps is `Ex_*`** (blueprint `def-exchange-projection`: `Ex_!` is
represented by `Ex_*` for the compactification `f = f ∘ 𝟙` of a proper `f`): under the
identifications `Rf_! ≅ Rf_*` and `Rf'_! ≅ Rf'_*`, the compact-support base change of a
cartesian square with `f` and `f'` proper is the direct-image base change. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper
    (sq : IsPullback g' f' f g) [IsProper f.left] [IsProper f'.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f').hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj K) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K) ≫
        (boundedConstructibleBaseChange ℓ sq.toCommSq).app K := by
  have h := congr_app (boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper' ℓ sq) K
  simpa using h

/-- The exchange `Rf ⋙ G ⟶ G' ⋙ Rf'` of an isomorphism `θ : G ⋙ Lf' ≅ Lf ⋙ G'` along the
adjunctions `Lf ⊣ Rf` and `Lf' ⊣ Rf'` is compatible with the units. -/
lemma Adjunction.map_unit_app_comp_exchangeRight_app {A B A' B' : Type*} [Category A] [Category B]
    [Category A'] [Category B'] {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G')
    (M : B) :
    G.map (af.unit.app M) ≫ (Adjunction.exchangeRight af af' θ).app (Lf.obj M) =
      af'.unit.app (G.obj M) ≫ Rf'.map (θ.hom.app M) := by
  rw [Adjunction.exchangeRight_app]
  erw [← af'.unit_naturality_assoc]
  rw [← Rf'.map_comp_assoc, ← Rf'.map_comp]
  have hθ := θ.hom.naturality (af.unit.app M)
  simp only [Functor.comp_map] at hθ
  erw [hθ]
  rw [Category.assoc, ← G'.map_comp]
  erw [af.left_triangle_components]
  simp

-- the `erw` steps unfold the restricted `ℚ̲̄_ℓ`-functors, which is expensive
/-- **`Ex_!` is compatible with the units of `Lf^* ⊣ Rf_!`** for proper vertical maps:
`Lg^*(η_f) ≫ Ex_! = η_{f'} ≫ Rf'_!(θ_sq)` with `θ_sq : Lg^* Lf'^* ≅ Lf^* Lg'^*`. -/
lemma map_unit_app_comp_boundedConstructibleLowerShriekBaseChange_padicAlgCl_app
    (sq : IsPullback g' f' f g) [IsProper f.left] [IsProper f'.left]
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
        ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M) =
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f').unit.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj M) ≫
      (boundedConstructibleLowerShriek ℓ f').map
        ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
          sq.toCommSq).hom.app M) := by
  have hP := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper ℓ sq
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)
  have hU := Adjunction.map_unit_app_comp_exchangeRight_app
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f')
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq)
    M
  rw [← boundedConstructibleBaseChange_eq_exchangeRight] at hU
  have hn := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f').inv.naturality
    ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq).hom.app M)
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rw [← cancel_mono ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f').hom.app _)]
  simp only [Category.assoc]
  rw [hP, ← Functor.map_comp_assoc
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app _), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hU]
  erw [← reassoc_of% hn, Iso.inv_hom_id_app, Category.comp_id]

/-- The compact-support base changes of squares with equal sides agree up to the casts. -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_congr_app
    {g'₁ g'₂ : X' ⟶ X} {f'₁ f'₂ : X' ⟶ Y'} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y' ⟶ Y}
    (sq₁ : IsPullback g'₁ f'₁ f₁ g₁) (sq₂ : IsPullback g'₂ f'₂ f₂ g₂) (h₁ : g'₁ = g'₂)
    (h₂ : f'₁ = f'₂) (h₃ : f₁ = f₂) (h₄ : g₁ = g₂)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app K =
      eqToHom (by subst h₃ h₄; rfl) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂).app K ≫
        eqToHom (by subst h₁ h₂; rfl) := by
  subst h₁ h₂ h₃ h₄
  simp


/-- The compact-support base changes of squares differing only in the bottom map agree up to
the cast. -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_congr_app_bottom
    {g₁ g₂ : Y' ⟶ Y} (sq₁ : IsPullback g' f' f g₁) (sq₂ : IsPullback g' f' f g₂) (h : g₁ = g₂)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app K =
      eqToHom (by subst h; rfl) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂).app K := by
  subst h
  simp
end Proper

end AlgebraicGeometry.ProEtale.CondensedRing
