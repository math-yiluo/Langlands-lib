/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy


public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-!
# Pullback of pro-étale sheaves commutes with restriction of scalars

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings and `g : Y ⟶ Z` a morphism of schemes.
Restriction of scalars along `ρ` commutes with the pullback `g^*` of pro-étale sheaves of
modules: there is a canonical isomorphism `g^* (Res F) ≅ Res (g^* F)` for sheaves `F` of
`Λ'`-modules on `Z`. It is the conjugate, for the adjunctions `Res ⊣ Coext` and `g^* ⊣ g_*`, of
the identity `g_* ∘ Coext = Coext ∘ g_*`: the direct image is precomposition with base change,
while coextension of scalars is postcomposition. This isomorphism is compatible with the
composition, identity and congruence isomorphisms of the pullbacks, and passes to the derived
categories, where it is compatible with the corresponding isomorphisms of derived pullbacks.

This is the compatibility of pullback with the change of the finite coefficients, used to make
the systems of derived pullbacks of the `ℓ`-adic coefficient stages into morphisms of adic
systems.

## Main definitions

- `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso ρ g` :
  `Res ⋙ g^* ≅ g^* ⋙ Res` on pro-étale sheaves of modules.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso ρ g` :
  `Res ⋙ Lg^* ≅ Lg^* ⋙ Res` on the derived categories.

## Main results

- `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso_comp_hom`,
  `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso_id_hom`,
  `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso_congr_hom` : the compatibilities of
  `upperStarRestrictScalarsIso` with `upperStarComp`, `upperStarId` and `upperStarCongr`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso_comp_hom_app`,
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso_id_hom_app`,
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso_congr_hom_app` : the
  derived versions, with `leftDerivedUpperStarComp`, `leftDerivedUpperStarId` and
  `leftDerivedUpperStarCongr`.

The derived statements are deduced from the underived ones through general pasting lemmas for
the isomorphisms `CategoryTheory.Functor.mapDerivedCategorySquareIso` induced on derived
categories by exact functors (`CategoryTheory.Functor.mapDerivedCategorySquareIso_hom_app_comp`,
`CategoryTheory.Functor.mapDerivedCategorySquareIso_hom_app_id`), which rest on the coherence of
`CategoryTheory.Functor.mapDerivedCategoryCompIso` proved here.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory

section Conjugate

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- The inverse associator is conjugate to the inverse associator, the counterpart of
`CategoryTheory.conjugateEquiv_associator_hom`. -/
lemma conjugateEquiv_associator_inv {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv := by
  ext X
  simp only [Functor.comp_obj, conjugateEquiv_apply_app, Adjunction.comp_unit_app,
    Functor.comp_map, Category.assoc, ← Functor.map_comp, Functor.associator_inv_app,
    Adjunction.comp_counit_app, Category.id_comp]
  simp

/-- The inverse left unitor is conjugate to the right unitor, the counterpart of
`CategoryTheory.conjugateEquiv_leftUnitor_hom`. -/
lemma conjugateEquiv_leftUnitor_inv {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    conjugateEquiv (Adjunction.id.comp adj) adj (Functor.leftUnitor L).inv =
      (Functor.rightUnitor R).hom := by
  cat_disch

end Conjugate

namespace Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Factors

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]



variable [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]





end Factors

section Coherence

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']



variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]





variable (G : D ⥤ E) (H : E ⥤ E') [G.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]



end Coherence

section Whisker

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]





end Whisker

section Pasting

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*} [Category A₀] [Category A₁] [Category A₂] [Category B₀]
  [Category B₁] [Category B₂] [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian B₀] [Abelian B₁]
  [Abelian B₂] [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
  [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
  {r₀ : A₀ ⥤ B₀} {r₁ : A₁ ⥤ B₁} {r₂ : A₂ ⥤ B₂} {P₂ : A₀ ⥤ A₁} {P₁ : A₁ ⥤ A₂} {P₁₂ : A₀ ⥤ A₂}
  {p₂ : B₀ ⥤ B₁} {p₁ : B₁ ⥤ B₂} {p₁₂ : B₀ ⥤ B₂}
  [r₀.Additive] [PreservesFiniteLimits r₀] [PreservesFiniteColimits r₀]
  [r₁.Additive] [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
  [r₂.Additive] [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
  [P₂.Additive] [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  [P₁.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [P₁₂.Additive] [PreservesFiniteLimits P₁₂] [PreservesFiniteColimits P₁₂]
  [p₂.Additive] [PreservesFiniteLimits p₂] [PreservesFiniteColimits p₂]
  [p₁.Additive] [PreservesFiniteLimits p₁] [PreservesFiniteColimits p₁]
  [p₁₂.Additive] [PreservesFiniteLimits p₁₂] [PreservesFiniteColimits p₁₂]

/-- The isomorphisms `Functor.mapDerivedCategorySquareIso` induced on derived categories are
compatible with the pasting of squares of exact functors along composition isomorphisms
`e : p₁₂ ≅ p₂ ⋙ p₁` and `e' : P₁₂ ≅ P₂ ⋙ P₁`: if the square `α₁₂` is the pasting of `α₂` and
`α₁` (hypothesis `h`), then so is the induced square on derived categories.

```
        P₂        P₁                       P₁₂
   A₀ ─────▶ A₁ ─────▶ A₂            A₀ ─────────▶ A₂
   │r₀  α₂   │r₁  α₁   │r₂     =     │r₀    α₁₂    │r₂
   ▼         ▼         ▼             ▼             ▼
   B₀ ─────▶ B₁ ─────▶ B₂            B₀ ─────────▶ B₂
        p₂        p₁                       p₁₂
```
-/
lemma mapDerivedCategorySquareIso_hom_app_comp (α₂ : r₀ ⋙ p₂ ≅ P₂ ⋙ r₁)
    (α₁ : r₁ ⋙ p₁ ≅ P₁ ⋙ r₂) (α₁₂ : r₀ ⋙ p₁₂ ≅ P₁₂ ⋙ r₂) (e : p₁₂ ≅ p₂ ⋙ p₁)
    (e' : P₁₂ ≅ P₂ ⋙ P₁)
    (h : ∀ X, α₁₂.hom.app X ≫ r₂.map (e'.hom.app X) =
      e.hom.app (r₀.obj X) ≫ p₁.map (α₂.hom.app X) ≫ α₁.hom.app (P₂.obj X))
    (K : DerivedCategory A₀) :
    (mapDerivedCategorySquareIso α₁₂).hom.app K ≫
        r₂.mapDerivedCategory.map ((mapDerivedCategoryTriangleIso e').hom.app K) =
      (mapDerivedCategoryTriangleIso e).hom.app (r₀.mapDerivedCategory.obj K) ≫
        p₁.mapDerivedCategory.map ((mapDerivedCategorySquareIso α₂).hom.app K) ≫
        (mapDerivedCategorySquareIso α₁).hom.app (P₂.mapDerivedCategory.obj K) := by
  have hiso : α₁₂ ≪≫ isoWhiskerRight e' r₂ =
      isoWhiskerLeft r₀ e ≪≫ isoWhiskerRight α₂ p₁ ≪≫ isoWhiskerLeft P₂ α₁ := by
    ext X
    simpa using h X
  have hm : (mapDerivedCategoryNatIso α₁₂).hom.app K ≫
      (mapDerivedCategoryNatIso (isoWhiskerRight e' r₂)).hom.app K =
      (mapDerivedCategoryNatIso (isoWhiskerLeft r₀ e)).hom.app K ≫
      (mapDerivedCategoryNatIso (isoWhiskerRight α₂ p₁)).hom.app K ≫
      (mapDerivedCategoryNatIso (isoWhiskerLeft P₂ α₁)).hom.app K := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.comp_app,
      ← mapDerivedCategoryNatIso_trans, ← mapDerivedCategoryNatIso_trans,
      ← mapDerivedCategoryNatIso_trans, hiso]
  have hWR₁ := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight e' r₂) K
  have hWR₂ := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight α₂ p₁) K
  have hWL₁ := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft r₀ e) K
  have hWL₂ := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft P₂ α₁) K
  have hA₁ := congr_app (mapDerivedCategoryCompIso_assoc P₂ P₁ r₂) K
  have hA₂ := congr_app (mapDerivedCategoryCompIso_assoc r₀ p₂ p₁) K
  have hA₃ := congr_app (mapDerivedCategoryCompIso_assoc P₂ r₁ p₁) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hWR₁ hWR₂
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hWL₁ hWL₂
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hA₁ hA₂ hA₃
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have hWL₁' : (mapDerivedCategoryNatIso (isoWhiskerLeft r₀ e)).hom.app K =
      (mapDerivedCategoryCompIso r₀ p₁₂).inv.app K ≫
        (mapDerivedCategoryNatIso e).hom.app (r₀.mapDerivedCategory.obj K) ≫
        (mapDerivedCategoryCompIso r₀ (p₂ ⋙ p₁)).hom.app K := by
    rw [← reassoc_of% hWL₁, Iso.inv_hom_id_app, Category.comp_id]
  have hWR₂' : (mapDerivedCategoryNatIso (isoWhiskerRight α₂ p₁)).hom.app K =
      (mapDerivedCategoryCompIso (r₀ ⋙ p₂) p₁).inv.app K ≫
        p₁.mapDerivedCategory.map ((mapDerivedCategoryNatIso α₂).hom.app K) ≫
        (mapDerivedCategoryCompIso (P₂ ⋙ r₁) p₁).hom.app K := by
    rw [← reassoc_of% hWR₂, Iso.inv_hom_id_app, Category.comp_id]
  have hA₂' : (mapDerivedCategoryCompIso r₀ (p₂ ⋙ p₁)).hom.app K ≫
      (mapDerivedCategoryCompIso (r₀ ⋙ p₂) p₁).inv.app K =
      (mapDerivedCategoryCompIso p₂ p₁).inv.app (r₀.mapDerivedCategory.obj K) ≫
        p₁.mapDerivedCategory.map ((mapDerivedCategoryCompIso r₀ p₂).hom.app K) := by
    rw [← cancel_epi ((mapDerivedCategoryCompIso r₀ (p₂ ⋙ p₁)).inv.app K),
      Iso.inv_hom_id_app_assoc, reassoc_of% hA₂, ← Functor.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Category.comp_id]
  have hA₃' : (mapDerivedCategoryCompIso (P₂ ⋙ r₁) p₁).hom.app K ≫
      (mapDerivedCategoryCompIso P₂ (r₁ ⋙ p₁)).inv.app K =
      p₁.mapDerivedCategory.map ((mapDerivedCategoryCompIso P₂ r₁).inv.app K) ≫
        (mapDerivedCategoryCompIso r₁ p₁).hom.app (P₂.mapDerivedCategory.obj K) := by
    rw [← cancel_epi ((mapDerivedCategoryCompIso (P₂ ⋙ r₁) p₁).inv.app K),
      Iso.inv_hom_id_app_assoc, ← reassoc_of% hA₃, Iso.inv_hom_id_app, Category.comp_id]
  rw [← reassoc_of% hWR₁, ← hA₁, reassoc_of% hm, reassoc_of% hWL₂, hWL₁', hWR₂']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hA₂', reassoc_of% hA₃']

end Pasting

section Identity

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B] [HasDerivedCategory A]
  [HasDerivedCategory B] {r : A ⥤ B} {P : A ⥤ A} {p : B ⥤ B}
  [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [p.Additive] [PreservesFiniteLimits p] [PreservesFiniteColimits p]

/-- The isomorphism `Functor.mapDerivedCategorySquareIso` induced on derived categories by a
square of exact functors whose horizontal functors are identified with identity functors by
`eP` and `ep` is compatible with these identifications, as soon as the square itself is
(hypothesis `h`). -/
lemma mapDerivedCategorySquareIso_hom_app_id (α : r ⋙ p ≅ P ⋙ r) (eP : P ≅ 𝟭 A)
    (ep : p ≅ 𝟭 B) (h : ∀ X, α.hom.app X ≫ r.map (eP.hom.app X) = ep.hom.app (r.obj X))
    (K : DerivedCategory A) :
    (mapDerivedCategorySquareIso α).hom.app K ≫
        r.mapDerivedCategory.map
          ((mapDerivedCategoryNatIso eP ≪≫ mapDerivedCategoryIdIso A).hom.app K) =
      (mapDerivedCategoryNatIso ep ≪≫ mapDerivedCategoryIdIso B).hom.app
        (r.mapDerivedCategory.obj K) := by
  have hiso : α ≪≫ isoWhiskerRight eP r = isoWhiskerLeft r ep := by
    ext X
    simpa using h X
  have hm : (mapDerivedCategoryNatIso α).hom.app K ≫
      (mapDerivedCategoryNatIso (isoWhiskerRight eP r)).hom.app K =
      (mapDerivedCategoryNatIso (isoWhiskerLeft r ep)).hom.app K := by
    rw [← NatTrans.comp_app, ← mapDerivedCategoryNatIso_trans, hiso]
  have hWR := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight eP r) K
  have hWL := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft r ep) K
  have hUL := congr_app (mapDerivedCategoryCompIso_id_comp r) K
  have hUR := congr_app (mapDerivedCategoryCompIso_comp_id r) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hWR hWL hUL hUR
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hWR, reassoc_of% hm, hUL]
  -- the identity is that of an object which agrees with the target only up to unfolding `𝟭 A`
  erw [Category.comp_id]
  rw [← cancel_epi ((mapDerivedCategoryCompIso r p).inv.app K),
    Iso.inv_hom_id_app_assoc, ← reassoc_of% hWL, hUR]
  erw [Category.comp_id]

end Identity

end Functor

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section UpperStar

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z)

/-- Restriction of scalars along `ρ : Λ →+* Λ'` commutes with the pullback of pro-étale sheaves:
for a morphism of schemes `g : Y ⟶ Z`, the canonical isomorphism `g^* (Res F) ≅ Res (g^* F)` for
sheaves `F` of `Λ'`-modules on `Z`. It is the conjugate, for the composite adjunctions
`Res ⋙ g^* ⊣ g_* ⋙ Coext` and `g^* ⋙ Res ⊣ Coext ⋙ g_*`, of the identity of
`g_* ⋙ Coext = Coext ⋙ g_*`: the direct image restricts sheaves along base change, while
coextension of scalars is computed objectwise. -/
noncomputable def upperStarRestrictScalarsIso :
    Sheaf.restrictScalars (Scheme.ProEt.topology Z) ρ ⋙ upperStar (ModuleCat.{u + 1} Λ) g ≅
      upperStar (ModuleCat.{u + 1} Λ') g ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology Y) ρ :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction _ g).comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
    ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp (upperStarLowerStarAdjunction _ g))).symm
    (Iso.refl _)

/-- `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso` is conjugate to the identity. -/
lemma conjugateEquiv_upperStarRestrictScalarsIso_hom :
    conjugateEquiv
      ((upperStarLowerStarAdjunction _ g).comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
      ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp (upperStarLowerStarAdjunction _ g))
      (upperStarRestrictScalarsIso ρ g).hom = 𝟙 _ :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (Iso.refl _))

/-- The componentwise form of
`AlgebraicGeometry.ProEtale.conjugateEquiv_upperStarRestrictScalarsIso_hom`. -/
lemma conjugateEquiv_upperStarRestrictScalarsIso_hom_app
    (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :
    (conjugateEquiv
      ((upperStarLowerStarAdjunction _ g).comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
      ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp (upperStarLowerStarAdjunction _ g))
      (upperStarRestrictScalarsIso ρ g).hom).app F = 𝟙 _ :=
  NatTrans.congr_app (conjugateEquiv_upperStarRestrictScalarsIso_hom ρ g) F

end UpperStar

/-- The identity isomorphism of the pullback is conjugate to the inverse of the identity
isomorphism of the pushforward. -/
lemma conjugateEquiv_upperStarId_hom (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id (upperStarLowerStarAdjunction A (𝟙 X)) (upperStarId A X).hom =
      (lowerStarId A X).inv :=
  congrArg Iso.hom (conjugateIsoEquiv_upperStarId A X)

section Coherence

/-- Compatibility of `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso` with the
composition isomorphisms `(g₁ ≫ g₂)^* ≅ g₂^* ⋙ g₁^*`: the isomorphism for `g₁ ≫ g₂` is the
pasting of those for `g₂` and `g₁`. -/
lemma upperStarRestrictScalarsIso_comp_hom {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) :
    (upperStarRestrictScalarsIso ρ (g₁ ≫ g₂)).hom ≫
        Functor.whiskerRight (upperStarComp _ g₁ g₂).hom (Sheaf.restrictScalars _ ρ) =
      Functor.whiskerLeft (Sheaf.restrictScalars _ ρ) (upperStarComp _ g₁ g₂).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (upperStarRestrictScalarsIso ρ g₂).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (upperStarRestrictScalarsIso ρ g₁).hom ≫
        (Functor.associator _ _ _).inv := by
  apply (conjugateEquiv
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g₂).comp
      (upperStarLowerStarAdjunction _ g₁)).comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
    ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (g₁ ≫ g₂)))).injective
  rw [← conjugateEquiv_comp _
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') (g₁ ≫ g₂)).comp
      (Sheaf.restrictCoextendScalarsAdj _ ρ)) _,
    conjugateEquiv_whiskerRight, conjugateEquiv_upperStarComp_hom,
    ← conjugateEquiv_comp _
      ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g₂).comp
          (upperStarLowerStarAdjunction _ g₁))) _,
    ← conjugateEquiv_comp _
      (((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g₂)).comp
          (upperStarLowerStarAdjunction _ g₁)) _,
    ← conjugateEquiv_comp _
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g₂).comp
        (Sheaf.restrictCoextendScalarsAdj _ ρ)).comp
          (upperStarLowerStarAdjunction _ g₁)) _,
    ← conjugateEquiv_comp _
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g₂).comp
        ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
          (upperStarLowerStarAdjunction _ g₁))) _,
    ← conjugateEquiv_comp _
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g₂).comp
        ((upperStarLowerStarAdjunction _ g₁).comp
          (Sheaf.restrictCoextendScalarsAdj _ ρ))) _]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_upperStarComp_hom, conjugateEquiv_associator_inv,
    conjugateEquiv_associator_hom]
  ext F : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, Category.comp_id,
    conjugateEquiv_upperStarRestrictScalarsIso_hom_app]
  ext V : 3
  simp only [lowerStarComp_hom_app_hom_app]
  rfl

/-- Compatibility of `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso` with the identity
isomorphisms `(𝟙 X)^* ≅ 𝟭`. -/
lemma upperStarRestrictScalarsIso_id_hom (X : Scheme.{u}) :
    (upperStarRestrictScalarsIso ρ (𝟙 X)).hom ≫
        Functor.whiskerRight (upperStarId _ X).hom (Sheaf.restrictScalars _ ρ) =
      Functor.whiskerLeft (Sheaf.restrictScalars _ ρ) (upperStarId _ X).hom ≫
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv := by
  apply (conjugateEquiv (Adjunction.id.comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
    ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)))).injective
  rw [← conjugateEquiv_comp _
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') (𝟙 X)).comp
      (Sheaf.restrictCoextendScalarsAdj _ ρ)) _,
    ← conjugateEquiv_comp _
      ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp Adjunction.id) _,
    ← conjugateEquiv_comp _ (Sheaf.restrictCoextendScalarsAdj _ ρ) _]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_upperStarId_hom, conjugateEquiv_leftUnitor_inv,
    conjugateEquiv_rightUnitor_hom]
  ext F : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.comp_id,
    conjugateEquiv_upperStarRestrictScalarsIso_hom_app]
  ext V : 3
  simp only [lowerStarId_inv_app_hom_app]
  rfl

/-- Compatibility of `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso` with the
congruence isomorphisms `f^* ≅ g^*` for `f = g`. -/
lemma upperStarRestrictScalarsIso_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (upperStarRestrictScalarsIso ρ f).hom ≫
        Functor.whiskerRight (upperStarCongr _ h).hom (Sheaf.restrictScalars _ ρ) =
      Functor.whiskerLeft (Sheaf.restrictScalars _ ρ) (upperStarCongr _ h).hom ≫
        (upperStarRestrictScalarsIso ρ g).hom := by
  subst h
  simp [upperStarCongr]

end Coherence

section Derived

/-- The components of the composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` of derived
pullbacks, in terms of the functors induced levelwise by the exact pullbacks. -/
lemma leftDerivedUpperStarComp_hom_app (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology R) A)) :
    (leftDerivedUpperStarComp A g₁ g₂).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory A (g₁ ≫ g₂)).hom.app K ≫
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp A g₁ g₂)).hom.app K ≫
        (upperStar A g₁).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory A g₂).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A g₁).inv.app
          ((upperStar A g₂).leftDerivedFunctor.obj K) := by
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]

/-- The components of the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback, in terms
of the functor induced levelwise by the exact pullback. -/
lemma leftDerivedUpperStarId_hom_app (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (leftDerivedUpperStarId A X).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory A (𝟙 X)).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId A X) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app K := by
  simp [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z)

/-- The derived pullback commutes with restriction of scalars: for `ρ : Λ →+* Λ'` and a
morphism of schemes `g : Y ⟶ Z`, the canonical isomorphism `Lg^* (Res K) ≅ Res (Lg^* K)` for `K`
in the derived category of pro-étale sheaves of `Λ'`-modules on `Z`. Both derived pullbacks are
computed levelwise (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory`), and
the isomorphism is induced by `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso`. -/
noncomputable def leftDerivedUpperStarRestrictScalarsIso :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) ρ ⋙
        L(upperStar (ModuleCat.{u + 1} Λ) g) ≅
      L(upperStar (ModuleCat.{u + 1} Λ') g) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) ρ :=
  Functor.isoWhiskerLeft (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) ρ)
      (leftDerivedUpperStarIsoMapDerivedCategory _ g) ≪≫
    Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ g).symm
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) ρ)

/-- The components of `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_hom_app
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory _ g).hom.app
          ((Sheaf.derivedRestrictScalars _ ρ).obj K) ≫
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g)).hom.app K ≫
        (Sheaf.derivedRestrictScalars _ ρ).map
          ((leftDerivedUpperStarIsoMapDerivedCategory _ g).inv.app K) :=
  rfl

/-- Compatibility of `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso` with
the composition isomorphisms `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` (over `Λ'` on the left, over `Λ` on
the right). -/
lemma leftDerivedUpperStarRestrictScalarsIso_comp_hom_app {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology R) (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ (g₁ ≫ g₂)).hom.app K ≫
        (Sheaf.derivedRestrictScalars _ ρ).map ((leftDerivedUpperStarComp _ g₁ g₂).hom.app K) =
      (leftDerivedUpperStarComp _ g₁ g₂).hom.app ((Sheaf.derivedRestrictScalars _ ρ).obj K) ≫
        (L(upperStar (ModuleCat.{u + 1} Λ) g₁)).map
          ((leftDerivedUpperStarRestrictScalarsIso ρ g₂).hom.app K) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ g₁).hom.app
          ((L(upperStar (ModuleCat.{u + 1} Λ') g₂)).obj K) := by
  have H := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (upperStarRestrictScalarsIso ρ g₂) (upperStarRestrictScalarsIso ρ g₁)
    (upperStarRestrictScalarsIso ρ (g₁ ≫ g₂)) (upperStarComp _ g₁ g₂) (upperStarComp _ g₁ g₂)
    (fun X ↦ by simpa using congr_app (upperStarRestrictScalarsIso_comp_hom ρ g₁ g₂) X) K
  have hnat :=
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g₁)).hom.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ') g₂).inv.app K)
  simp only [Functor.comp_map] at hnat
  rw [leftDerivedUpperStarComp_hom_app, leftDerivedUpperStarComp_hom_app,
    leftDerivedUpperStarRestrictScalarsIso_hom_app,
    leftDerivedUpperStarRestrictScalarsIso_hom_app,
    leftDerivedUpperStarRestrictScalarsIso_hom_app]
  simp only [Category.assoc]
  -- `erw`: the instance arguments of the derived pullbacks are found along different paths
  erw [NatIso.naturality_1_assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  -- `erw`: `Sheaf.derivedRestrictScalars` is the reducible `mapDerivedCategory` of `H`
  erw [reassoc_of% hnat, reassoc_of% H]

/-- Compatibility of `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso` with
the identity isomorphisms `L(𝟙 X)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_id_hom_app (X : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ (𝟙 X)).hom.app K ≫
        (Sheaf.derivedRestrictScalars _ ρ).map ((leftDerivedUpperStarId _ X).hom.app K) =
      (leftDerivedUpperStarId _ X).hom.app ((Sheaf.derivedRestrictScalars _ ρ).obj K) := by
  have H := Functor.mapDerivedCategorySquareIso_hom_app_id (upperStarRestrictScalarsIso ρ (𝟙 X))
    (upperStarId _ X) (upperStarId _ X)
    (fun Y ↦ by simpa using congr_app (upperStarRestrictScalarsIso_id_hom ρ X) Y) K
  rw [leftDerivedUpperStarRestrictScalarsIso_hom_app, leftDerivedUpperStarId_hom_app,
    leftDerivedUpperStarId_hom_app]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  -- `erw`: `Sheaf.derivedRestrictScalars` is the reducible `mapDerivedCategory` of `H`
  erw [H]

/-- Compatibility of `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso` with
the congruence isomorphisms `Lf^* ≅ Lg^*` for `f = g`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_congr_hom_app {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ f).hom.app K ≫
        (Sheaf.derivedRestrictScalars _ ρ).map ((leftDerivedUpperStarCongr _ h).hom.app K) =
      (leftDerivedUpperStarCongr _ h).hom.app ((Sheaf.derivedRestrictScalars _ ρ).obj K) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app K := by
  subst h
  simp

end Derived

end AlgebraicGeometry.ProEtale
