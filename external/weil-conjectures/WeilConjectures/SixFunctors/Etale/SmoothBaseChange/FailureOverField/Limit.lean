/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.TransitionComposition

/-!
# Survival of a cokernel element under cofiltered limits

The ingredients of step (2) of the blueprint lemma `lemma-reduction-field--1`
(`AlgebraicGeometry.Etale.survivesBaseChange_of_isLimit`): for a cofiltered system of schemes
`T_i` over `T` with affine transition morphisms, the transition maps of the sources and of the
targets of the base-change maps over the stages `T_i` form directed systems
(`AlgebraicGeometry.Etale.overLowerStarTransition`,
`AlgebraicGeometry.Etale.overTargetTransition`), compatible with the base-change maps, and on
geometric stalks the targets over the limit are the colimits of the targets over the stages, by
the limit theorem for higher direct images (`AlgebraicGeometry.Etale.higherDirectImage_limit`).

## Main statements

- `AlgebraicGeometry.Etale.mem_range_baseChangeHomologyMap_iff`: the survival condition written
  with the derived transition maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Without this, `X ⟶ Y` in statements elaborates through `ReflQuiver.toQuiver`, while compositions
and functor images carry `CategoryStruct.toQuiver`; the kernel reconciles the two on the derived
categories only by unfolding them, which made the proofs below slow to check. -/
attribute [-instance] CategoryTheory.catToReflQuiver

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

lemma mapDerivedCategoryPlusNatIso_hom_app_singleFunctor {F G : C ⥤ D} [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (X : C) :
    (mapDerivedCategoryPlusNatIso e).hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
        (G.mapDerivedCategoryPlusSingleFunctor 0).hom.app X =
      (F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
        (DerivedCategory.Plus.singleFunctor D 0).map (e.hom.app X) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  exact mapDerivedCategoryNatIso_hom_app_singleFunctor e X

lemma mapDerivedCategoryPlusCompIso_hom_app_singleFunctor (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : C) :
    (mapDerivedCategoryPlusCompIso F G).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
        G.mapDerivedCategoryPlus.map ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) ≫
        (G.mapDerivedCategoryPlusSingleFunctor 0).hom.app (F.obj X) =
      ((F ⋙ G).mapDerivedCategoryPlusSingleFunctor 0).hom.app X := by
  apply DerivedCategory.Plus.ι.map_injective
  have hmap : ∀ {X Y : DerivedCategory.Plus D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map f) =
        G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := fun _ => rfl
  simp only [Functor.map_comp, ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    ι_map_mapDerivedCategoryPlusCompIso_hom_app, hmap]
  exact mapDerivedCategoryCompIso_hom_app_singleFunctor F G X


lemma mapDerivedCategoryPlusNatIso_trans_compIso_hom_app_singleFunctor {F₁₂ : C ⥤ E}
    (F₂ : C ⥤ D) (F₁ : D ⥤ E) [F₁₂.Additive] [F₂.Additive] [F₁.Additive]
    [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁] (e : F₁₂ ≅ F₂ ⋙ F₁) (X : C) :
    (mapDerivedCategoryPlusNatIso e ≪≫ mapDerivedCategoryPlusCompIso F₂ F₁).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
      F₁.mapDerivedCategoryPlus.map ((F₂.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) ≫
      (F₁.mapDerivedCategoryPlusSingleFunctor 0).hom.app (F₂.obj X) =
    (F₁₂.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
      (DerivedCategory.Plus.singleFunctor E 0).map (e.hom.app X) := by
  rw [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    mapDerivedCategoryPlusCompIso_hom_app_singleFunctor]
  exact mapDerivedCategoryPlusNatIso_hom_app_singleFunctor e X

end CategoryTheory.Functor

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section Single

/-- The composition isomorphism of the derived pullbacks at a sheaf placed in degree `0` is the
underived composition isomorphism, through the identifications `h^*(G[0]) ≅ (h^* G)[0]`. -/
lemma Etale.upperStarCompDerivedPlus_hom_app_singleFunctor {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
      D+((h₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((h₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G) ≫
      (((h₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((h₂)^*[ModuleCat.{u + 1} Λ]).obj G) =
    (((h₁₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app G) := by
  exact Functor.mapDerivedCategoryPlusNatIso_trans_compIso_hom_app_singleFunctor _ _ _ G

end Single

section StageTransition

omit [CommRing Λ] in
/-- The naturality of a natural transformation between composites of functors, stated for
abstract functors so that its instances at concrete functors are checked syntactically. -/
lemma natTrans_app_comp_map_map {ℬ 𝒞 𝒞' 𝒟 : Type*} [Category* ℬ]
    [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟] {P₁ : ℬ ⥤ 𝒞} {P₂ : 𝒞 ⥤ 𝒟} {Q₁ : ℬ ⥤ 𝒞'}
    {Q₂ : 𝒞' ⥤ 𝒟} (β : P₁ ⋙ P₂ ⟶ Q₁ ⋙ Q₂) {X Y : ℬ} (f : X ⟶ Y) :
    P₂.map (P₁.map f) ≫ β.app Y = β.app X ≫ Q₂.map (Q₁.map f) :=
  β.naturality f

variable {S T : Scheme.{u}}

/-- The transition map `R(πᵢ ≫ g)_*(πᵢ^* K) ⟶ R(πⱼ ≫ g)_*(πⱼ^* K)` between the derived direct
images of the pullbacks of a complex `K` on `T` to two schemes `Tᵢ`, `Tⱼ` over `T`, along a
morphism `ρ : Tⱼ ⟶ Tᵢ` over `T`: the transition map
`AlgebraicGeometry.Etale.lowerStarPlusTransition` along `ρ`, followed by the composition
isomorphism `ρ^* πᵢ^* ≅ πⱼ^*`. -/
noncomputable def Etale.overLowerStarTransition (g : T ⟶ S) {Tᵢ Tⱼ : Scheme.{u}} (πᵢ : Tᵢ ⟶ T)
    (πⱼ : Tⱼ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ) (hπ : ρ ≫ πᵢ = πⱼ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((πᵢ ≫ g)_*[ModuleCat.{u + 1} Λ]).obj (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K) ⟶
      R+((πⱼ ≫ g)_*[ModuleCat.{u + 1} Λ]).obj (D+((πⱼ)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  Etale.lowerStarPlusTransition Λ ρ (πᵢ ≫ g) (πⱼ ≫ g) (by rw [← Category.assoc, hπ]) _ ≫
    R+((πⱼ ≫ g)_*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ πⱼ hπ.symm).inv.app K)

/-- The transition maps `AlgebraicGeometry.Etale.overLowerStarTransition` compose. -/
lemma Etale.overLowerStarTransition_comp (g : T ⟶ S) {Tᵢ Tⱼ Tₖ : Scheme.{u}} (πᵢ : Tᵢ ⟶ T)
    (πⱼ : Tⱼ ⟶ T) (πₖ : Tₖ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ) (ρ' : Tₖ ⟶ Tⱼ) (ρ'' : Tₖ ⟶ Tᵢ)
    (hπ : ρ ≫ πᵢ = πⱼ) (hπ' : ρ' ≫ πⱼ = πₖ) (hπ'' : ρ'' ≫ πᵢ = πₖ) (hρ : ρ' ≫ ρ = ρ'')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.overLowerStarTransition Λ g πᵢ πⱼ ρ hπ K ≫
        Etale.overLowerStarTransition Λ g πⱼ πₖ ρ' hπ' K =
      Etale.overLowerStarTransition Λ g πᵢ πₖ ρ'' hπ'' K := by
  subst hρ hπ hπ'
  have hc := Etale.lowerStarPlusTransition_comp Λ ρ ρ' (ρ' ≫ ρ) rfl (πᵢ ≫ g) ((ρ ≫ πᵢ) ≫ g)
    ((ρ' ≫ ρ ≫ πᵢ) ≫ g) (by rw [Category.assoc]) (by simp only [Category.assoc])
    (by simp only [Category.assoc]) (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K)
  have hn := Etale.lowerStarPlusTransition_naturality Λ ρ' ((ρ ≫ πᵢ) ≫ g)
    ((ρ' ≫ ρ ≫ πᵢ) ≫ g) (by simp only [Category.assoc])
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ (ρ ≫ πᵢ) rfl).inv.app K)
  have A := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    ρ' ρ πᵢ (ρ' ≫ ρ) (ρ ≫ πᵢ) (ρ' ≫ ρ ≫ πᵢ) rfl rfl (Category.assoc _ _ _).symm) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A
  have A' : D+((ρ')^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ (ρ ≫ πᵢ) rfl).inv.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ' (ρ ≫ πᵢ) (ρ' ≫ ρ ≫ πᵢ)
        rfl).inv.app K =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ' ρ (ρ' ≫ ρ) rfl).inv.app
          (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (ρ' ≫ ρ) πᵢ (ρ' ≫ ρ ≫ πᵢ)
          (Category.assoc _ _ _).symm).inv.app K := by
    rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (ρ' ≫ ρ) πᵢ
        (ρ' ≫ ρ ≫ πᵢ) (Category.assoc _ _ _).symm).hom.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ' ρ (ρ' ≫ ρ) rfl).hom.app
          (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K)), ← A]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rw [reassoc_of% A]
    simp
  simp only [Etale.overLowerStarTransition, Category.assoc]
  rw [reassoc_of% hn, ← hc]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [A']

/-- The transition map between the targets of the derived base-change maps over two schemes
`Tᵢ`, `Tⱼ` over `T`, along a morphism `ρ : Tⱼ ⟶ Tᵢ` over `T` covered by `b : Yⱼ ⟶ Yᵢ`: the
transition map `AlgebraicGeometry.Etale.targetTransitionPlus` at `πᵢ^* K`, followed by the
composition isomorphism `ρ^* πᵢ^* ≅ πⱼ^*`. -/
noncomputable def Etale.overTargetTransition {X Yᵢ Yⱼ Tᵢ Tⱼ : Scheme.{u}} (eᵢ : Yᵢ ⟶ Tᵢ)
    (hᵢ : Yᵢ ⟶ X) (eⱼ : Yⱼ ⟶ Tⱼ) (hⱼ : Yⱼ ⟶ X) (πᵢ : Tᵢ ⟶ T) (πⱼ : Tⱼ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ)
    (b : Yⱼ ⟶ Yᵢ) (wa : b ≫ eᵢ = eⱼ ≫ ρ) (wh : b ≫ hᵢ = hⱼ) (hπ : ρ ≫ πᵢ = πⱼ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((hᵢ)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((eᵢ)^*[ModuleCat.{u + 1} Λ]).obj (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K)) ⟶
      R+((hⱼ)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((eⱼ)^*[ModuleCat.{u + 1} Λ]).obj (D+((πⱼ)^*[ModuleCat.{u + 1} Λ]).obj K)) :=
  Etale.targetTransitionPlus Λ eᵢ hᵢ ρ b eⱼ hⱼ wa wh _ ≫
    R+((hⱼ)_*[ModuleCat.{u + 1} Λ]).map (D+((eⱼ)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ πⱼ hπ.symm).inv.app K))

/-- The transition map from `T` to `Tᵢ`, followed by the transition map from `Tᵢ` to `Tⱼ`, is
the transition map from `T` to `Tⱼ`. -/
lemma Etale.targetTransitionPlus_comp_overTargetTransition {X Y Yᵢ Yⱼ Tᵢ Tⱼ : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (eᵢ : Yᵢ ⟶ Tᵢ) (hᵢ : Yᵢ ⟶ X) (eⱼ : Yⱼ ⟶ Tⱼ) (hⱼ : Yⱼ ⟶ X)
    (πᵢ : Tᵢ ⟶ T) (πⱼ : Tⱼ ⟶ T) (aᵢ : Yᵢ ⟶ Y) (aⱼ : Yⱼ ⟶ Y) (waᵢ : aᵢ ≫ e = eᵢ ≫ πᵢ)
    (whᵢ : aᵢ ≫ h = hᵢ) (waⱼ : aⱼ ≫ e = eⱼ ≫ πⱼ) (whⱼ : aⱼ ≫ h = hⱼ) (ρ : Tⱼ ⟶ Tᵢ)
    (b : Yⱼ ⟶ Yᵢ) (wa : b ≫ eᵢ = eⱼ ≫ ρ) (wh : b ≫ hᵢ = hⱼ) (hπ : ρ ≫ πᵢ = πⱼ)
    (hb : b ≫ aᵢ = aⱼ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.targetTransitionPlus Λ e h πᵢ aᵢ eᵢ hᵢ waᵢ whᵢ K ≫
        Etale.overTargetTransition Λ eᵢ hᵢ eⱼ hⱼ πᵢ πⱼ ρ b wa wh hπ K =
      Etale.targetTransitionPlus Λ e h πⱼ aⱼ eⱼ hⱼ waⱼ whⱼ K :=
  Etale.targetTransitionPlus_comp Λ e h πᵢ aᵢ eᵢ hᵢ waᵢ whᵢ ρ b eⱼ hⱼ wa wh πⱼ aⱼ hb hπ waⱼ
    whⱼ K

/-- The derived base-change maps over `Tᵢ` and over `Tⱼ` commute with the transition maps
`AlgebraicGeometry.Etale.overLowerStarTransition` and
`AlgebraicGeometry.Etale.overTargetTransition`. -/
lemma Etale.baseChange_app_comp_overTargetTransition {X Yᵢ Yⱼ Tᵢ Tⱼ : Scheme.{u}} {p : X ⟶ S}
    (g : T ⟶ S) {eᵢ : Yᵢ ⟶ Tᵢ} {hᵢ : Yᵢ ⟶ X} {eⱼ : Yⱼ ⟶ Tⱼ} {hⱼ : Yⱼ ⟶ X} {πᵢ : Tᵢ ⟶ T}
    {πⱼ : Tⱼ ⟶ T} (sqᵢ : CommSq eᵢ hᵢ (πᵢ ≫ g) p) (sqⱼ : CommSq eⱼ hⱼ (πⱼ ≫ g) p)
    (ρ : Tⱼ ⟶ Tᵢ) (b : Yⱼ ⟶ Yᵢ) (wa : b ≫ eᵢ = eⱼ ≫ ρ) (wh : b ≫ hᵢ = hⱼ)
    (hπ : ρ ≫ πᵢ = πⱼ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sqᵢ).app (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        Etale.overTargetTransition Λ eᵢ hᵢ eⱼ hⱼ πᵢ πⱼ ρ b wa wh hπ K =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.overLowerStarTransition Λ g πᵢ πⱼ ρ hπ K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sqⱼ).app
          (D+((πⱼ)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  have c := Etale.baseChange_app_comp_targetTransitionPlus Λ sqᵢ ρ (πⱼ ≫ g)
    (by rw [← Category.assoc, hπ]) sqⱼ b wa wh (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K)
  have n := natTrans_app_comp_map_map (P₁ := R+((πⱼ ≫ g)_*[ModuleCat.{u + 1} Λ]))
    (P₂ := D+((p)^*[ModuleCat.{u + 1} Λ])) (Q₁ := D+((eⱼ)^*[ModuleCat.{u + 1} Λ]))
    (Q₂ := R+((hⱼ)_*[ModuleCat.{u + 1} Λ])) (Etale.baseChange (ModuleCat.{u + 1} Λ) sqⱼ)
    (X := D+((ρ)^*[ModuleCat.{u + 1} Λ]).obj (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K))
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ πⱼ hπ.symm).inv.app K)
  rw [Etale.overTargetTransition, reassoc_of% c, Etale.overLowerStarTransition,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [n]

end StageTransition

section Conversion

/-- The form of `AlgebraicGeometry.Etale.upperStarCompDerivedPlus_hom_app_singleFunctor` for the
inverse of the composition isomorphism. -/
lemma Etale.upperStarCompDerivedPlus_inv_app_singleFunctor {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
      (((h₁₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G =
    D+((h₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((h₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G) ≫
      (((h₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((h₂)^*[ModuleCat.{u + 1} Λ]).obj G) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).inv.app G) := by
  rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)), Iso.hom_inv_id_app_assoc,
    reassoc_of% Etale.upperStarCompDerivedPlus_hom_app_singleFunctor, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

variable {S T : Scheme.{u}}

/-- The transition map `AlgebraicGeometry.Etale.overLowerStarTransition` at a sheaf placed in
degree `0` is, through the identifications `π^*(G[0]) ≅ (π^* G)[0]`, the transition map of
higher direct images underlying `AlgebraicGeometry.Etale.higherDirectImageOverMap`. -/
lemma Etale.overLowerStarTransition_singleFunctor (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {U V : Over T} (φ : U ⟶ V) :
    Etale.overLowerStarTransition Λ g V.hom U.hom φ.left (Over.w φ)
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
      R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((U.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G) =
    R+((V.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((V.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G) ≫
      Etale.lowerStarPlusTransition Λ φ.left (V.hom ≫ g) (U.hom ≫ g)
        (by rw [← Category.assoc, Over.w])
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) ≫
      R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((φ.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
            (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G) ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
              (Over.w φ).symm).inv.app G)) := by
  have hn := Etale.lowerStarPlusTransition_naturality Λ φ.left (V.hom ≫ g) (U.hom ≫ g)
    (by rw [← Category.assoc, Over.w])
    ((((V.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G)
  rw [reassoc_of% hn, Etale.overLowerStarTransition, Category.assoc, ← Functor.map_comp,
    Etale.upperStarCompDerivedPlus_inv_app_singleFunctor, Functor.map_comp]

/-- The transition map `AlgebraicGeometry.Etale.higherDirectImageOverMap`, unfolded: the
degree-`q` homology of the transition map of derived direct images followed by the
identifications `φ^*(G|_V[0]) ≅ (φ^* G|_V)[0]` and `φ^*(G|_V) ≅ G|_U`. -/
lemma Etale.higherDirectImageOverMap_eq (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V : Over T} (φ : U ⟶ V) :
    Etale.higherDirectImageOverMap Λ g G q φ =
      (DerivedCategory.Plus.homologyFunctor _ q).map
          (Etale.lowerStarPlusTransition Λ φ.left (V.hom ≫ g) (U.hom ≫ g)
              (by rw [← Category.assoc, Over.w])
              ((DerivedCategory.Plus.singleFunctor _ 0).obj
                (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) ≫
            R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
              ((((φ.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
                (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G))) ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map
              ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
                (Over.w φ).symm).inv.app G))) :=
  rfl

/-- In degree `q`, the transition map `AlgebraicGeometry.Etale.overLowerStarTransition` at a sheaf
placed in degree `0` is `AlgebraicGeometry.Etale.higherDirectImageOverMap`, through the
identifications `π^*(G[0]) ≅ (π^* G)[0]`. -/
lemma Etale.homologyFunctor_map_overLowerStarTransition (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V : Over T}
    (φ : U ⟶ V) :
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.overLowerStarTransition Λ g V.hom U.hom φ.left (Over.w φ)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((((U.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G)) =
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((V.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((((V.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G)) ≫
      Etale.higherDirectImageOverMap Λ g G q φ := by
  rw [Etale.higherDirectImageOverMap_eq, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, Etale.overLowerStarTransition_singleFunctor]
  simp only [Functor.map_comp, Category.assoc]

/-- The identification `e'^*(π^*(F[0])) ≅ (a^*(e^* F))[0]` for a commutative square
`a ≫ e = e' ≫ π`. -/
noncomputable def Etale.stageSingleIso {Y Y' T' : Scheme.{u}} (e : Y ⟶ T) (a : Y' ⟶ Y)
    (e' : Y' ⟶ T') (π : T' ⟶ T) (wa : a ≫ e = e' ≫ π)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    D+((e')^*[ModuleCat.{u + 1} Λ]).obj
        (D+((π)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        (((a)^*[ModuleCat.{u + 1} Λ]).obj (((e)^*[ModuleCat.{u + 1} Λ]).obj F)) :=
  ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).symm ≪≫
      Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≪≫
    D+((a)^*[ModuleCat.{u + 1} Λ]).mapIso
      ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F) ≪≫
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app
      (((e)^*[ModuleCat.{u + 1} Λ]).obj F)

/-- The coherence of the composition isomorphisms of derived pullbacks underlying
`AlgebraicGeometry.Etale.overTargetTransition_stageSingleIso`: the inverse form of
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus_coherence`. -/
lemma Etale.upperStarCompDerivedPlus_coherence_inv {T₂ T₁ Y Y₂ Y₁ : Scheme.{u}} (e : Y ⟶ T)
    (e₂ : Y₂ ⟶ T₂) (e₁ : Y₁ ⟶ T₁) (π₂ : T₂ ⟶ T) (π₁ : T₁ ⟶ T₂) (π : T₁ ⟶ T)
    (a₂ : Y₂ ⟶ Y) (a₁ : Y₁ ⟶ Y₂) (a : Y₁ ⟶ Y) (ha : a₁ ≫ a₂ = a) (hπ : π₁ ≫ π₂ = π)
    (wa₂ : a₂ ≫ e = e₂ ≫ π₂) (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁) (wa : a ≫ e = e₁ ≫ π)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ e₂ (a₁ ≫ e₂) rfl).inv.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π₁ (a₁ ≫ e₂) wa₁).hom.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₁ π₂ π hπ.symm).inv.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π (a ≫ e) wa).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).hom.app K =
    D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).inv.app K ≫
          (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).hom.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).inv.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  have C := Etale.upperStarCompDerivedPlus_coherence Λ e e₂ e₁ π₂ π₁ π a₂ a₁ a ha hπ wa₂ wa₁ wa K
  rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a
      ha.symm).hom.app (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
    D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).hom.app K))]
  simp only [Category.assoc] at C ⊢
  rw [reassoc_of% C]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rfl

/-- The transition map `AlgebraicGeometry.Etale.overTargetTransition` at a sheaf placed in
degree `0` is, through the identifications `AlgebraicGeometry.Etale.stageSingleIso`, the transition
map of higher direct images underlying `AlgebraicGeometry.Etale.higherDirectImageOverMap`. -/
lemma Etale.overTargetTransition_stageSingleIso {X Y Tᵢ Tⱼ : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) {U V : Over Y} (φ : U ⟶ V) (eᵢ : V.left ⟶ Tᵢ) (eⱼ : U.left ⟶ Tⱼ)
    (πᵢ : Tᵢ ⟶ T) (πⱼ : Tⱼ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ) (waᵢ : V.hom ≫ e = eᵢ ≫ πᵢ)
    (waⱼ : U.hom ≫ e = eⱼ ≫ πⱼ) (wa : φ.left ≫ eᵢ = eⱼ ≫ ρ) (hπ : ρ ≫ πᵢ = πⱼ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.overTargetTransition Λ eᵢ (V.hom ≫ h) eⱼ (U.hom ≫ h) πᵢ πⱼ ρ φ.left wa
        (by rw [← Category.assoc, Over.w]) hπ ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      R+((U.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        (Etale.stageSingleIso Λ e U.hom eⱼ πⱼ waⱼ F).hom =
    R+((V.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        (Etale.stageSingleIso Λ e V.hom eᵢ πᵢ waᵢ F).hom ≫
      Etale.lowerStarPlusTransition Λ φ.left (V.hom ≫ h) (U.hom ≫ h)
        (by rw [← Category.assoc, Over.w])
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj (((e)^*[ModuleCat.{u + 1} Λ]).obj F))) ≫
      R+((U.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        ((((φ.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
            (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj (((e)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
              (Over.w φ).symm).inv.app (((e)^*[ModuleCat.{u + 1} Λ]).obj F))) := by
  have hn := Etale.lowerStarPlusTransition_naturality Λ φ.left (V.hom ≫ h) (U.hom ≫ h)
    (by rw [← Category.assoc, Over.w]) (Etale.stageSingleIso Λ e V.hom eᵢ πᵢ waᵢ F).hom
  rw [reassoc_of% hn, Etale.overTargetTransition, Etale.targetTransitionPlus]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  -- the identity of isomorphisms in the derived category of `U`
  have hs := Etale.upperStarCompDerivedPlus_inv_app_singleFunctor Λ φ.left V.hom U.hom
    (Over.w φ).symm (((e)^*[ModuleCat.{u + 1} Λ]).obj F)
  have hc := Etale.upperStarCompDerivedPlus_coherence_inv Λ e eᵢ eⱼ πᵢ ρ πⱼ V.hom φ.left U.hom
    (Over.w φ) hπ waᵢ wa waⱼ ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  have hnat := natTrans_app_comp_map_map (P₁ := D+((V.hom)^*[ModuleCat.{u + 1} Λ]))
    (P₂ := D+((φ.left)^*[ModuleCat.{u + 1} Λ])) (Q₁ := 𝟭 _)
    (Q₂ := D+((U.hom)^*[ModuleCat.{u + 1} Λ]))
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
      (Over.w φ).symm).inv
    (X := D+((e)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    (Y := (DerivedCategory.Plus.singleFunctor _ 0).obj (((e)^*[ModuleCat.{u + 1} Λ]).obj F))
    ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
  simp only [Etale.stageSingleIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc] at hc ⊢
  rw [← hs, reassoc_of% hnat, reassoc_of% hc]

/-- In degree `q`, the transition map `AlgebraicGeometry.Etale.overTargetTransition` at a sheaf
placed in degree `0` is `AlgebraicGeometry.Etale.higherDirectImageOverMap`, through the
identifications `AlgebraicGeometry.Etale.stageSingleIso`. -/
lemma Etale.homologyFunctor_map_overTargetTransition {X Y Tᵢ Tⱼ : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) {U V : Over Y} (φ : U ⟶ V) (eᵢ : V.left ⟶ Tᵢ) (eⱼ : U.left ⟶ Tⱼ)
    (πᵢ : Tᵢ ⟶ T) (πⱼ : Tⱼ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ) (waᵢ : V.hom ≫ e = eᵢ ≫ πᵢ)
    (waⱼ : U.hom ≫ e = eⱼ ≫ πⱼ) (wa : φ.left ≫ eᵢ = eⱼ ≫ ρ) (hπ : ρ ≫ πᵢ = πⱼ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.overTargetTransition Λ eᵢ (V.hom ≫ h) eⱼ (U.hom ≫ h) πᵢ πⱼ ρ φ.left wa
          (by rw [← Category.assoc, Over.w]) hπ ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((U.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          (Etale.stageSingleIso Λ e U.hom eⱼ πⱼ waⱼ F).hom) =
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((V.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          (Etale.stageSingleIso Λ e V.hom eᵢ πᵢ waᵢ F).hom) ≫
      Etale.higherDirectImageOverMap Λ h (((e)^*[ModuleCat.{u + 1} Λ]).obj F) q φ := by
  rw [Etale.higherDirectImageOverMap_eq, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, Etale.overTargetTransition_stageSingleIso Λ e h φ eᵢ eⱼ πᵢ πⱼ ρ waᵢ waⱼ wa
      hπ F]
  simp only [Functor.map_comp, Category.assoc]

end Conversion

/-- If a family of morphisms `τᵢ : Mᵢ ⟶ N` of sheaves on `S_ét` is jointly surjective on the
stalks at all geometric points of `S`, then for `p : X ⟶ S` the pullbacks `p^* τᵢ` are jointly
surjective on the stalk at every geometric point of `X`, in the sense that every element is a
sum of elements in their images. -/
lemma Etale.mem_iSup_range_sheafFiber_map_upperStar {S X : Scheme.{u}} (p : X ⟶ S) (x : X)
    {I : Type u} (M : I → Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {N : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (τ : ∀ i, M i ⟶ N)
    (h : ∀ (s : S) (y : ((S.uliftPointSmallEtale s).sheafFiber.obj N : ModuleCat.{u + 1} Λ)),
      ∃ i y', ((S.uliftPointSmallEtale s).sheafFiber.map (τ i)).hom y' = y)
    (y : ((X.uliftPointSmallEtale x).sheafFiber.obj (((p)^*[ModuleCat.{u + 1} Λ]).obj N) :
      ModuleCat.{u + 1} Λ)) :
    y ∈ ⨆ i, LinearMap.range
      ((X.uliftPointSmallEtale x).sheafFiber.map (((p)^*[ModuleCat.{u + 1} Λ]).map (τ i))).hom := by
  have : ∀ Z : Scheme.{u}, LocallySmall.{u + 1} Z.Etale := fun _ ↦ locallySmall_max.{u + 1, u}
  let σ : ∐ M ⟶ N := Sigma.desc τ
  -- `σ` is an epimorphism, since it is surjective on all stalks
  have hepi : ∀ s : S, Epi ((S.uliftPointSmallEtale s).sheafFiber.map σ) := fun s ↦ by
    rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨i, y', rfl⟩ := h s y
    refine ⟨((S.uliftPointSmallEtale s).sheafFiber.map (Sigma.ι M i)).hom y', ?_⟩
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, Sigma.ι_comp_desc]
  have hQ : IsZero (cokernel σ) := by
    have : IsIso (0 : cokernel σ ⟶ cokernel σ) := by
      refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
      have hz : IsZero ((S.uliftPointSmallEtale s).sheafFiber.obj (cokernel σ)) := by
        refine IsZero.of_epi_eq_zero ((S.uliftPointSmallEtale s).sheafFiber.map (cokernel.π σ)) ?_
        rw [← cancel_epi ((S.uliftPointSmallEtale s).sheafFiber.map σ), ← Functor.map_comp,
          cokernel.condition, Functor.map_zero, comp_zero]
      exact ⟨0, hz.eq_of_src _ _, hz.eq_of_src _ _⟩
    exact (IsZero.iff_id_eq_zero _).2
      (by rw [← IsIso.hom_inv_id (0 : cokernel σ ⟶ cokernel σ), zero_comp])
  have : Epi σ := Preadditive.epi_of_isZero_cokernel σ hQ
  have : Epi ((X.uliftPointSmallEtale x).sheafFiber.map (((p)^*[ModuleCat.{u + 1} Λ]).map σ)) :=
    inferInstance
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 this y
  let G := (p)^*[ModuleCat.{u + 1} Λ] ⋙ (X.uliftPointSmallEtale x).sheafFiber
  have hc : IsColimit (G.mapCocone (Cofan.mk _ (Sigma.ι M))) :=
    isColimitOfPreserves G (coproductIsCoproduct M)
  -- the images of the coprojections span the stalk of the coproduct
  have hz : z ∈ ⨆ i, LinearMap.range (G.map (Sigma.ι M i)).hom := by
    let P := ⨆ i, LinearMap.range (G.map (Sigma.ι M i)).hom
    have hq : ModuleCat.ofHom P.mkQ = 0 := by
      refine hc.hom_ext fun ⟨i⟩ ↦ ?_
      ext w
      simp only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, ModuleCat.hom_comp,
        ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply, Limits.comp_zero,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero P).2
        (Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ w))
    have := congrArg (fun f ↦ f.hom z) hq
    simpa using this
  refine (?_ : Submodule.map ((X.uliftPointSmallEtale x).sheafFiber.map
    (((p)^*[ModuleCat.{u + 1} Λ]).map σ)).hom (⨆ i, LinearMap.range (G.map (Sigma.ι M i)).hom) ≤ _)
    (Submodule.mem_map_of_mem hz)
  rw [Submodule.map_iSup]
  refine iSup_mono fun i ↦ ?_
  rw [← LinearMap.range_comp, ← ModuleCat.hom_comp]
  change LinearMap.range ((X.uliftPointSmallEtale x).sheafFiber.map
    (((p)^*[ModuleCat.{u + 1} Λ]).map (Sigma.ι M i)) ≫ _).hom ≤ _
  rw [← Functor.map_comp, ← Functor.map_comp, Sigma.ι_comp_desc]

section StageFunctor

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The base change of schemes over `T` to schemes over `Y`, for a Cartesian square `sq` with
base `g : T ⟶ S`: a scheme `U` over `T` is sent to `U ×_S X`, mapping to `Y = T ×_S X` through
the Cartesian square. -/
@[simps]
noncomputable def Etale.stageFunctor (sq : IsPullback e h g p) : Over T ⥤ Over Y where
  obj U := Over.mk (sq.lift (pullback.fst (U.hom ≫ g) p ≫ U.hom) (pullback.snd (U.hom ≫ g) p)
    (by rw [Category.assoc]; exact pullback.condition))
  map {U V} φ := Over.homMk (pullback.map _ _ _ _ φ.left (𝟙 X) (𝟙 S)
      (by rw [Category.comp_id, ← Category.assoc, Over.w]) (by simp))
    (sq.hom_ext (by simp [Over.w φ]) (by simp))
  map_id U := by ext1; exact pullback.hom_ext (by simp) (by simp)
  map_comp φ ψ := by ext1; exact pullback.hom_ext (by simp) (by simp)

/-- The square relating the base changes of a morphism `φ : U ⟶ V` of schemes over `T` is
Cartesian. -/
lemma Etale.isPullback_stageFunctor_map (sq : IsPullback e h g p) {U V : Over T} (φ : U ⟶ V) :
    IsPullback ((Etale.stageFunctor sq).map φ).left (pullback.fst (U.hom ≫ g) p)
      (pullback.fst (V.hom ≫ g) p) φ.left := by
  refine IsPullback.flip (IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback _ _))
  have hb : ((Etale.stageFunctor sq).map φ).left ≫ pullback.snd (V.hom ≫ g) p =
      pullback.snd (U.hom ≫ g) p := by simp
  rw [hb, ← Category.assoc, Over.w φ]
  exact IsPullback.of_hasPullback _ _

instance (sq : IsPullback e h g p) {U V : Over T} (φ : U ⟶ V) [IsAffineHom φ.left] :
    IsAffineHom ((Etale.stageFunctor sq).map φ).left :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (Etale.isPullback_stageFunctor_map sq φ).flip
    inferInstance

/-- The base change of a cofiltered limit of schemes over `T` is a limit. -/
noncomputable def Etale.isLimitStageFunctorMapCone (sq : IsPullback e h g p) {I : Type*}
    [Category I] [IsCofiltered I] {D : I ⥤ Over T} (c : Cone D)
    (hc : IsLimit ((Over.forget T).mapCone c)) :
    IsLimit ((Over.forget Y).mapCone ((Etale.stageFunctor sq).mapCone c)) :=
  have : IsConnected I := IsCofiltered.isConnected I
  isLimitOfIsPullbackOfIsConnected
    (F := (D ⋙ Etale.stageFunctor sq) ⋙ Over.forget Y) (G := D ⋙ Over.forget T)
    { app i := pullback.fst ((D.obj i).hom ≫ g) p
      naturality i j f := by simp }
    _ ((Over.forget T).mapCone c)
    { hom := pullback.fst (c.pt.hom ≫ g) p
      w j := by simp }
    (fun i ↦ Etale.isPullback_stageFunctor_map sq (c.π.app i)) hc

end StageFunctor

section SourceIso

variable {X S T : Scheme.{u}}

/-- The identification of the degree-`q` homology of `p^* R(W ≫ g)_*(W^*(G[0]))` with the pullback
along `p` of the higher direct image `R^q(W ≫ g)_*(W^* G)`. -/
noncomputable def Etale.sourceStageIso (p : X ⟶ S) (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (W : Over T) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj (D+((p)^*[ModuleCat.{u + 1} Λ]).obj
        (R+((W.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj (D+((W.hom)^*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≅
      ((p)^*[ModuleCat.{u + 1} Λ]).obj
        (Etale.higherDirectImage Λ (W.hom ≫ g) q (((W.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) :=
  (DerivedCategory.Plus.homologyFunctor _ q).mapIso (D+((p)^*[ModuleCat.{u + 1} Λ]).mapIso
      (R+((W.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).mapIso
        ((((W.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app G))) ≪≫
    (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).symm.app
      (R+((W.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((W.hom)^*[ModuleCat.{u + 1} Λ]).obj G)))

/-- The transition maps `AlgebraicGeometry.Etale.overLowerStarTransition`, pulled back along `p`,
are in degree `q` the pullbacks of the maps `AlgebraicGeometry.Etale.higherDirectImageOverMap`. -/
lemma Etale.sourceStageIso_naturality (p : X ⟶ S) (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V : Over T} (φ : U ⟶ V) :
    (DerivedCategory.Plus.homologyFunctor _ q).map (D+((p)^*[ModuleCat.{u + 1} Λ]).map
        (Etale.overLowerStarTransition Λ g V.hom U.hom φ.left (Over.w φ)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) ≫
      (Etale.sourceStageIso Λ p g G q U).hom =
    (Etale.sourceStageIso Λ p g G q V).hom ≫
      ((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.higherDirectImageOverMap Λ g G q φ) := by
  have E := Etale.homologyFunctor_map_overLowerStarTransition Λ g G q φ
  have n₁ := natTrans_app_comp_map_map (P₁ := D+((p)^*[ModuleCat.{u + 1} Λ]))
    (P₂ := DerivedCategory.Plus.homologyFunctor _ q)
    (Q₁ := DerivedCategory.Plus.homologyFunctor _ q) (Q₂ := (p)^*[ModuleCat.{u + 1} Λ])
    (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).inv
    (X := R+((V.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj (D+((V.hom)^*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))
    (Y := R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj G)))
    (Etale.overLowerStarTransition Λ g V.hom U.hom φ.left (Over.w φ)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
      R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((U.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G))
  have n₂ := natTrans_app_comp_map_map (P₁ := D+((p)^*[ModuleCat.{u + 1} Λ]))
    (P₂ := DerivedCategory.Plus.homologyFunctor _ q)
    (Q₁ := DerivedCategory.Plus.homologyFunctor _ q) (Q₂ := (p)^*[ModuleCat.{u + 1} Λ])
    (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).inv
    (X := R+((V.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj (D+((V.hom)^*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))
    (Y := R+((V.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G)))
    (R+((V.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((V.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G))
  simp only [Etale.sourceStageIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, n₁,
    Functor.map_comp (DerivedCategory.Plus.homologyFunctor _ q), E, Functor.map_comp,
    ← Category.assoc, ← n₂]

end SourceIso

/-- The stalk form of `AlgebraicGeometry.Etale.sourceStageIso_naturality`. -/
lemma Etale.sheafFiber_map_sourceStageIso_naturality {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V : Over T} (φ : U ⟶ V)
    (x : X) :
    (DerivedCategory.Plus.homologyFunctor _ q ⋙ (X.uliftPointSmallEtale x).sheafFiber).map
        (D+((p)^*[ModuleCat.{u + 1} Λ]).map
          (Etale.overLowerStarTransition Λ g V.hom U.hom φ.left (Over.w φ)
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) ≫
      (X.uliftPointSmallEtale x).sheafFiber.map (Etale.sourceStageIso Λ p g G q U).hom =
    (X.uliftPointSmallEtale x).sheafFiber.map (Etale.sourceStageIso Λ p g G q V).hom ≫
      (X.uliftPointSmallEtale x).sheafFiber.map
        (((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.higherDirectImageOverMap Λ g G q φ)) := by
  rw [Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp,
    Etale.sourceStageIso_naturality]

/-- The stalk form of `AlgebraicGeometry.Etale.homologyFunctor_map_overTargetTransition`. -/
lemma Etale.sheafFiber_map_overTargetTransition {X Y T Tᵢ Tⱼ : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) {U V : Over Y} (φ : U ⟶ V) (eᵢ : V.left ⟶ Tᵢ) (eⱼ : U.left ⟶ Tⱼ)
    (πᵢ : Tᵢ ⟶ T) (πⱼ : Tⱼ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ) (waᵢ : V.hom ≫ e = eᵢ ≫ πᵢ)
    (waⱼ : U.hom ≫ e = eⱼ ≫ πⱼ) (wa : φ.left ≫ eᵢ = eⱼ ≫ ρ) (wh : φ.left ≫ V.hom ≫ h = U.hom ≫ h)
    (hπ : ρ ≫ πᵢ = πⱼ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (x : X) :
    (DerivedCategory.Plus.homologyFunctor _ q ⋙ (X.uliftPointSmallEtale x).sheafFiber).map
        (Etale.overTargetTransition Λ eᵢ (V.hom ≫ h) eⱼ (U.hom ≫ h) πᵢ πⱼ ρ φ.left wa wh hπ
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (X.uliftPointSmallEtale x).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((U.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          (Etale.stageSingleIso Λ e U.hom eⱼ πⱼ waⱼ F).hom)) =
    (X.uliftPointSmallEtale x).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((V.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          (Etale.stageSingleIso Λ e V.hom eᵢ πᵢ waᵢ F).hom)) ≫
      (X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.higherDirectImageOverMap Λ h (((e)^*[ModuleCat.{u + 1} Λ]).obj F) q φ) := by
  have E := congrArg (X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.homologyFunctor_map_overTargetTransition Λ e h φ eᵢ eⱼ πᵢ πⱼ ρ waᵢ waⱼ wa hπ F q)
  rw [Functor.map_comp, Functor.map_comp] at E
  exact E

section Survival

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The form of `AlgebraicGeometry.Etale.sheafFiber_map_overTargetTransition` for the base changes
along a morphism `ψ` of schemes over `T`. -/
lemma Etale.sheafFiber_map_stageTargetTransition (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (x : X) {U V : Over T}
    (ψ : U ⟶ V) :
    (DerivedCategory.Plus.homologyFunctor _ q ⋙ (X.uliftPointSmallEtale x).sheafFiber).map
        (Etale.overTargetTransition Λ (pullback.fst (V.hom ≫ g) p)
          (((Etale.stageFunctor sq).obj V).hom ≫ h) (pullback.fst (U.hom ≫ g) p)
          (((Etale.stageFunctor sq).obj U).hom ≫ h) V.hom U.hom ψ.left
          ((Etale.stageFunctor sq).map ψ).left (by simp) (by rw [← Category.assoc, Over.w])
          (Over.w ψ) ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (X.uliftPointSmallEtale x).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((((Etale.stageFunctor sq).obj U).hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          (Etale.stageSingleIso Λ e ((Etale.stageFunctor sq).obj U).hom
            (pullback.fst (U.hom ≫ g) p) U.hom (sq.lift_fst _ _ _) F).hom)) =
    (X.uliftPointSmallEtale x).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((((Etale.stageFunctor sq).obj V).hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          (Etale.stageSingleIso Λ e ((Etale.stageFunctor sq).obj V).hom
            (pullback.fst (V.hom ≫ g) p) V.hom (sq.lift_fst _ _ _) F).hom)) ≫
      (X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.higherDirectImageOverMap Λ h (((e)^*[ModuleCat.{u + 1} Λ]).obj F) q
          ((Etale.stageFunctor sq).map ψ)) :=
  Etale.sheafFiber_map_overTargetTransition Λ e h ((Etale.stageFunctor sq).map ψ)
    (pullback.fst (V.hom ≫ g) p) (pullback.fst (U.hom ≫ g) p) V.hom U.hom ψ.left
    (sq.lift_fst _ _ _) (sq.lift_fst _ _ _) (by simp) (by rw [← Category.assoc, Over.w])
    (Over.w ψ) F q x

omit [CommRing Λ] in
private lemma mem_range_iff_of_comm' {R : Type*} [Ring R] {A B C D : ModuleCat R}
    (f : A ⟶ B) (g : C ⟶ D) (s : A ⟶ C) (t : B ⟶ D) [IsIso s] [IsIso t] (w : f ≫ t = s ≫ g)
    (y : B) : y ∈ Set.range f.hom ↔ t.hom y ∈ Set.range g.hom := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨s.hom z, by rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← w,
      ModuleCat.hom_comp, LinearMap.comp_apply]⟩
  · rintro ⟨z, hz⟩
    refine ⟨(inv s).hom z, ((ConcreteCategory.isIso_iff_bijective t).1 inferInstance).1 ?_⟩
    change (f ≫ t).hom _ = _
    rw [w, ← hz, ModuleCat.hom_comp, LinearMap.comp_apply, ← LinearMap.comp_apply s.hom,
      ← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply]

/-- The membership of the transported element in the image of the base-change map does not
depend on how the second side `h'` of the Cartesian square is written. -/
lemma Etale.mem_range_baseChangeHomologyMap_congr (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T' Y' : Scheme.{u}} (π : T' ⟶ T) (e' : Y' ⟶ T') (h₁ h₂ : Y' ⟶ X)
    (sq₁ : IsPullback e' h₁ (π ≫ g) p) (sq₂ : IsPullback e' h₂ (π ≫ g) p) (a : Y' ⟶ Y)
    (wa : a ≫ e = e' ≫ π) (wh₁ : a ≫ h = h₁) (wh₂ : a ≫ h = h₂) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeTargetTransition Λ e h q π a e' h₁ wa wh₁ F)).hom ξ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq₁ q (((π)^*[ModuleCat.{u + 1} Λ]).obj F))).hom ↔
    ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeTargetTransition Λ e h q π a e' h₂ wa wh₂ F)).hom ξ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq₂ q (((π)^*[ModuleCat.{u + 1} Λ]).obj F))).hom := by
  subst wh₁ wh₂
  rfl

/-- The membership of the transported element in the image of the base-change map, in terms
of the derived maps at the sheaf placed in degree `0`. -/
lemma Etale.mem_range_baseChangeHomologyMap_iff (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T' Y' : Scheme.{u}} (π : T' ⟶ T) (e' : Y' ⟶ T') (h' : Y' ⟶ X)
    (sq' : IsPullback e' h' (π ≫ g) p) (a : Y' ⟶ Y) (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h') :
    ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeTargetTransition Λ e h q π a e' h' wa wh F)).hom ξ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq' q (((π)^*[ModuleCat.{u + 1} Λ]).obj F))).hom ↔
    ((X.uliftPointSmallEtale x).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.targetTransitionPlus Λ e h π a e' h' wa wh
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))).hom ξ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ q).map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq'.toCommSq).app
            (D+((π)^*[ModuleCat.{u + 1} Λ]).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))).hom := by
  have n := natTrans_app_comp_map_map (P₁ := R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]))
    (P₂ := D+((p)^*[ModuleCat.{u + 1} Λ])) (Q₁ := D+((e')^*[ModuleCat.{u + 1} Λ]))
    (Q₂ := R+((h')_*[ModuleCat.{u + 1} Λ])) (Etale.baseChange (ModuleCat.{u + 1} Λ) sq'.toCommSq)
    (X := D+((π)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    (Y := (DerivedCategory.Plus.singleFunctor _ 0).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F))
    ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
  rw [Etale.baseChangeTargetTransition_eq, Etale.baseChangeHomologyMap_eq_homologyFunctor_map,
    Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  symm
  refine mem_range_iff_of_comm' _ _
    ((X.uliftPointSmallEtale x).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
      (D+((p)^*[ModuleCat.{u + 1} Λ]).map (R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)))))
    _ ?_ _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, n]

end Survival

end AlgebraicGeometry
