/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.SectionsGalois

/-!
# Global sections of pullbacks in the two models of ℓ-adic sheaves

Morphisms `ℚ̄_ℓ ⟶ x^* H` of ℓ-adic sheaves give sections `𝟙 ⟶ x^* (E H)` of module
objects (`AlgebraicGeometry.ProEtale.condensedSectionOfAdicSection`), compatibly with the pullback
of sections along `σ` with `σ ≫ x = t`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {S T : Scheme.{u}}

/-- The pullback compatibility of the two models along equal morphisms. -/
lemma map_adicUpperStarCongr_hom_app_comp_adicUpperStarCompCondensedModIso_hom_app
    {g g' : S ⟶ T} (h : g = g') (H : AdicSheaf l T) :
    (adicSheafEquivCondensedMod l S).functor.map ((adicUpperStarCongr l h).hom.app H) ≫
        (adicUpperStarCompCondensedModIso l g').hom.app H =
      (adicUpperStarCompCondensedModIso l g).hom.app H ≫
        eqToHom (congrArg (fun s ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) s).obj
          ((adicSheafEquivCondensedMod l T).functor.obj H)) h) := by
  subst h
  rw [eqToHom_refl, Category.comp_id, adicUpperStarCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The pullback of global sections of `ℓ`-adic sheaves along `σ`, for `σ ≫ x̄ = x̄`. -/
noncomputable def adicUpperStarSectionMap {R : Scheme.{u}} (σ : S ⟶ R) (x : R ⟶ T)
    {t : S ⟶ T} (h : σ ≫ x = t)
    (H : AdicSheaf l T) (β : AdicSheaf.unit l R ⟶ (x)^*ᵃ[l].obj H) :
    AdicSheaf.unit l S ⟶ (t)^*ᵃ[l].obj H :=
  (adicUpperStarUnitIso l σ).inv ≫ (σ)^*ᵃ[l].map β ≫
      (adicUpperStarComp l σ x).inv.app H ≫
    (adicUpperStarCongr l h).hom.app H

/-- The global sections of the pullback of an `ℓ`-adic sheaf as global sections of the pullback
of the corresponding module object. -/
noncomputable def condensedSectionOfAdicSection (x : S ⟶ T) (H : AdicSheaf l T)
    (β : AdicSheaf.unit l S ⟶ (x)^*ᵃ[l].obj H) :
    𝟙ₘ ⟶ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) x).obj
      ((adicSheafEquivCondensedMod l T).functor.obj H) :=
  (adicSheafEquivCondensedModTensorUnitIso l S).inv ≫
      (adicSheafEquivCondensedMod l S).functor.map β ≫
    (adicUpperStarCompCondensedModIso l x).hom.app H

lemma adicSheafEquivCondensedModTensorUnitIso_inv_comp_map_adicUpperStarUnitIso_inv (σ : S ⟶ T) :
    (adicSheafEquivCondensedModTensorUnitIso l S).inv ≫
        (adicSheafEquivCondensedMod l S).functor.map (adicUpperStarUnitIso l σ).inv ≫
        (adicUpperStarCompCondensedModIso l σ).hom.app (AdicSheaf.unit l T) =
      (Functor.Monoidal.εIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) σ)).hom ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) σ).map
          (adicSheafEquivCondensedModTensorUnitIso l T).inv := by
  have h := upperStar_map_inv_comp_adicUpperStarCompCondensedModIso_inv_app_unit (l := l) σ
  have hI : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) σ).mapIso
        (adicSheafEquivCondensedModTensorUnitIso l T).symm ≪≫
      ((adicUpperStarCompCondensedModIso l σ).app (AdicSheaf.unit l T)).symm ≪≫
      (adicSheafEquivCondensedMod l S).functor.mapIso (adicUpperStarUnitIso l σ) ≪≫
      adicSheafEquivCondensedModTensorUnitIso l S =
      (Functor.Monoidal.εIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) σ)).symm :=
    Iso.ext (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv] using h)
  have h2 := congrArg (fun i ↦ i.inv) hI
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_hom, Category.assoc,
    ] at h2
  rw [← h2, Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

lemma map_adicUpperStarComp_inv_app_comp_adicUpperStarCompCondensedModIso_hom_app
    {R : Scheme.{u}} (g : S ⟶ R) (f : R ⟶ T) (H : AdicSheaf l T) :
    (adicSheafEquivCondensedMod l S).functor.map ((adicUpperStarComp l g f).inv.app H) ≫
        (adicUpperStarCompCondensedModIso l (g ≫ f)).hom.app H =
      (adicUpperStarCompCondensedModIso l g).hom.app ((f)^*ᵃ[l].obj H) ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).map
          ((adicUpperStarCompCondensedModIso l f).hom.app H) ≫
        (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) g f).inv.app
          ((adicSheafEquivCondensedMod l T).functor.obj H) := by
  have h := adicUpperStarCompCondensedModIso_inv_app_comp_map_adicUpperStarComp_hom_app (l := l)
    g f H
  have hI : ((adicUpperStarCompCondensedModIso l (g ≫ f)).app H).symm ≪≫
      (adicSheafEquivCondensedMod l S).functor.mapIso ((adicUpperStarComp l g f).app H) =
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) g f).app
          ((adicSheafEquivCondensedMod l T).functor.obj H) ≪≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).mapIso
          ((adicUpperStarCompCondensedModIso l f).app H).symm ≪≫
        ((adicUpperStarCompCondensedModIso l g).app ((f)^*ᵃ[l].obj H)).symm :=
    Iso.ext (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
      Iso.app_hom] using h)
  have h2 := congrArg (fun i ↦ i.inv) hI
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc] using h2

/-- Pulling back global sections is compatible with the comparison of the two models. -/
theorem condensedSectionOfAdicSection_adicUpperStarSectionMap {R : Scheme.{u}} (σ : S ⟶ R)
    (x : R ⟶ T) {t : S ⟶ T} (h : σ ≫ x = t) (H : AdicSheaf l T)
    (β : AdicSheaf.unit l R ⟶ (x)^*ᵃ[l].obj H) :
    condensedSectionOfAdicSection t H (adicUpperStarSectionMap σ x h H β) =
      CondensedRing.upperStarSectionMap (Profinite.padicAlgClRingObj l) σ h
        ((adicSheafEquivCondensedMod l T).functor.obj H) (condensedSectionOfAdicSection x H β) :=
            by
  rw [condensedSectionOfAdicSection, adicUpperStarSectionMap, condensedSectionOfAdicSection,
    CondensedRing.upperStarSectionMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [map_adicUpperStarCongr_hom_app_comp_adicUpperStarCompCondensedModIso_hom_app,
    reassoc_of% (map_adicUpperStarComp_inv_app_comp_adicUpperStarCompCondensedModIso_hom_app σ x
    H),
    ]
  have hn := (adicUpperStarCompCondensedModIso l σ).hom.naturality β
  rw [Functor.comp_map, Functor.comp_map] at hn
  rw [reassoc_of% hn,
    reassoc_of% (adicSheafEquivCondensedModTensorUnitIso_inv_comp_map_adicUpperStarUnitIso_inv σ)]

end AlgebraicGeometry.ProEtale
