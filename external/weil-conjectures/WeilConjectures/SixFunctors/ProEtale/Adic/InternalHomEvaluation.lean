/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom

/-!
# Evaluation of internal homs of `ℓ`-adic sheaves and weakly étale pullback

The evaluation `𝓗om(M, N) ⊗ M ⟶ N` of sheaves of `ℚ̄_ℓ,X`-modules is the restriction of the
evaluation of the internal hom of sheaves along `𝓗om_{ℚ̄_ℓ}(M, N) ⊆ [M, N]`
(`AlgebraicGeometry.ProEtale.AdicSheaf.evaluation_eq`). Hence the identification
`g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)` for a weakly étale `g`
(`AlgebraicGeometry.ProEtale.adicUpperStarIhomIso`) is compatible with the evaluations
(`AlgebraicGeometry.ProEtale.adicUpperStarIhomIso_evaluation`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Functor.LaxMonoidal Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Sheaf.symmetricCategory

/-- The evaluation of the internal hom of sheaves of modules through the equalizer description
`𝓗om_{ℚ̄_ℓ}(M, N) ⊆ [M, N]`. -/
lemma AdicSheaf.evaluation_eq {X : Scheme.{u}} (M N : AdicSheaf l X) :
    Mod.evaluation M N =
      ((AdicSheaf.ihomIsoIhom' M).hom.app N).hom ▷ M.X ≫ (β_ M.X _).inv ≫
        M.X ◁ (equalizer.ι (Mod.homModPre (Mod.act M.X) N) (Mod.homModB _ M N)).hom ≫
          (ihom.ev M.X).app N.X := by
  have h₁ : (Mod.ihomAdjunction M).counit.app N =
      (Mod.tensorLeft M).map ((AdicSheaf.ihomIsoIhom' M).hom.app N) ≫
        (Mod.ihom'Adjunction _ M).counit.app N :=
    ((Mod.ihomAdjunction M).rightAdjointUniq_hom_app_counit (Mod.ihom'Adjunction _ M) N).symm
  have h₂ : Mod.tensorπ _ M ≫ ((Mod.ihom'Adjunction _ M).counit.app N).hom =
      (β_ M.X _).inv ≫ M.X ◁ (equalizer.ι (Mod.homModPre (Mod.act M.X) N)
        (Mod.homModB _ M N)).hom ≫ (ihom.ev M.X).app N.X := by
    change (colimit.ι _ _ ≫ colimit.desc _ (Mod.ihomCocone (𝟙 _))).hom = _
    rw [colimit.ι_desc]
    change (Mod.ihomDesc (𝟙 _)).hom = _
    rw [Mod.ihomDesc_hom, Category.id_comp, uncurry_eq]
    rfl
  rw [Mod.evaluation, h₁, Mod.comp_hom', Mod.tensorπ_map_assoc, h₂]
  rfl

variable {V X : Scheme.{u}} (g : V ⟶ X) [WeaklyEtale g]

/-- The identification `g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)` for a weakly étale `g` is compatible
with the evaluations. -/
lemma adicUpperStarIhomIso_evaluation (M N : AdicSheaf l X) :
    ((adicUpperStarIhomIso l g M).hom.app N).hom ▷ ((g)^*ᵃ[l].obj M).X ≫
        Mod.evaluation ((g)^*ᵃ[l].obj M) ((g)^*ᵃ[l].obj N) =
      μ (g)^*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.evaluation M N) := by
  have hβ (P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
      μ (g)^*[WeilCoefficients.{u} l] Q P ≫ (g)^*[_].map (β_ P Q).inv =
        (β_ ((g)^*[_].obj P) ((g)^*[_].obj Q)).inv ≫ μ (g)^*[WeilCoefficients.{u} l] P Q := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← Functor.LaxBraided.braided, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  have hc : ((adicUpperStarIhomIso l g M).hom.app N).hom ≫
      ((AdicSheaf.ihomIsoIhom' ((g)^*ᵃ[l].obj M)).hom.app ((g)^*ᵃ[l].obj N)).hom =
        (g)^*[WeilCoefficients.{u} l].map ((AdicSheaf.ihomIsoIhom' M).hom.app N).hom ≫
          (Mod.mapIhom'Hom (g)^*[WeilCoefficients.{u} l] (adicUpperStarRingIso g) M N).hom := by
    simp only [adicUpperStarIhomIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
      asIso_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
      Mod.comp_hom', Category.assoc]
    rw [← Mod.comp_hom', Iso.inv_hom_id_app, Mod.id_hom']
    erw [Category.comp_id]
    rfl
  have hι := congrArg Mod.Hom.hom
    (Mod.mapIhom'Hom_ι (g)^*[WeilCoefficients.{u} l] (adicUpperStarRingIso g) M N)
  simp only [Mod.comp_hom'] at hι
  rw [AdicSheaf.evaluation_eq, AdicSheaf.evaluation_eq, ← comp_whiskerRight_assoc, hc,
    comp_whiskerRight_assoc, BraidedCategory.braiding_inv_naturality_left_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [hι, MonoidalCategory.whiskerLeft_comp_assoc]
  rw [Mod.mapHomModHom_hom]
  have hev := ihomComparison_ev (g)^*[WeilCoefficients.{u} l] M.X N.X
  erw [hev]
  conv_rhs => rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  erw [← μ_natural_left_assoc, reassoc_of% hβ, ← μ_natural_right_assoc]
  rfl

end AlgebraicGeometry.ProEtale
