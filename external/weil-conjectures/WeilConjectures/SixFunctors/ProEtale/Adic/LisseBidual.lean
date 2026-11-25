/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Bidual
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation
public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris

/-!
# Biduality for lisse `ℓ`-adic sheaves

The biduality morphism `M ⟶ 𝓗om(𝓗om(M, N), N)` of sheaves of `ℚ̄_ℓ,X`-modules
(`CategoryTheory.Mod.bidual`) is compatible with pullback along a weakly étale morphism `g`
through `g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)`
(`AlgebraicGeometry.ProEtale.adicUpperStar_map_bidual`). Hence for a lisse sheaf `F` the
biduality morphism `F ⟶ F^∨∨`, `F^∨ = 𝓗om(F, ℚ̄_ℓ)`, is an isomorphism
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_bidual`): this can be checked on a pro-étale
cover trivialising `F`, where it is biduality for the free module `ℚ̄_ℓⁿ`
(`CategoryTheory.Mod.isIso_bidual_of_iso_biproduct`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Sheaf.symmetricCategory

variable {V X : Scheme.{u}} (g : V ⟶ X) [WeaklyEtale g]

/-- The pullback along a weakly étale morphism of the biduality morphism
`M ⟶ 𝓗om(𝓗om(M, N), N)` is the biduality morphism of the pullbacks, through
`g^* 𝓗om(M, N) ≅ 𝓗om(g^* M, g^* N)`. -/
lemma adicUpperStar_map_bidual (M N : AdicSheaf l X) :
    (g)^*ᵃ[l].map (Mod.bidual M N) ≫
        (adicUpperStarIhomIso l g ((AdicSheaf.ihom M).obj N)).hom.app N ≫
          (Mod.ihomMap ((adicUpperStarIhomIso l g M).inv.app N)).app ((g)^*ᵃ[l].obj N) =
      Mod.bidual ((g)^*ᵃ[l].obj M) ((g)^*ᵃ[l].obj N) := by
  refine Mod.uncurryHom_injective ?_
  have h₁ : Mod.uncurryHom ((g)^*ᵃ[l].map (Mod.bidual M N) ≫
      (adicUpperStarIhomIso l g ((AdicSheaf.ihom M).obj N)).hom.app N) =
        (β_ ((g)^*ᵃ[l].obj M).X ((g)^*ᵃ[l].obj ((AdicSheaf.ihom M).obj N)).X).hom ≫
          ((adicUpperStarIhomIso l g M).hom.app N).hom ▷ ((g)^*ᵃ[l].obj M).X ≫
            Mod.evaluation ((g)^*ᵃ[l].obj M) ((g)^*ᵃ[l].obj N) := by
    rw [Mod.uncurryHom, Mod.comp_hom', comp_whiskerRight_assoc, adicUpperStarIhomIso_evaluation,
      adicUpperStarIhomIso_evaluation]
    refine (μ_natural_left_assoc (g)^*[WeilCoefficients.{u} l] (Mod.bidual M N).hom
      ((AdicSheaf.ihom M).obj N).X _).trans ?_
    rw [← Functor.map_comp, show (Mod.bidual M N).hom ▷ ((AdicSheaf.ihom M).obj N).X ≫
        Mod.evaluation ((AdicSheaf.ihom M).obj N) N = Mod.uncurryHom (Mod.bidual M N) from rfl,
      Mod.uncurryHom_bidual, Functor.map_comp, Functor.LaxBraided.braided_assoc]
    rfl
  rw [← Category.assoc, Mod.uncurryHom_comp_ihomMap, Mod.uncurryHom_bidual, h₁,
    BraidedCategory.braiding_naturality_right_assoc, ← comp_whiskerRight_assoc,
    ← Mod.comp_hom', Iso.inv_hom_id_app, Mod.id_hom', id_whiskerRight, Category.id_comp]
  rfl

/-- **Biduality for lisse sheaves.** For a lisse sheaf `F` of `ℚ̄_ℓ,X`-modules, the biduality
morphism `F ⟶ 𝓗om(𝓗om(F, ℚ̄_ℓ), ℚ̄_ℓ)` is an isomorphism. -/
theorem IsAdicLisseSheaf.isIso_bidual {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F) :
    IsIso (Mod.bidual F (AdicSheaf.unit l X)) := by
  obtain ⟨R, hR, h⟩ := hF
  obtain ⟨ι, W, f, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine isIso_of_isIso_adicUpperStar l f hR _ fun i ↦ ?_
  obtain ⟨n, ⟨e⟩⟩ := h (f i) (.mk i)
  have := Mod.isIso_bidual_of_iso_biproduct e (adicUpperStarUnitIso l (f i)).symm
  have := Mod.isIso_ihomMap_app ((adicUpperStarIhomIso l (f i) F).inv.app (AdicSheaf.unit l X))
    ((f i)^*ᵃ[l].obj (AdicSheaf.unit l X))
  have h' := adicUpperStar_map_bidual (f i) F (AdicSheaf.unit l X)
  rw [← Category.assoc] at h'
  have : IsIso ((f i)^*ᵃ[l].map (Mod.bidual F (AdicSheaf.unit l X)) ≫
      (adicUpperStarIhomIso l (f i) ((AdicSheaf.ihom F).obj (AdicSheaf.unit l X))).hom.app
        (AdicSheaf.unit l X)) := by
    have : IsIso (((f i)^*ᵃ[l].map (Mod.bidual F (AdicSheaf.unit l X)) ≫
        (adicUpperStarIhomIso l (f i) ((AdicSheaf.ihom F).obj (AdicSheaf.unit l X))).hom.app
          (AdicSheaf.unit l X)) ≫ (Mod.ihomMap ((adicUpperStarIhomIso l (f i) F).inv.app
            (AdicSheaf.unit l X))).app ((f i)^*ᵃ[l].obj (AdicSheaf.unit l X))) := by
      rw [h']
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((Mod.ihomMap ((adicUpperStarIhomIso l (f i) F).inv.app
      (AdicSheaf.unit l X))).app ((f i)^*ᵃ[l].obj (AdicSheaf.unit l X)))
  exact IsIso.of_isIso_comp_right _ ((adicUpperStarIhomIso l (f i)
    ((AdicSheaf.ihom F).obj (AdicSheaf.unit l X))).hom.app (AdicSheaf.unit l X))

end AlgebraicGeometry.ProEtale
