/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom

/-!
# A criterion for a curried pairing to be an isomorphism

Let `π : W ⟶ Y` be a quasi-compact surjective weakly étale morphism. Pullback along `π` is
faithful on sheaves of `ℚ̄_ℓ`-modules (`AlgebraicGeometry.ProEtale.AdicSheaf.faithful_upperStar`),
hence reflects isomorphisms.

Let `κ : M ⟶ 𝓗om(D, N)` be a morphism of sheaves of `ℚ̄_ℓ,Y`-modules such that `π^* M`, `π^* D`,
`π^* N` are trivialised by isomorphisms with `ℚ̄_ℓ,W` under which the uncurried pairing
`π^* M ⊗ π^* D ⟶ π^* N` becomes the multiplication of `ℚ̄_ℓ,W`. Then `κ` is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_of_upperStar_uncurry_eq_mul`): after pullback along `π` and
transport along the trivialisations, it becomes the inverse of the isomorphism
`𝓗om(ℚ̄_ℓ, ℚ̄_ℓ) ≅ ℚ̄_ℓ` (`CategoryTheory.Mod.ihomRegularIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Sheaf.symmetricCategory

/-- A morphism of sheaves of `ℚ̄_ℓ,Y`-modules vanishes if its pullback along a quasi-compact
surjective weakly étale morphism does: its image vanishes, being detected on the pullback
(`AlgebraicGeometry.ProEtale.AdicSheaf.isZero_of_isZero_upperStar`). -/
lemma AdicSheaf.eq_zero_of_upperStar_map_eq_zero {W Y : Scheme.{u}} (π : W ⟶ Y)
    [WeaklyEtale π] [QuasiCompact π] [Surjective π] {M N : AdicSheaf l Y} (f : M ⟶ N)
    (hf : (π)^*ᵃ[l].map f = 0) : f = 0 := by
  have hz : IsZero (Abelian.image f) := by
    refine AdicSheaf.isZero_of_isZero_upperStar (fun _ : PUnit.{u + 1} ↦ π) ?_ fun _ ↦ ?_
    · rw [Presieve.ofArrows_pUnit]
      exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
    · refine IsZero.of_iso ?_ (Abelian.PreservesImage.iso (π)^*ᵃ[l] f)
      have : Abelian.factorThruImage ((π)^*ᵃ[l].map f) = 0 := by
        rw [← cancel_mono (Abelian.image.ι _), Abelian.image.fac, zero_comp]
        exact hf
      exact IsZero.of_epi_eq_zero _ this
  rw [← Abelian.image.fac f, hz.eq_of_src (Abelian.image.ι f) 0, comp_zero]

/-- The pullback along a quasi-compact surjective weakly étale morphism is faithful. -/
lemma AdicSheaf.faithful_upperStar {W Y : Scheme.{u}} (π : W ⟶ Y) [WeaklyEtale π]
    [QuasiCompact π] [Surjective π] : (π)^*ᵃ[l].Faithful where
  map_injective {_ _} f g hfg := by
    rw [← sub_eq_zero]
    exact AdicSheaf.eq_zero_of_upperStar_map_eq_zero π _
      (by rw [Functor.map_sub, hfg, sub_self])

/-- The pullback along a quasi-compact surjective weakly étale morphism reflects isomorphisms,
being faithful on a balanced category. -/
lemma AdicSheaf.reflectsIsomorphisms_upperStar {W Y : Scheme.{u}} (π : W ⟶ Y) [WeaklyEtale π]
    [QuasiCompact π] [Surjective π] : (π)^*ᵃ[l].ReflectsIsomorphisms :=
  have := AdicSheaf.faithful_upperStar (l := l) π
  have : (π)^*ᵃ[l].ReflectsMonomorphisms := Functor.reflectsMonomorphisms_of_faithful _
  have : (π)^*ᵃ[l].ReflectsEpimorphisms := Functor.reflectsEpimorphisms_of_faithful _
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms _

/-- The uncurried form of `Hom_A(A, A) ≅ A` is the multiplication of `A`. -/
lemma AdicSheaf.uncurryHom_ihomRegularIso_inv (W : Scheme.{u}) :
    Mod.uncurryHom (Mod.ihomRegularIso.inv.app (AdicSheaf.unit l W)) =
      MonObj.mul (X := adicConstantSheaf l W) := by
  have hc : (Mod.ihomRegularIso.inv.app (AdicSheaf.unit l W) ≫
      Mod.ihomRegularIso.hom.app _).hom = 𝟙 _ := by
    rw [Iso.inv_hom_id_app]
    rfl
  rw [Mod.comp_hom'] at hc
  rw [Mod.uncurryHom, Mod.evaluation_regular]
  erw [← comp_whiskerRight_assoc, hc, id_whiskerRight, Category.id_comp]
  exact IsCommMonObj.mul_comm (adicConstantSheaf l W)

/-- **A criterion for a curried pairing to be an isomorphism.** Let `κ : M ⟶ 𝓗om(D, N)` and
let `π` be a quasi-compact surjective weakly étale morphism. If `π^* M`, `π^* D`, `π^* N` are
identified with `ℚ̄_ℓ` such that the uncurried pairing `π^* M ⊗ π^* D ⟶ π^* N` becomes the
multiplication, then `κ` is an isomorphism. -/
theorem isIso_of_upperStar_uncurry_eq_mul {Y W : Scheme.{u}} (π : W ⟶ Y) [WeaklyEtale π]
    [QuasiCompact π] [Surjective π] {M D N : AdicSheaf l Y} (κ : M ⟶ (AdicSheaf.ihom D).obj N)
    (eM : (π)^*ᵃ[l].obj M ≅ AdicSheaf.unit l W) (eD : (π)^*ᵃ[l].obj D ≅ AdicSheaf.unit l W)
    (eN : (π)^*ᵃ[l].obj N ≅ AdicSheaf.unit l W)
    (h : (eM.inv.hom ⊗ₘ eD.inv.hom) ≫ μ (π)^*[WeilCoefficients.{u} l] M.X D.X ≫
      (π)^*[WeilCoefficients.{u} l].map (κ.hom ▷ D.X ≫ Mod.evaluation D N) ≫ eN.hom.hom =
        MonObj.mul (X := adicConstantSheaf l W)) :
    IsIso κ := by
  have := AdicSheaf.reflectsIsomorphisms_upperStar (l := l) π
  let e : (AdicSheaf.ihom D ⋙ (π)^*ᵃ[l]).obj N ≅ (AdicSheaf.ihom (AdicSheaf.unit l W)).obj
      (AdicSheaf.unit l W) :=
    (adicUpperStarIhomIso l π D).app N ≪≫ (AdicSheaf.ihom ((π)^*ᵃ[l].obj D)).mapIso eN ≪≫
      (Mod.ihomMapIso eD.symm).app _
  have key : eM.inv ≫ (π)^*ᵃ[l].map κ ≫ e.hom =
      Mod.ihomRegularIso.inv.app (AdicSheaf.unit l W) := by
    refine Mod.uncurryHom_injective
      (Eq.trans ?_ (AdicSheaf.uncurryHom_ihomRegularIso_inv W).symm)
    rw [← h]
    simp only [e, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    change Mod.uncurryHom (((eM.inv ≫ (π)^*ᵃ[l].map κ ≫
      (adicUpperStarIhomIso l π D).hom.app N) ≫
      (AdicSheaf.ihom ((π)^*ᵃ[l].obj D)).map eN.hom) ≫ (Mod.ihomMap eD.inv).app _) = _
    rw [Mod.uncurryHom_comp_ihomMap, Mod.uncurryHom_comp_ihom_map, Mod.uncurryHom_comp,
      Mod.uncurryHom_comp, Mod.uncurryHom, adicUpperStarIhomIso_evaluation, tensorHom_def',
      Category.assoc, Functor.map_comp]
    have hn : ((π)^*ᵃ[l].map κ).hom ▷ ((π)^*ᵃ[l].obj D).X ≫
        μ (π)^*[WeilCoefficients.{u} l] ((AdicSheaf.ihom D).obj N).X D.X =
          μ (π)^*[WeilCoefficients.{u} l] M.X D.X ≫
            (π)^*[WeilCoefficients.{u} l].map (κ.hom ▷ D.X) :=
      μ_natural_left (π)^*[WeilCoefficients.{u} l] κ.hom D.X
    simp only [Category.assoc]
    rw [reassoc_of% hn]
  have : IsIso ((π)^*ᵃ[l].map κ) := by
    have h₁ : IsIso (eM.inv ≫ (π)^*ᵃ[l].map κ ≫ e.hom) := by
      rw [key]
      infer_instance
    have h₂ : IsIso ((π)^*ᵃ[l].map κ ≫ e.hom) := IsIso.of_isIso_comp_left eM.inv _
    exact IsIso.of_isIso_comp_right _ e.hom
  exact isIso_of_reflects_iso κ (π)^*ᵃ[l]

end AlgebraicGeometry.ProEtale
