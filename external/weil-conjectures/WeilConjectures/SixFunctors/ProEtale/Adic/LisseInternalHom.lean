/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The internal hom out of a lisse sheaf is exact

For a lisse sheaf `F` of `ℚ̄_ℓ,X`-modules, the internal hom `𝓗om_{ℚ̄_ℓ,X}(F, -)` is exact
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesFiniteColimits_ihom`): it is left exact
as a right adjoint, and it preserves epimorphisms since this can be checked after pullback along
the members of a pro-étale cover trivialising `F`, where `F` becomes `ℚ̄_ℓⁿ` and
`𝓗om(ℚ̄_ℓⁿ, -) = (-)ⁿ` (`CategoryTheory.Mod.epi_ihom_map_of_iso_biproduct`); weakly étale
pullback commutes with the internal hom (`AlgebraicGeometry.ProEtale.adicUpperStarIhomIso`).

For any morphism `g`, pullback commutes with the tensor product of modules
(`AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso`), which gives the projection formula
`g_* 𝓗om(g^* M, N) ≅ 𝓗om(M, g_* N)`
(`AlgebraicGeometry.ProEtale.adicLowerStarCompIhomUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- A sheaf of `ℚ̄_ℓ,X`-modules vanishes if its pullbacks along the members of a pro-étale cover
vanish. -/
lemma AdicSheaf.isZero_of_isZero_upperStar {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    [∀ i, WeaklyEtale (g i)] (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {M : AdicSheaf l X} (h : ∀ i, IsZero ((g i)^*ᵃ[l].obj M)) : IsZero M := by
  refine AdicSheaf.isZero_of_isZero_X ?_
  have : IsIso (0 : M.X ⟶ M.X) := by
    refine isIso_of_isIso_localizationRestriction _ _ g hg fun i ↦ ?_
    have hz : IsZero ((localizationRestriction _ (g i) inferInstance).obj M.X) :=
      ((AdicSheaf.forget _).map_isZero (h i)).of_iso
        ((upperStarIsoLocalizationRestriction _ (g i) inferInstance).app M.X).symm
    rw [hz.eq_of_src ((localizationRestriction _ (g i) inferInstance).map 0) (𝟙 _)]
    infer_instance
  exact (IsZero.iff_id_eq_zero _).2 (by rw [← IsIso.hom_inv_id (0 : M.X ⟶ M.X), zero_comp])

/-- **The internal hom out of a lisse sheaf preserves epimorphisms**: after pullback along a
member `g` of a pro-étale cover trivialising `F`, it becomes the internal hom out of `ℚ̄_ℓⁿ`. -/
theorem IsAdicLisseSheaf.epi_ihom_map {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F)
    {M N : AdicSheaf l X} (f : M ⟶ N) [Epi f] : Epi ((AdicSheaf.ihom F).map f) := by
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine Preadditive.epi_of_isZero_cokernel _
    (AdicSheaf.isZero_of_isZero_upperStar g hR fun i ↦ ?_)
  obtain ⟨n, ⟨e⟩⟩ := hRF (g i) (.mk i)
  have : Epi ((g i)^*ᵃ[l].map ((AdicSheaf.ihom F).map f)) := by
    have key := NatIso.naturality_2 (adicUpperStarIhomIso l (g i) F) f
    change Epi ((AdicSheaf.ihom F ⋙ (g i)^*ᵃ[l]).map f)
    rw [← key]
    have := Mod.epi_ihom_map_of_iso_biproduct e ((g i)^*ᵃ[l].map f)
    exact epi_comp' inferInstance (epi_comp' this inferInstance)
  exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso (g i)^*ᵃ[l] _)

/-- **The internal hom out of a lisse sheaf is exact**: it is left exact as a right adjoint,
and it preserves epimorphisms (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.epi_ihom_map`). -/
theorem IsAdicLisseSheaf.preservesFiniteColimits_ihom {F : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) : PreservesFiniteColimits (AdicSheaf.ihom F) := by
  have := (Mod.ihomAdjunction F).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (AdicSheaf.ihom F) := inferInstance
  refine (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2 fun S hS ↦ ?_
  have := hS.epi_g
  have h := (Functor.preservesFiniteLimits_tfae (AdicSheaf.ihom F)).out 4 1
  exact ⟨(h.1 ‹_› S hS).1, hF.epi_ihom_map S.g⟩

attribute [local instance] Abelian.hasFiniteBiproducts

/-- **Being lisse is local**: a sheaf whose pullbacks along the members of a pro-étale cover are
lisse is lisse, trivialised on the composite cover. -/
theorem IsAdicLisseSheaf.of_cover {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X) {M : AdicSheaf l X}
    (h : ∀ i, IsAdicLisseSheaf ((g i)^*ᵃ[l].obj M)) : IsAdicLisseSheaf M := by
  choose R hR hRM using h
  choose κ V f hf using fun i ↦ (R i).exists_eq_ofArrows
  refine ⟨_, Precoverage.comp_mem_coverings g hg f (fun i ↦ hf i ▸ hR i), ?_⟩
  rintro _ _ ⟨⟨i, k⟩⟩
  obtain ⟨n, ⟨e⟩⟩ := hRM i (f i k) (by rw [hf i]; exact .mk k)
  exact ⟨n, ⟨(adicUpperStarComp l _ _).app M ≪≫ e⟩⟩

/-- A finite direct sum of copies of a lisse sheaf is lisse. -/
theorem IsAdicLisseSheaf.biproduct_const {N : AdicSheaf l X} (hN : IsAdicLisseSheaf N) :
    ∀ n : ℕ, IsAdicLisseSheaf (⨁ fun _ : Fin n ↦ N)
  | 0 => IsAdicLisseSheaf.of_isZero
      ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
        fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩
  | n + 1 => ((IsAdicLisseSheaf.biproduct_const hN n).biprod
      (hN.of_iso (biproductUniqueIso (fun _ : Fin 1 ↦ N)).symm)).of_iso
      (biprodBiproductSumIso (fun _ : Fin n ⊕ Fin 1 ↦ N) ≪≫
        biproduct.whiskerEquiv (f := fun _ : Fin n ⊕ Fin 1 ↦ N) (g := fun _ : Fin (n + 1) ↦ N)
          finSumFinEquiv (fun _ ↦ Iso.refl _))

/-- **Pullback of an internal hom out of a lisse sheaf.** For `F` lisse and any morphism
`i : Y ⟶ X`, if `i^* G` is lisse then so is `i^* 𝓗om(F, G)`: on the base change of a cover
trivialising `F`, it becomes a finite direct sum of copies of the pullback of `i^* G`. -/
theorem IsAdicLisseSheaf.upperStar_ihom {Y : Scheme.{u}} (i : Y ⟶ X) {F G : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf ((i)^*ᵃ[l].obj G)) :
    IsAdicLisseSheaf ((i)^*ᵃ[l].obj ((AdicSheaf.ihom F).obj G)) := by
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨κ, V, g, rfl⟩ := R.exists_eq_ofArrows
  refine IsAdicLisseSheaf.of_cover (fun k ↦ pullback.fst i (g k))
    (Precoverage.mem_coverings_of_isPullback g hR i _ _
      fun k ↦ IsPullback.of_hasPullback i (g k)) fun k ↦ ?_
  have := Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk k)
  obtain ⟨n, ⟨e⟩⟩ := hRF (g k) (.mk k)
  let p := pullback.fst i (g k)
  let q := pullback.snd i (g k)
  have hpq : p ≫ i = q ≫ g k := pullback.condition
  refine (IsAdicLisseSheaf.biproduct_const (hG.upperStar p) n).of_iso
    ((adicUpperStarComp l p i).symm.app _ ≪≫ (adicUpperStarCongr l hpq).app _ ≪≫
      (adicUpperStarComp l q (g k)).app _ ≪≫
      (q)^*ᵃ[l].mapIso ((adicUpperStarIhomIso l (g k) F).app G ≪≫
        (Mod.ihomMapIso e).symm.app _ ≪≫ Mod.ihomBiproductIso _ _ ≪≫
        biproduct.mapIso fun _ ↦ Mod.ihomRegularIso.app _) ≪≫
      (q)^*ᵃ[l].mapBiproduct _ ≪≫
      biproduct.mapIso fun _ ↦ (adicUpperStarComp l q (g k)).symm.app G ≪≫
        (adicUpperStarCongr l hpq.symm).app G ≪≫ (adicUpperStarComp l p i).app G).symm

section ProjectionFormula

attribute [local instance] Sheaf.symmetricCategory

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y)

variable (l) in
/-- The ring isomorphism `ℚ̄_ℓ,Z ≅ g^* ℚ̄_ℓ,Y` along which `g^*` acts on modules, for any `g`. -/
noncomputable abbrev adicUpperStarRingHom : adicConstantSheaf l Z ⟶
    (g)^*[WeilCoefficients.{u} l].obj (adicConstantSheaf l Y) :=
  inv (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).homEquiv _ _).symm
    (adicConstantSheafToLowerStar l g))

variable (l) in
/-- **Pullback commutes with the tensor product of modules**: `g^*(P ⊗_A M) ≅ g^*P ⊗_A g^*M`,
for any morphism `g`. -/
noncomputable def adicUpperStarTensorLeftIso (M : AdicSheaf l Y) :
    Mod.tensorLeft M ⋙ (g)^*ᵃ[l] ≅ (g)^*ᵃ[l] ⋙ Mod.tensorLeft ((g)^*ᵃ[l].obj M) :=
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  Mod.tensorLeftCompMapModComapIso (adicUpperStarRingHom l g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _) M

variable (l) in
/-- **The projection formula for the internal hom**: `g_* 𝓗om(g^* M, N) ≅ 𝓗om(M, g_* N)`,
naturally in `N`, for any morphism `g`. The left adjoints `g^*(- ⊗_A M)` and
`g^* - ⊗_A g^* M` agree (`AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso`). -/
noncomputable def adicLowerStarCompIhomUpperStarIso (M : AdicSheaf l Y) :
    (g)_*ᵃ[l] ⋙ AdicSheaf.ihom M ≅ AdicSheaf.ihom ((g)^*ᵃ[l].obj M) ⋙ (g)_*ᵃ[l] :=
  conjugateIsoEquiv ((Mod.ihomAdjunction M).comp (adicUpperStarLowerStarAdjunction l g))
    ((adicUpperStarLowerStarAdjunction l g).comp (Mod.ihomAdjunction ((g)^*ᵃ[l].obj M)))
    (adicUpperStarTensorLeftIso l g M).symm

end ProjectionFormula

end AlgebraicGeometry.ProEtale
