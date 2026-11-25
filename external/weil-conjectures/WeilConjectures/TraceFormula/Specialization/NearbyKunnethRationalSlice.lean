/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModelPair
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangePadicAlgClIff
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseHypotheses
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFormula
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethProper

/-!

# Gabber's Künneth formula with `ℚ̄_ℓ`-coefficients from the `𝒪_E` ones

Bounded constructible `ℚ̄_ℓ`-complexes `A`, `B` on noetherian schemes have integral models
`A₀`, `B₀` over the ring of integers `𝒪_E` of a common finite subextension `E ⊆ ℚ̄_ℓ`
(`ProEtale.exists_derivedExtendScalars_iso_integralModel_pair`), and the Künneth map `Π_{A,B}`
is, up to isomorphism, `ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} Π_{A₀,B₀}`
(`NearbyCyclesModel.isIso_map_map_kunnethMap_iff_padicAlgCl`). This file deduces:

* the generic-slicing step with `ℚ̄_ℓ`-coefficients from the ones with `𝒪_E`-coefficients
  (`NearbyCyclesModel.sliceKunnethFormula_padicAlgCl`);
* Gabber's Künneth formula for proper models with `ℚ̄_ℓ`-coefficients from the one with
  `𝒪_E`-coefficients (`NearbyCyclesModel.properKunnethFormula_padicAlgCl_of_integral`), hence
  Gabber's Künneth formula with `ℚ̄_ℓ`-coefficients
  (`NearbyCyclesModel.kunnethFormula_padicAlgCl_of_integral`), by the reduction to proper models
  (`NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

-- the Künneth maps of the derived categories of module objects are large terms
/-- The image `G(Π_{A,B})` of the Künneth map under a functor `G` is invertible if `G(Π_{A',B'})`
is, for `A ≅ A'` and `B ≅ B'`. -/
lemma isIso_map_kunnethMap_of_iso {D : Type*} [Category D]
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
      (condensedRingObj Λ Z')) ⥤ D) (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (a : A ≅ A') (b : B ≅ B')
    (h : IsIso (G.map (kunnethMap Λ φ₁ φ₂ A' B'))) : IsIso (G.map (kunnethMap Λ φ₁ φ₂ A B)) := by
  refine ((MorphismProperty.isomorphisms D).arrow_mk_iso_iff (Arrow.isoMk
    (G.mapIso (L((f₁')^*⟦Λ⟧).mapIso ((M.nearbyCycles Λ).mapIso a) ⊗ᵢ
      L((f₂')^*⟦Λ⟧).mapIso ((N.nearbyCycles Λ).mapIso b)))
    (G.mapIso ((P.nearbyCycles Λ).mapIso (L((f₁)^*⟦Λ⟧).mapIso a ⊗ᵢ L((f₂)^*⟦Λ⟧).mapIso b)))
    ?_)).2 h
  simp only [Arrow.mk_hom, Functor.mapIso_hom, tensorIso_hom, ← G.map_comp]
  rw [kunnethMap_naturality Λ φ₁ φ₂ a.hom b.hom]

end General

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

private lemma exists_tensor_isGE_of_boundedConstructible
    {ℓ : ℕ} [Fact ℓ.Prime] {X Y Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] [TopologicalSpace.NoetherianSpace Y]
    [TopologicalSpace.NoetherianSpace Z]
    {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y} (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hA₀ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) A₀)
    {B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))}
    (hB₀ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y) B₀) :
    ∃ c : ℤ, (L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀).IsGE c := by
  have hAB : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)
      (L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
        L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀) :=
    boundedConstructible_tensorObj
      (PadicIntegersRingObj.lisseHypotheses ℓ E.1).toLisseTensorHypotheses
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₁ A₀ hA₀)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₂ B₀ hB₀)
  exact hAB.1.1

private lemma sliceKunnethFormula_padicAlgCl_isIso {n : ℕ}
    (h : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SliceKunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' n) :
    SliceKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' n := by
  refine ⟨?_⟩
  intro X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂' φ₁ φ₂ qM gM qN gN hM hN hpb hP hgen hX hY hZ b hb
    m₁ m₂ hle h₁ h₂ eM heM eN heN A B hA hB
  have hmodels := ProEtale.exists_derivedExtendScalars_iso_integralModel_pair X Y ℓ ⟨A, hA⟩ ⟨B, hB⟩
  rcases hmodels with ⟨E, A₀, B₀, eA, eB⟩
  rcases eA with ⟨eA⟩
  rcases eB with ⟨eB⟩
  let s := baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
    (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k'))
  have h₀ : IsIso (L((s)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).map
      (kunnethMap (Profinite.padicIntegersRingObj ℓ E.1) φ₁ φ₂ A₀.obj B₀.obj)) := by
    exact (h E).isIso φ₁ φ₂ hM hN hpb hP hgen hX hY hZ hb hle h₁ h₂ heM heN A₀.2 B₀.2
  -- bounds below of `A₀`, `B₀` and of their external product
  have ha : A₀.obj.IsGE A₀.2.1.1.choose := A₀.2.1.1.choose_spec
  have ha' : B₀.obj.IsGE B₀.2.1.1.choose := B₀.2.1.1.choose_spec
  have : A₀.obj.IsGE (min A₀.2.1.1.choose B₀.2.1.1.choose) :=
    DerivedCategory.TStructure.t.isGE_of_ge A₀.obj _ _ (min_le_left _ _)
  have : B₀.obj.IsGE (min A₀.2.1.1.choose B₀.2.1.1.choose) :=
    DerivedCategory.TStructure.t.isGE_of_ge B₀.obj _ _ (min_le_right _ _)
  obtain ⟨c, hc⟩ := exists_tensor_isGE_of_boundedConstructible E (X := X) (Y := Y) (Z := Z)
    (f₁ := f₁) (f₂ := f₂) (A₀ := A₀.obj) (B₀ := B₀.obj) A₀.2 B₀.2
  have : QuasiCompact M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip inferInstance
  have : QuasiSeparated M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip inferInstance
  have : QuasiCompact N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip inferInstance
  have : QuasiSeparated N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip inferInstance
  have : QuasiCompact P.j := MorphismProperty.of_isPullback hP.isPullback_j.flip inferInstance
  have : QuasiSeparated P.j := MorphismProperty.of_isPullback hP.isPullback_j.flip inferInstance
  have key := (isIso_map_map_map_kunnethMap_iff_padicAlgCl ℓ E φ₁ φ₂
    s A₀.obj B₀.obj (min A₀.2.1.1.choose B₀.2.1.1.choose) c).1 (Functor.map_isIso _ _)
  simpa only [s] using isIso_map_kunnethMap_of_iso _ _ φ₁ φ₂ eA.symm eB.symm key

-- the Künneth maps of the derived categories of module objects are large terms
/-- **The generic-slicing step with `ℚ̄_ℓ`-coefficients from the `𝒪_E` ones** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Finite support"): if the generic-slicing step
holds with `𝒪_E`-coefficients in chart dimension `n` for every finite subextension `E ⊆ ℚ̄_ℓ`, it
holds with `ℚ̄_ℓ`-coefficients. Bounded constructible `A`, `B` on the noetherian schemes `X`, `Y`
have integral models `A₀`, `B₀` over a common `𝒪_E`
(`ProEtale.exists_derivedExtendScalars_iso_integralModel_pair`), and the pullback of `Π_{A,B}` is
invertible since that of `Π_{A₀,B₀}` is
(`NearbyCyclesModel.isIso_map_map_map_kunnethMap_iff_padicAlgCl`). -/
theorem sliceKunnethFormula_padicAlgCl {n : ℕ}
    (h : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SliceKunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' n) :
    SliceKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' n :=
  sliceKunnethFormula_padicAlgCl_isIso h

-- the Künneth maps of the derived categories of module objects are large terms
/-- **Gabber's Künneth formula for proper models with `ℚ̄_ℓ`-coefficients from the `𝒪_E` ones**
(blueprint `proposition-external-kunneth-formula-nearby-cycles`): if Gabber's Künneth formula with
`𝒪_E`-coefficients holds in chart dimension `n` for every finite subextension `E ⊆ ℚ̄_ℓ`, then
the Künneth formula for proper models with `ℚ̄_ℓ`-coefficients holds in chart dimension `n`
(`NearbyCyclesModel.ProperKunnethFormula`). Bounded constructible `A`, `B` on the noetherian
schemes `X`, `Y` have integral models `A₀`, `B₀` over a common `𝒪_E`
(`ProEtale.exists_derivedExtendScalars_iso_integralModel_pair`), and `Π_{A,B}` is invertible
since `Π_{A₀,B₀}` is (`NearbyCyclesModel.isIso_map_map_kunnethMap_iff_padicAlgCl`). -/
theorem properKunnethFormula_padicAlgCl_of_integral {n : ℕ}
    (h : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      KunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' n) :
    ProperKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' n := by
  intro X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂' φ₁ φ₂ qM gM qN gN hM hN hpb hP hgen _ _ hX hY _ m₁ m₂
    hle h₁ h₂ eM heM eN heN A B hA hB
  obtain ⟨E, A₀, B₀, ⟨eA⟩, ⟨eB⟩⟩ :=
    ProEtale.exists_derivedExtendScalars_iso_integralModel_pair X Y ℓ ⟨A, hA⟩ ⟨B, hB⟩
  have h₀ := h E φ₁ φ₂ hM hN hpb hP hgen hle h₁ h₂ heM heN A₀.2 B₀.2
  -- bounds below of `A₀`, `B₀` and of their external product
  obtain ⟨a, ha⟩ := A₀.2.1.1
  obtain ⟨a', ha'⟩ := B₀.2.1.1
  have : A₀.obj.IsGE (min a a') :=
    DerivedCategory.TStructure.t.isGE_of_ge A₀.obj _ _ (min_le_left a a')
  have : B₀.obj.IsGE (min a a') :=
    DerivedCategory.TStructure.t.isGE_of_ge B₀.obj _ _ (min_le_right a a')
  have hAB : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)
      (L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀.obj ⊗
        L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀.obj) :=
    boundedConstructible_tensorObj
      (PadicIntegersRingObj.lisseHypotheses ℓ E.1).toLisseTensorHypotheses
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₁ A₀.obj A₀.2)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₂ B₀.obj B₀.2)
  obtain ⟨c, hc⟩ := hAB.1.1
  have : QuasiCompact M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip inferInstance
  have : QuasiSeparated M.j := MorphismProperty.of_isPullback hM.isPullback_j.flip inferInstance
  have : QuasiCompact N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip inferInstance
  have : QuasiSeparated N.j := MorphismProperty.of_isPullback hN.isPullback_j.flip inferInstance
  have : QuasiCompact P.j := MorphismProperty.of_isPullback hP.isPullback_j.flip inferInstance
  have : QuasiSeparated P.j := MorphismProperty.of_isPullback hP.isPullback_j.flip inferInstance
  have key := (isIso_map_map_kunnethMap_iff_padicAlgCl ℓ E φ₁ φ₂ A₀.obj B₀.obj (min a a') c).1
    (Functor.map_isIso _ _)
  exact isIso_kunnethMap_of_iso _ φ₁ φ₂ eA.symm eB.symm key

/-- **Gabber's Künneth formula with `ℚ̄_ℓ`-coefficients from the `𝒪_E` ones** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`): if Gabber's Künneth formula with
`𝒪_E`-coefficients holds in chart dimension `n` for every finite subextension `E ⊆ ℚ̄_ℓ`, so does
the one with `ℚ̄_ℓ`-coefficients. By the reduction to proper models
(`NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula`), this is
`NearbyCyclesModel.properKunnethFormula_padicAlgCl_of_integral`. -/
theorem kunnethFormula_padicAlgCl_of_integral {n : ℕ}
    (h : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      KunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' n) :
    KunnethFormula (Profinite.padicAlgClRingObj ℓ) k' n := by
  intro X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂' φ₁ φ₂ qM gM qN gN hM hN hpb hP hgen m₁ m₂ hle h₁ h₂ eM
    heM eN heN A B hA hB
  exact isIso_kunnethMap_of_properKunnethFormula (properKunnethFormula_padicAlgCl_of_integral h) hM
    hN hpb hP hgen hle h₁ h₂ heM heN hA hB

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
