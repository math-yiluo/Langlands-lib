/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ThickOrigin
public import WeilConjectures.TraceFormula.Specialization.ThickOriginPow

/-!

# The fibre of the power model over the zero section

Let `J ⊆ I^m` with `I^m ⊆ J` and let `ν : 𝒟_I ⟶ 𝒟_J` be the power map of the deformations to the
normal cones over the trait. A point of the special fibre of `𝒟_I` whose image lies on the zero
section of the special fibre of `𝒟_J` lies on the zero section of `𝒟_I`
(`ProEtale.CondensedRing.mem_range_zeroSectionSpecialFibreMap_of_powMap`): this is the
set-theoretic equality `ν⁻¹(V(J t⁻¹)) = V(I t⁻¹)` of
`IdealSheafData.mem_range_deformationSpaceMap_subschemeι_of_deformationSpacePowMap`, transported
along the cartesian squares relating the deformation spaces, the total spaces over the trait and
their special fibres.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (k' : Type u) [Field k'] {m : ℕ} (hm : m ≠ 0) {k : Type u} [Field k] [Algebra k k']
  (X : Over (Spec (.of k))) {I J : X.left.IdealSheafData}
  (hJ : ∀ U : X.left.AffineZariskiSite, J.siteIdeal U ≤ I.siteIdeal U ^ m)
  (hJ' : ∀ U : X.left.AffineZariskiSite, I.siteIdeal U ^ m ≤ J.siteIdeal U)
  (hσ : traitPowMap k' m hm ≫ traitToAffineLine k k' =
    traitToAffineLine k k' ≫ affineLinePowMap k m)

include hJ' in
/-- A point of the special fibre of `𝒟_I` lying over the zero section of `𝒟_J` lies on the zero
section of `𝒟_I`. -/
theorem mem_range_zeroSectionSpecialFibreMap_of_powMap
    (y : (deformationSpecialFibre X I k').left)
    (hy : deformationSpecialFibrePowMap k' hm X I J (IdealSheafData.deformationSpacePowMap m hJ)
      (affineLinePowMap k m) (deformationSpacePowMap_deformationSpaceToAffineLine hJ) hσ y ∈
        Set.range (zeroSectionSpecialFibreMap X J k').left) :
    y ∈ Set.range (zeroSectionSpecialFibreMap X I k').left := by
  set ν₀ := IdealSheafData.deformationSpacePowMap m hJ
  set ν := deformationTotalPowMap k' hm X I J ν₀ (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine hJ) hσ
  obtain ⟨ζ, hζ⟩ := hy
  -- the image in `D_J X` lies on the zero section
  have h₁ : ν₀ (deformationTotalToSpace X I k' (deformationSpecialToTotal X I k' y)) ∈
      Set.range (IdealSheafData.deformationSpaceMap J.subschemeι J ⊥
        J.siteIdeal_map_appLE_subschemeι_le_bot) := by
    refine ⟨deformationTotalToSpace (centre X J) ⊥ k'
      (deformationSpecialToTotal (centre X J) ⊥ k' ζ), ?_⟩
    have e₁ : (zeroSectionSpecialFibreMap X J k').left ≫ deformationSpecialToTotal X J k' ≫
        deformationTotalToSpace X J k' = deformationSpecialToTotal (centre X J) ⊥ k' ≫
          deformationTotalToSpace (centre X J) ⊥ k' ≫
            IdealSheafData.deformationSpaceMap J.subschemeι J ⊥
              J.siteIdeal_map_appLE_subschemeι_le_bot := by
      rw [zeroSectionSpecialFibreMap, deformationSpecialFibreMap_toTotal_assoc,
        deformationTotalMap_toSpace]
      rfl
    have e₂ : deformationSpecialFibrePowMap k' hm X I J ν₀ (affineLinePowMap k m)
        (deformationSpacePowMap_deformationSpaceToAffineLine hJ) hσ ≫
        deformationSpecialToTotal X J k' ≫ deformationTotalToSpace X J k' =
        deformationSpecialToTotal X I k' ≫ deformationTotalToSpace X I k' ≫ ν₀ := by
      rw [deformationSpecialFibrePowMap, ← Category.assoc]
      erw [pullback.lift_fst]
      rw [Category.assoc, deformationTotalPowMap_toSpace]
    have := congr($(e₁).base ζ)
    have h₂ := congr($(e₂).base y)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this h₂
    rw [← h₂, ← hζ, this]
  -- hence the point of `D_I X` lies on the zero section
  obtain ⟨u, hu⟩ :=
    IdealSheafData.mem_range_deformationSpaceMap_subschemeι_of_deformationSpacePowMap hJ hJ' h₁
  -- lift to the total space and to the special fibre of the constant family of the centre
  obtain ⟨v, hv₁, hv₂⟩ := (isPullback_deformationTotalMap_toSpace (centreι X I)
    (siteIdeal_map_appLE_le_bot X I) k').exists_scheme_point
    (deformationSpecialToTotal X I k' y) u hu.symm
  obtain ⟨w, hw₁, hw₂⟩ := (isPullback_deformationSpecialFibreMap_toTotal (centreι X I)
    (siteIdeal_map_appLE_le_bot X I) k').exists_scheme_point y v hv₁.symm
  exact ⟨w, hw₁⟩


/-- The power map of the special fibres maps the zero section of `𝒟_I` into the zero section of
`𝒟_J`. -/
theorem deformationSpecialFibrePowMap_mem_range_zeroSectionSpecialFibreMap (hm₀ : 0 < m)
    (z : (deformationSpecialFibre (centre X I) ⊥ k').left) :
    deformationSpecialFibrePowMap k' hm X I J (IdealSheafData.deformationSpacePowMap m hJ)
      (affineLinePowMap k m) (deformationSpacePowMap_deformationSpaceToAffineLine hJ) hσ
        ((zeroSectionSpecialFibreMap X I k').left z) ∈
      Set.range (zeroSectionSpecialFibreMap X J k').left := by
  set ν₀ := IdealSheafData.deformationSpacePowMap m hJ
  set y := (zeroSectionSpecialFibreMap X I k').left z
  have e₁ : (zeroSectionSpecialFibreMap X I k').left ≫ deformationSpecialToTotal X I k' ≫
      deformationTotalToSpace X I k' = deformationSpecialToTotal (centre X I) ⊥ k' ≫
        deformationTotalToSpace (centre X I) ⊥ k' ≫
          IdealSheafData.deformationSpaceMap I.subschemeι I ⊥
            I.siteIdeal_map_appLE_subschemeι_le_bot := by
    rw [zeroSectionSpecialFibreMap, deformationSpecialFibreMap_toTotal_assoc,
      deformationTotalMap_toSpace]
    rfl
  have e₂ : deformationSpecialFibrePowMap k' hm X I J ν₀ (affineLinePowMap k m)
      (deformationSpacePowMap_deformationSpaceToAffineLine hJ) hσ ≫
      deformationSpecialToTotal X J k' ≫ deformationTotalToSpace X J k' =
      deformationSpecialToTotal X I k' ≫ deformationTotalToSpace X I k' ≫ ν₀ := by
    rw [deformationSpecialFibrePowMap, ← Category.assoc]
    erw [pullback.lift_fst]
    rw [Category.assoc, deformationTotalPowMap_toSpace]
  have h₀ : deformationTotalToSpace X I k' (deformationSpecialToTotal X I k' y) ∈
      Set.range (IdealSheafData.deformationSpaceMap I.subschemeι I ⊥
        I.siteIdeal_map_appLE_subschemeι_le_bot) := by
    refine ⟨deformationTotalToSpace (centre X I) ⊥ k'
      (deformationSpecialToTotal (centre X I) ⊥ k' z), ?_⟩
    have := congr($(e₁).base z)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    exact this.symm
  obtain ⟨u, hu⟩ :=
    IdealSheafData.deformationSpacePowMap_mem_range_deformationSpaceMap_subschemeι hJ hm₀ h₀
  have h₂ := congr($(e₂).base y)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h₂
  obtain ⟨v, hv₁, hv₂⟩ := (isPullback_deformationTotalMap_toSpace (centreι X J)
    (siteIdeal_map_appLE_le_bot X J) k').exists_scheme_point _ u (h₂.trans hu.symm)
  obtain ⟨w, hw₁, hw₂⟩ := (isPullback_deformationSpecialFibreMap_toTotal (centreι X J)
    (siteIdeal_map_appLE_le_bot X J) k').exists_scheme_point _ v hv₁.symm
  exact ⟨w, hw₁⟩

end AlgebraicGeometry.ProEtale.CondensedRing
