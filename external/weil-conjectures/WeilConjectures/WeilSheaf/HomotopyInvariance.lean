/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.HomotopyInvariance.Lisse
public import WeilConjectures.WeilSheaf.HomotopyInvariance.Restriction

/-!
# Homotopy invariance for Weil complexes along trivial line bundles

Let `π : Y ≅ Z ×_{k₀} 𝔸¹ ⟶ Z` be the trivial line bundle over a `k₀`-scheme `Z` of finite type.
The unit `K ⟶ Rπ_* π^* K` of `π^* ⊣ Rπ_*` is an isomorphism for every Weil complex `K` on `Z`
(blueprint `lem-pur-a1-direct-image`, extended to all Weil complexes). This file proves it for
reduced `Z` by Noetherian induction on the closed subsets of an ambient scheme `X` containing
`Z` as a closed subscheme
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isClosedImmersion_of_isReduced`); the general
case,
`AlgebraicGeometry.WeilComplex.isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback`
in `WeilConjectures.WeilSheaf.AffineLineBundle`, follows by passing to the reduced subscheme.

For the induction step, `K` has lisse cohomology sheaves on a dense open subscheme `j : U ⟶ Z`
(`AlgebraicGeometry.WeilComplex.exists_dense_isLisse_homologySheaf_upperStar`); let
`i : T ⟶ Z` be the reduced closed complement. In the closed-support triangle
`i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶`, the unit is invertible at `Rj_* j^* K` by smooth base change
and homotopy invariance for complexes with lisse cohomology
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isLisse_homologySheaf`), and at
`i_* Ri^! K` by smooth base change and the induction hypothesis for `T`, whose image in `X` is a
strictly smaller closed subset
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj`).
The objects at which the unit is invertible form a triangulated subcategory
(`CategoryTheory.Adjunction.isTriangulated_isoLocus_unit`), so it is invertible at `K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Homotopy invariance on reduced closed subschemes.** Let `X` be a scheme and `C` a closed
subset of `X`. For every reduced `k₀`-scheme `Z` of finite type with a closed immersion
`i : Z ⟶ X` whose image lies in `C`, every trivial line bundle `π : Y ≅ Z ×_{k₀} 𝔸¹ ⟶ Z` and every
Weil complex `K` on `Z`, the unit `K ⟶ Rπ_* π^* K` is an isomorphism. The proof is a Noetherian
induction on `C`. -/
theorem isIso_unit_app_of_isClosedImmersion_of_isReduced {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (C : TopologicalSpace.Closeds X) (Z : Scheme.{u})
    [Z.Over (Spec (CommRingCat.of k₀))] [IsReduced Z]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))] (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : Set.range i ⊆ C) (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ Z)
    (s : Y ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (Z ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (K : WeilComplex k₀ l Z) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app K) := by
  induction C using WellFoundedLT.induction generalizing Z Y with
  | _ C ih => ?_
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact isIso_unit_app_of_isEmpty π K
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace Z :=
    QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian Z := ⟨⟩
  have := locallyOfFiniteType_over_of_isOver π (S := Spec (CommRingCat.of k₀))
  -- a dense open `j : U ⟶ Z` on which `K` has lisse cohomology sheaves
  obtain ⟨U, hU, hUl⟩ := exists_dense_isLisse_homologySheaf_upperStar K
  let j := U.ι
  let : U.toScheme.Over (Spec (CommRingCat.of k₀)) := ⟨j ≫ Z ↘ Spec (CommRingCat.of k₀)⟩
  have : j.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have := locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  have : QuasiCompact (U.toScheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (j ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have : QuasiSeparated (U.toScheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (j ≫ Z ↘ Spec (CommRingCat.of k₀)))
  -- its reduced closed complement `r : T ⟶ Z`
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds Z)
  let r := I.subschemeι
  let : I.subscheme.Over (Spec (CommRingCat.of k₀)) := ⟨r ≫ Z ↘ Spec (CommRingCat.of k₀)⟩
  have : r.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (r ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (r ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have : QuasiSeparated (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (r ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have hr : Set.range r = (U : Set Z)ᶜ := by simp [r, I]
  have hc : IsCompl (Set.range r.base) (Set.range j.base) := by
    have hr' : Set.range r.base = (U : Set Z)ᶜ := hr
    rw [hr', Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  -- the image of `T` in `X` is a strictly smaller closed subset
  let C' : TopologicalSpace.Closeds X :=
    ⟨i '' (U : Set Z)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
  have hC' : C' < C := by
    obtain ⟨x, hx⟩ := hU.nonempty
    refine lt_of_le_of_ne ?_ fun h ↦ ?_
    · rintro _ ⟨z, -, rfl⟩
      exact hi ⟨z, rfl⟩
    · obtain ⟨z, hz, hzx⟩ : i x ∈ C' := h ▸ hi ⟨x, rfl⟩
      exact hz (i.isClosedEmbedding.injective hzx ▸ hx)
  have hrC' : Set.range (r ≫ i) ⊆ C' := by
    rintro _ ⟨z, rfl⟩
    refine ⟨r z, ?_, by simp⟩
    rw [← hr]
    exact ⟨z, rfl⟩
  obtain ⟨w, hw, -⟩ := existsUnique_distTriang_closedSupportTriangle r j hc K
  -- the unit is invertible at the two outer terms of the closed-support triangle
  have hP := (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.isoLocus
    |>.ext_of_isTriangulatedClosed₂ _ hw
  refine hP ?_ ?_
  · exact isIso_unit_app_derivedLowerStar_obj π s hπ r _
      fun Y' _ π' s' _ hπ' _ _ _ ↦ ih C' hC' I.subscheme (r ≫ i) hrC' Y' π' s' hπ' _
  · exact isIso_unit_app_derivedLowerStar_obj π s hπ j _
      fun Y' _ π' s' _ hπ' _ _ _ ↦ isIso_unit_app_of_isLisse_homologySheaf π' s' hπ' _ hUl

end AlgebraicGeometry.WeilComplex
