/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationOpenImmersion
public import WeilConjectures.TraceFormula.CurveLocal.ModelAxes
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroCoverConstruction

/-!

# The complement of the axes in `T'` lies over the punctured curves

For a cover datum, the points of `T' ∖ (D' ∪ H')` map, under both projections `T' ⟶ C`, into the
punctured neighbourhood `p⁻¹(W ∖ y)` of `c` over which the terms of the models are trivialized
(`CoverDatum.ψ₁`, `CoverDatum.ψ₂`; blueprint `lemma-tangent-cones-on-cover` (i): `N' ⊠ Q'` is
formed on the complement of the axes).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {M : CurveLocalModel k} {ℓ : ℕ}
  {Λ : Type (u + 1)} [CommRing Λ]
  {PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (D : M.CoverDatum ℓ PL PK)

/-- The punctured neighbourhood `p⁻¹(W ∖ y)` of `c` in `C`. -/
noncomputable abbrev Vc : D.C.Opens := D.p ⁻¹ᵁ puncturedOpens D.W _ M.isClosed_y

/-- The complement `T' ∖ (D' ∪ H')`. -/
noncomputable abbrev O' : D.T'.Opens := D.dD'.openComplement ⊓ D.dH'.openComplement



lemma subset_range_dD' : D.π.base ⁻¹' (Set.range M.a.base ∪ Set.range M.v.base) ⊆
    Set.range D.dD'.base := by
  rw [range_reducedClosedι]
  exact subset_closure

lemma subset_range_dH' : D.π.base ⁻¹' Set.range M.hH.base ⊆ Set.range D.dH'.base := by
  rw [range_reducedClosedι]
  exact subset_closure

/-- Points of `T'` map into `p⁻¹(W)` under both projections. -/
lemma mem_W_of_toBase (z : D.T') (i : D.S' ⟶ D.C) (hi : D.s' ≫ i = D.c) :
    D.p.base (i.base ((strictLocalizationToBase D.s').base z)) ∈ D.W := by
  have h := range_strictLocalizationToBase_subset D.s' ((i ≫ D.p).base ⁻¹' (D.W : Set M.X))
    (D.W.isOpen.preimage (i ≫ D.p).base.hom.continuous) default (by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Category.assoc, hi, D.c_comp]
      exact D.mem_W) ⟨z, rfl⟩
  simpa using h

/-- The points of `T' ∖ (D' ∪ H')` lie, under the first projection, over `p⁻¹(W ∖ y)`. -/
lemma fst_mem_Vc (z : D.T') (hz : z ∈ D.O') :
    (pullback.fst D.fC D.fC).base ((strictLocalizationToBase D.s').base z) ∈ D.Vc := by
  refine ⟨D.mem_W_of_toBase z _ (by rw [s', pullback.lift_fst]), fun hy ↦
    hz.1 (D.subset_range_dD' (Or.inr ?_))⟩
  rw [mem_range_v_iff]
  change (D.π ≫ M.τ ≫ pullback.fst M.f M.f).base z = _
  rw [← Category.assoc, D.π_comp_τ, Category.assoc, D.g_fst, ← Category.assoc]
  exact Set.mem_singleton_iff.1 hy

/-- The points of `T' ∖ (D' ∪ H')` lie, under the second projection, over `p⁻¹(W ∖ y)`. -/
lemma snd_mem_Vc (z : D.T') (hz : z ∈ D.O') :
    (pullback.snd D.fC D.fC).base ((strictLocalizationToBase D.s').base z) ∈ D.Vc := by
  refine ⟨D.mem_W_of_toBase z _ (by rw [s', pullback.lift_snd]), fun hy ↦ hz.2
    (D.subset_range_dH' (show D.π.base z ∈ Set.range M.hH.base from ?_))⟩
  rw [mem_range_hH_iff]
  change (D.π ≫ M.τ ≫ pullback.snd M.f M.f).base z = _
  rw [← Category.assoc, D.π_comp_τ, Category.assoc, D.g_snd, ← Category.assoc]
  exact Set.mem_singleton_iff.1 hy

end AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum
