/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.Fiber
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
public import WeilConjectures.DeligneLaumon.Reduction.CompactSupport
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.PoincareDualityLisse

/-!
# Vanishing of compactly supported cohomology of affine curves above degree two

Let `G` be a Weil sheaf on a separated `k₀`-scheme `X` of finite type. This file proves the
ingredients of the cohomological range `H_c^r(X ⊗ k̄, G) = 0` for `r ∉ {0, 1, 2}` on schemes of
dimension at most one
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_krullDim_le_one`):

- `H_c^r` vanishes for `r < 0`, the direct image with compact support of a sheaf being
  concentrated in nonnegative degrees;
- the open–closed exact sequence `H_c^r(U, G|_U) ⟶ H_c^r(X, G) ⟶ H_c^r(Z, G|_Z)` for an open `U`
  with closed complement `Z`;
- for `X` smooth of relative dimension one and `G` lisse, `H_c^r(X, G)` vanishes for `r > 2`: it is
  Poincaré dual to `H^{2 - r}(X, G^∨(1))`, which vanishes in negative degrees
  (blueprint `corollary-degreewise-duality-over-fields--1`);
- on the affine line, `G` is lisse on a dense open with finite complement, so `H_c^r` vanishes for
  `r > 2`;
- on an affine scheme of dimension at most one, a finite morphism to the affine line (Noether
  normalization) reduces the vanishing for `r > 2` to the affine line.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_neg`
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_openClosed`
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isLisse`
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_affineLine`
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine_of_two_lt`
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section General

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The open–closed exact sequence.** Let `j : U ⟶ X` be a quasi-compact open immersion with
closed complement `i : Z ⟶ X`. If `H_c^r(U ⊗ k̄, G|_U)` and `H_c^r(Z ⊗ k̄, G|_Z)` vanish, so does
`H_c^r(X ⊗ k̄, G)`, by the exact sequence `H_c^r(U, G|_U) ⟶ H_c^r(X, G) ⟶ H_c^r(Z, G|_Z)`. -/
theorem subsingleton_compactlySupportedCohomology_of_openClosed {U Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (G : WeilSheaf k₀ l X) (r : ℤ)
    (hU : Subsingleton (((upperStar j).obj G).compactlySupportedCohomology r).carrier)
    (hZ : Subsingleton (((upperStar i).obj G).compactlySupportedCohomology r).carrier) :
    Subsingleton (G.compactlySupportedCohomology r).carrier := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := WeilComplex.exists_distTriang_derivedLowerShriek_openClosed
    j i hij (X ↘ Spec (CommRingCat.of k₀)) (toComplex.obj G)
  let E₁ := WeilComplex.cohomologyEquivOfIso (e₁ ≪≫
    (WeilComplex.derivedLowerShriekCongr (comp_over j _)).app _ ≪≫
    (WeilComplex.derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).mapIso
      (WeilComplex.upperStarToComplexIso j G)) r
  let E₃ := WeilComplex.cohomologyEquivOfIso (e₃ ≪≫
    (WeilComplex.derivedLowerShriekCongr (comp_over i _)).app _ ≪≫
    (WeilComplex.derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).mapIso
      (WeilComplex.upperStarToComplexIso i G)) r
  let E₂ := WeilComplex.cohomologyEquivOfIso e₂ r
  have h₁ : Subsingleton (T.obj₁.cohomologyFrobeniusModule r).carrier :=
    @Equiv.subsingleton _ _ E₁.toLinearEquiv.toEquiv hU
  have h₃ : Subsingleton (T.obj₃.cohomologyFrobeniusModule r).carrier :=
    @Equiv.subsingleton _ _ E₃.toLinearEquiv.toEquiv hZ
  have h₂ : Subsingleton (T.obj₂.cohomologyFrobeniusModule r).carrier := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := (WeilComplex.exact_cohomologyMap T r hT x).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero]
  exact E₂.symm.toLinearEquiv.toEquiv.subsingleton

/-- **Vanishing above degree two for a lisse sheaf on a smooth curve.** If `X` is smooth of
relative dimension one over `k₀` and `F` is a lisse Weil sheaf on `X`, then `H_c^r(X ⊗ k̄, F) = 0`
for `r > 2`: by Poincaré duality it is dual to `H^{2 - r}(X ⊗ k̄, F^∨(1))`, which vanishes since
`2 - r < 0` (blueprint: `corollary-degreewise-duality-over-fields--1`). -/
theorem subsingleton_compactlySupportedCohomology_of_isLisse
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {r : ℤ} (hr : 2 < r) :
    Subsingleton (F.compactlySupportedCohomology r).carrier := by
  obtain ⟨P, hP, -⟩ := exists_isPerfPair_compactlySupportedCohomology_dual 1 hF r (2 - r)
    (by push_cast; ring)
  have : Subsingleton
      ((((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ 1)).cohomology (2 - r)).carrier) :=
    subsingleton_globalSections_of_isZero
      (isZero_homologySheaf_derivedLowerStar_of_neg (X ↘ Spec (CommRingCat.of k₀)) _
        (by omega))
  refine ⟨fun x y ↦ hP.bijective_left.injective ?_⟩
  ext z
  rw [Subsingleton.elim z 0, map_zero, map_zero]

end General

section AffineLine

/-- **Vanishing above degree two on the affine line.** For a Weil sheaf `G` on `𝔸¹_{k₀}`,
`H_c^r(𝔸¹ ⊗ k̄, G) = 0` for `r > 2`: `G` is lisse on a dense open `U` with finite complement `Z`;
`H_c^r(U, G|_U)` vanishes by Poincaré duality on the smooth curve `U`, `H_c^r(Z, G|_Z)` because
`Z` is finite, and the open–closed exact sequence glues the two. -/
theorem subsingleton_compactlySupportedCohomology_affineLine
    (G : WeilSheaf k₀ l 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))) {r : ℤ} (hr : 2 < r) :
    Subsingleton (G.compactlySupportedCohomology r).carrier := by
  -- the lisse locus `U` of `G`, a dense open with finite complement
  obtain ⟨U, hUd, hUl⟩ := WeilSheaf.exists_dense_isLisse_upperStar G
  obtain ⟨b, ⟨s, hs⟩, hb⟩ :=
    AffineSpace.exists_basicOpen_forall_exists_mem_and_finite U hUd.nonempty
  have hfin : ((U : Set 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))ᶜ).Finite :=
    (hb s hs).2.subset fun x hx ↦ ⟨hx, Subsingleton.elim _ _⟩
  -- the reduced closed complement `Z` of `U`, quasi-finite over `k₀`
  let C : TopologicalSpace.Closeds 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) :=
    ⟨(U : Set 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))ᶜ, U.isOpen.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over (Spec (CommRingCat.of k₀)) :=
    ⟨i ≫ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hrange : Set.range i = C := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have : LocallyOfFiniteType
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i]
    infer_instance
  have : IsSeparated
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i]
    infer_instance
  have : QuasiCompact
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i]
    infer_instance
  have : LocallyQuasiFinite
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
    refine .of_finite_preimage_singleton _ fun _ ↦
      (hfin.preimage i.isClosedEmbedding.injective.injOn).subset fun z _ ↦ ?_
    exact (hrange ▸ ⟨z, rfl⟩ : i z ∈ (C : Set _))
  have := isNoetherian_of_locallyOfFiniteType
    (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
  -- the open part: `U` is a smooth curve on which `G` is lisse
  have hc := comp_over U.ι (Spec (CommRingCat.of k₀))
  have : SmoothOfRelativeDimension 1 (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← hc]
    exact AffineSpace.smoothOfRelativeDimension_one_of_isOpenImmersion U.ι
  have : IsSeparated (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← hc]
    infer_instance
  have : QuasiCompact (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← hc]
    infer_instance
  have : LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← hc]
    infer_instance
  have : QuasiCompact U.ι := inferInstance
  exact subsingleton_compactlySupportedCohomology_of_openClosed U.ι i
    (by rw [Scheme.Opens.range_ι, hrange]; exact isCompl_compl) G r
    (subsingleton_compactlySupportedCohomology_of_isLisse hUl hr)
    (subsingleton_compactlySupportedCohomology_of_locallyQuasiFinite _ (by omega))

end AffineLine

/-- **Vanishing above degree two on an affine curve.** For an affine `k₀`-scheme `C` of finite
type of dimension at most one and a Weil sheaf `F` on `C`, `H_c^r(C ⊗ k̄, F) = 0` for `r > 2`: a
finite morphism `f : C ⟶ 𝔸¹_{k₀}` (Noether normalization) identifies `H_c^r(C, F)` with
`H_c^r(𝔸¹, f₀*F)`, which vanishes for `r > 2`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_affineLine`). -/
theorem subsingleton_compactlySupportedCohomology_of_isAffine_of_two_lt {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))] (hC : ringKrullDim Γ(C, ⊤) ≤ 1)
    (F : WeilSheaf k₀ l C) {r : ℤ} (hr : 2 < r) :
    Subsingleton (F.compactlySupportedCohomology r).carrier := by
  obtain ⟨f, hf, hfo⟩ := AffineSpace.exists_isFinite_of_ringKrullDim_le_one (k := k₀) C hC
  have : f.IsOver (Spec (CommRingCat.of k₀)) := ⟨hfo⟩
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_higherLowerShriek_zero f F r
  have := subsingleton_compactlySupportedCohomology_affineLine
    ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F) hr
  exact E.toLinearEquiv.toEquiv.subsingleton

end AlgebraicGeometry.WeilSheaf
