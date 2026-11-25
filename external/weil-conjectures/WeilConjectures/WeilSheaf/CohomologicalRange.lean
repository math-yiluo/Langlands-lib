/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.CohomologicalRangeAffine

/-!
# The cohomological range of a curve

The compactly supported cohomology `H_c^r(X ⊗ k̄, G)` of a Weil sheaf `G` on a separated
`k₀`-scheme `X` of finite type and of dimension at most one is concentrated in degrees
`0, 1, 2`. In particular this holds on a smooth affine curve.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_krullDim_le_one`:
  the curve clause of the Euler-product form of the trace formula.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine`: the
  compactly supported cohomology of a smooth affine curve is concentrated in degrees `0, 1, 2`.

## Implementation notes

The blueprint proves the range of a smooth affine curve at the finite coefficient levels
`𝒪_E / ϖⁿ`, by the cohomological dimension of a proper curve and a Mittag-Leffler argument for
the passage to the limit. Weil sheaves in the repository have coefficients `ℚ̄_ℓ` directly and no
finite coefficient levels, so this argument cannot be run. Instead, the vanishing above degree two
is reduced, by Noetherian induction, Noether normalization and the lisse locus on the affine line,
to Poincaré duality for lisse sheaves on smooth curves
(`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`, blueprint
`corollary-degreewise-duality-over-fields--1`), see
`WeilConjectures.WeilSheaf.CohomologicalRangeAffine`. The statement is clause (3) of the
Euler-product form of the trace formula (blueprint `theorem-trace-formula-euler-product`), for a
sheaf placed in degree zero on a scheme of dimension at most one; it is stated here for Weil
sheaves, without the finite-level hypotheses (étale-origin witnesses and compactification
admissibility of the reductions of a lattice) of the blueprint, which have no counterpart for
`ℚ̄_ℓ`-Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `theorem-trace-formula-euler-product`, clause (3): if the separated `k₀`-scheme `X` of
finite type has dimension at most one and `G` is a Weil sheaf on `X`, placed in degree zero, then
`H_c^r(X ⊗ k̄, G) = 0` for `r ∉ {0, 1, 2}`, so that the Euler product of the trace formula only
involves `H_c^0`, `H_c^1` and `H_c^2`.

Negative degrees vanish for any `X`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_neg`). Degrees above
two vanish by Noetherian induction on the closed subsets of `X`: a nonempty closed subscheme `T`
of `X` contains a nonempty affine open `U`, of dimension at most one, on which the vanishing holds
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine_of_two_lt`);
by induction it holds on the reduced complement of `U`, and the open–closed exact sequence glues
the two. -/
theorem subsingleton_compactlySupportedCohomology_of_krullDim_le_one
    (hX : topologicalKrullDim X ≤ 1) (G : WeilSheaf k₀ l X) {r : ℤ} (hr : r < 0 ∨ 2 < r) :
    Subsingleton (G.compactlySupportedCohomology r).carrier := by
  rcases hr with hr | hr
  · exact subsingleton_compactlySupportedCohomology_of_neg G hr
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))
  -- Noetherian induction on the closed subsets of `X`.
  have key : ∀ (Z : Closeds X) (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))]
      (i : T ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))],
      Set.range i ⊆ Z → ∀ [IsSeparated (T ↘ Spec (CommRingCat.of k₀))]
        [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
        [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l T),
        Subsingleton (F.compactlySupportedCohomology r).carrier := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | ind Z ih =>
    intro T _ i _ _ hiZ _ _ _ F
    have := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))
    -- `T` has dimension at most one, and so do its affine opens.
    have hT : topologicalKrullDim T ≤ 1 :=
      i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hX
    have hdim (V : Scheme.{u}) [IsAffine V] (v : V ⟶ T) [IsOpenImmersion v] :
        ringKrullDim Γ(V, ⊤) ≤ 1 := by
      have e := IsHomeomorph.topologicalKrullDim_eq _ V.isoSpec.hom.homeomorph.isHomeomorph
      change topologicalKrullDim V = topologicalKrullDim (PrimeSpectrum Γ(V, ⊤)) at e
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← e]
      exact v.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hT
    cases isEmpty_or_nonempty T
    · exact subsingleton_compactlySupportedCohomology_of_isAffine_of_two_lt
        (hdim T (𝟙 T)) F hr
    -- a nonempty affine open `U` of `T`
    obtain ⟨t⟩ := ‹Nonempty T›
    obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset (x := t) (U := ⊤) trivial
    have : IsAffine U := hU
    have hc := comp_over U.ι (Spec (CommRingCat.of k₀))
    have : IsSeparated (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← hc]; infer_instance
    have : LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← hc]; infer_instance
    have : QuasiCompact (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← hc]; infer_instance
    have : NoetherianSpace U.toScheme := inferInstanceAs (NoetherianSpace (U : Set T))
    have : QuasiCompact U.ι := inferInstance
    -- the reduced closed complement `T'` of `U`
    let C : Closeds T := ⟨(U : Set T)ᶜ, U.isOpen.isClosed_compl⟩
    let i' := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
    let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over
        (Spec (CommRingCat.of k₀)) := ⟨i' ≫ T ↘ Spec (CommRingCat.of k₀)⟩
    have : i'.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have hrange : Set.range i' = C := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
    have : IsSeparated
        ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i']; infer_instance
    have : LocallyOfFiniteType
        ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i']; infer_instance
    have : QuasiCompact
        ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i']; infer_instance
    let Z' : Closeds X := ⟨i '' C, i.isClosedEmbedding.isClosedMap _ C.isClosed⟩
    have hZ' : Z' < Z := by
      refine lt_of_le_of_ne (fun y ⟨s, _, hs⟩ ↦ hiZ ⟨s, hs⟩) fun h ↦ ?_
      have : i t ∈ (Z' : Set X) := h ▸ hiZ ⟨t, rfl⟩
      obtain ⟨s, hs, hsi⟩ := this
      exact hs (i.isClosedEmbedding.injective hsi ▸ htU)
    have h₂ := ih Z' hZ' _ (i' ≫ i) (by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]; exact subset_rfl)
      ((upperStar i').obj F)
    exact subsingleton_compactlySupportedCohomology_of_openClosed U.ι i'
      (by rw [Scheme.Opens.range_ι, hrange]; exact isCompl_compl) F r
      (subsingleton_compactlySupportedCohomology_of_isAffine_of_two_lt (hdim U U.ι) _ hr) h₂
  exact key ⊤ X (𝟙 X) (Set.subset_univ _) G

/-- *Cohomological range of an affine curve.* If `X` is a smooth affine curve over `k₀` and `G`
is a constructible Weil sheaf on `X`, then `H_c^r(X ⊗ k̄, G) = 0` for `r ∉ {0, 1, 2}`: a smooth
curve has dimension at most one, and the compactly supported cohomology of a sheaf on a scheme of
dimension at most one is concentrated in degrees `0, 1, 2`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_krullDim_le_one`).
(blueprint: `lemma-cohomological-range-curve--1`) -/
theorem subsingleton_compactlySupportedCohomology_of_isAffine [IsAffine X]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {r : ℤ}
    (hr : r < 0 ∨ 2 < r) :
    Subsingleton (G.compactlySupportedCohomology r).carrier :=
  subsingleton_compactlySupportedCohomology_of_krullDim_le_one
    (by exact_mod_cast
      topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (CommRingCat.of k₀)) 1) G hr

end WeilSheaf

end AlgebraicGeometry
