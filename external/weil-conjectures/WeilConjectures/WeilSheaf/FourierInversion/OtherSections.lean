/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.AffineLineBundle
public import WeilConjectures.WeilSheaf.AffineLineSmoothAdjunction
import WeilConjectures.WeilSheaf.SmoothPurityThomFromTate
public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.LowerShriekOperations
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerShriek

/-!
# Fourier inversion: inputs from other sections

Statements of blueprint nodes of other sections (the projection formula, the open–closed
recollement and the Thom isomorphism for Weil complexes) used in the proof of Fourier inversion.
The projection formula is
`AlgebraicGeometry.WeilComplex.derivedLowerShriekCompTensorLisseIso`; the Thom isomorphism is
deduced from smooth purity via `WeilConjectures.WeilSheaf.AffineLineSmoothAdjunction`
and the homotopy invariance of `WeilConjectures.WeilSheaf.AffineLineBundle`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section OtherSections

/-- Blueprint `sec-Weil-complexes`: Six operations on Weil complexes (the projection
formula). For a separated quasi-compact morphism `f : X ⟶ Y` locally of finite type of
`k₀`-schemes of finite type and a lisse Weil sheaf `G` on `Y`, `Rf₀!(f^* G ⊗ K) ≅ G ⊗ Rf₀! K`
naturally in the Weil complex `K` (`G`, lisse, is in particular of finite Tor-amplitude). -/
theorem WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.tensorLisse G hG ≅
      WeilComplex.tensorLisse ((WeilSheaf.upperStar f).obj G)
          (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ⋙
        WeilComplex.derivedLowerShriek k₀ l f) :=
  ⟨WeilComplex.derivedLowerShriekCompTensorLisseIso f G hG⟩

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--8` and
`proposition-extension-zero-restriction-closed-subscheme` (open–closed recollement), for Weil
complexes. Let `i : Z ⟶ X` be a closed immersion of `k₀`-schemes of finite type and `j : U ⟶ X` the
complementary open immersion. There is a natural transformation `K ⟶ Ri_* i^* K` (the closed
unit) which is an isomorphism at every `K` with `j^* K = 0`: in the recollement triangle
`j_! j^* K ⟶ K ⟶ Ri_* i^* K ⟶`, the first term vanishes. -/
theorem WeilComplex.exists_isIso_app_of_isZero_upperStar {X Z U : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i]
    [IsOpenImmersion j] [i.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] (hij : Set.range j = (Set.range i)ᶜ)
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ η : 𝟭 (WeilComplex k₀ l X) ⟶
        WeilComplex.upperStar i ⋙ WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) i,
      ∀ K : WeilComplex k₀ l X, IsZero ((WeilComplex.upperStar j).obj K) → IsIso (η.app K) :=
  by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian X := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have hc : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [show Set.range j.base = (Set.range i.base)ᶜ from hij]
    exact isCompl_compl
  have hR := WeilComplex.fullyFaithfulDerivedLowerStar (k₀ := k₀) (l := l) i
  have := hR.full
  have := hR.faithful
  refine ⟨(WeilComplex.upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) i).unit,
    fun K hK ↦ ?_⟩
  obtain ⟨M, ⟨e⟩⟩ := WeilComplex.derivedLowerStar_essImage_of_isZero i j hc K hK
  exact (WeilComplex.upperStarDerivedLowerStarAdjunction i).isIso_unit_app_of_iso e.symm

/-- Blueprint `lemma-integral-linear-character--1` (and its vector-bundle form
`lemma-integral-linear-character--1`), combined with the projection formula of `sec-Weil-complexes`
for the constant sheaf: for the trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`,
`Rπ₀! π^* P ≅ P(-1)[-2]` naturally in the Weil complex `P` on `X`. The trivial line bundle is given
by a cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`. Only the existence of a natural isomorphism
is stated: the proof, by uniqueness of adjoints, does not produce the canonical map
`τ_E = Rπ_! thom(E)`. -/
theorem WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (s : Y ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.upperStar π ⋙ WeilComplex.derivedLowerShriek k₀ l π ≅
      WeilComplex.tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)) := by
  exact WeilComplex.purity_nonempty_trivialLineThom π s hπ

end OtherSections

end AlgebraicGeometry
