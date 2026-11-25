/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.ProperLowerStarAdjoint

/-! # The compact-support adjunction over a separated base -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- Compactification and the proved proper adjunction give a right adjoint to
compact pushforward over a separated finite-type base. -/
theorem isLeftAdjoint_derivedLowerShriek_of_separated_base : HasUpperShriek k₀ l f := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  let := Compactification.over (k₀ := k₀) c
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := inferInstance
  have e : derivedLowerShriek k₀ l f ≅ extensionByZero c.i ⋙ derivedLowerStar c.g :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ ((derivedLowerShriekCompιIso k₀ l c).app K))
      (fun φ ↦ by
        apply (WeilComplex.objectProperty k₀ l Y).ι.map_injective
        exact (derivedLowerShriekCompιIso k₀ l c).hom.naturality φ)
  have := isLeftAdjoint_derivedLowerStar_of_isProper (k₀ := k₀) (l := l) c.g
  have : (extensionByZero (k₀ := k₀) (l := l) c.i).IsLeftAdjoint :=
    (extensionByZeroUpperStarAdjunction c.i).isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso e.symm

end AlgebraicGeometry.WeilComplex
