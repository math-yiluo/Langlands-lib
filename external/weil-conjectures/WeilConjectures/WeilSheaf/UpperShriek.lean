/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import WeilConjectures.WeilSheaf.ProperLowerStarAdjoint

/-!
# The exceptional inverse image of Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of `k₀`-schemes of finite type, `Y`
separated over `k₀`, the direct image with compact support `Rf₀!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`) has a right adjoint `Rf^!`; this is the
constructible adjunction `Rf_! ⊣ Rf^!` of the six-functor chapter
(`theorem-verdier-biduality`), `AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`.
It is deduced through a compactification from the proper case
`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerStar_of_isProper`. The exceptional
inverse image `AlgebraicGeometry.WeilComplex.upperShriek f` is *defined* as that right adjoint,
which is how the blueprint characterizes it (`theorem-f-shriek-finite-coefficients`); so that no
data is chosen from the existence statement, it takes the existence of the right adjoint
(`AlgebraicGeometry.WeilComplex.HasUpperShriek f`) as a hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

section UpperShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The direct image with compact support `Rf₀!` of Weil complexes along `f` has a right adjoint,
the exceptional inverse image `Rf^!` (`AlgebraicGeometry.WeilComplex.upperShriek`). That it
has one when `Y` is separated over `k₀` is
`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`. -/
abbrev HasUpperShriek : Prop :=
  (derivedLowerShriek k₀ l f).IsLeftAdjoint

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- **The constructible exceptional adjunction** (blueprint: `theorem-verdier-biduality`, "the
constructible adjunction `Rf_! ⊣ Rf^!`"; the exceptional inverse image itself is defined at the
finite stage as `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`): for a
separated morphism of finite type `f : X ⟶ Y` of `k₀`-schemes of finite type, `Y` separated over
`k₀`, the direct image with compact support `Rf₀!` of Weil complexes has a right adjoint. -/
theorem isLeftAdjoint_derivedLowerShriek
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))] : HasUpperShriek k₀ l f := by
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

variable [HasUpperShriek k₀ l f]

/-- The exceptional inverse image `Rf^!` of Weil complexes along a separated morphism of finite
type `f : X ⟶ Y` of `k₀`-schemes of finite type: the right adjoint of the direct image with
compact support `Rf₀!` (blueprint: `theorem-f-shriek-finite-coefficients`, which characterizes
`Rf^!` by the adjunction `Hom(Rf_! K, L) ≅ Hom(K, Rf^! L)` on constructible complexes). -/
noncomputable def upperShriek : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
  (derivedLowerShriek k₀ l f).rightAdjoint

/-- The adjunction `Rf₀! ⊣ Rf^!`. -/
noncomputable def derivedLowerShriekUpperShriekAdjunction :
    derivedLowerShriek k₀ l f ⊣ upperShriek (k₀ := k₀) (l := l) f :=
  Adjunction.ofIsLeftAdjoint _

end UpperShriek

end WeilComplex

end AlgebraicGeometry
