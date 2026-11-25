/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.Functor.CurryComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm
public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedTensorSquare
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedCoherenceOfSquare
import WeilConjectures.Tactic.ExactModProofs

/-!
# The condensed realization is compatible with the pullback–tensor comparisons

For a morphism `g : Z ⟶ Y` of `k₀`-schemes, the derived condensed realization `N` carries the
native pullback–tensor comparison `g^*(A ⊗ B) ≅ g^*A ⊗ g^*B`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTensor`) to the comparison
`Lḡ^*(K ⊗ᴸ L) ⟶ Lḡ^*K ⊗ᴸ Lḡ^*L` of condensed `ℚ̲̄_ℓ`-modules on the geometric fibres
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`), up to the tensor
comparisons `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensor` and the pullback
comparison `AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso`:
this is `CategoryTheory.Adjunction.ComparisonCompatible`, the hypothesis of
`CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The native derived tensor product of pro-étale Weil complexes, curried. -/
noncomputable abbrev nativeCurriedTensor (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :=
  Functor.curry.obj (nativeDerivedTensor k₀ l X)

/-- The condensed realization commutes with the derived tensor products, in curried form. -/
noncomputable abbrev condensedRealizationCurriedTensor (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :=
  Functor.curryCompIsoOfIso' (condensedRealizationTensor k₀ l X)

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The native pullback–tensor comparison `g^*(A ⊗ B) ⟶ g^*A ⊗ g^*B`, in curried form. -/
noncomputable abbrev nativeCurriedPullTensor :=
  (Functor.curryCompIsoOfIso (nativePullTensor k₀ l g)).hom

/-- **Compatibility of the condensed realization with the pullback–tensor comparisons.** -/
theorem comparisonCompatible_derivedCondensedRealization :
    Adjunction.ComparisonCompatible (derivedCondensedRealizationUpperStarIso k₀ l g)
      (nativeCurriedPullTensor k₀ l g)
      (ProEtale.CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (condensedRealizationCurriedTensor k₀ l Z) (condensedRealizationCurriedTensor k₀ l Y) := by
  exact_mod_proofs projectionComparisonCompatible_of_square k₀ l g
    (condensedRealizationTensor_pull_square k₀ l g)

end AlgebraicGeometry.ProEtaleWeilSheaf
