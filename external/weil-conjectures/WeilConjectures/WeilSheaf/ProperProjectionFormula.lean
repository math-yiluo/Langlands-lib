/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationCoherence
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationProjection
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapReflect
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIsomorphisms
public import WeilConjectures.WeilSheaf.Native.Projection.ProperProjectionIso

/-!
# The proper projection formula for native Weil complexes

For a proper morphism `g : Z ⟶ Y` of separated `k₀`-schemes of finite type,
`Rg_* A ⊗ T ≅ Rg_*(A ⊗ g^* T)`, naturally in the Weil complexes `A` on `Z` and `T` on `Y`, the
tensor product being the native derived tensor product of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor`). This is the proper case of
`fix-prop-projection-formula` ("a projection formula for the derived direct image is asserted
only in the proper case").
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]

/-- **The proper projection formula for Weil complexes** (blueprint:
`fix-prop-projection-formula`, the proper case, for `Λ = ℚ̄_ℓ` with Weil structures): for a
proper morphism `g : Z ⟶ Y` of separated `k₀`-schemes of finite type,
`Rg_* A ⊗ T ≅ Rg_*(A ⊗ g^* T)`, naturally in the Weil complexes `A` on `Z` and `T` on `Y`.

The isomorphism is the projection map of `g^* ⊣ Rg_*` built from the native pullback–tensor
comparison (`AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTensor`). The derived condensed
realization reflects isomorphisms and carries this projection map to the projection map of the
geometric fibres of condensed `ℚ̲̄_ℓ`-modules
(`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv_of_reflects`, with the
coherence `AlgebraicGeometry.ProEtaleWeilSheaf.comparisonCompatible_derivedCondensedRealization`
and the invertible base change map
`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_mateEquiv_derivedCondensedRealizationUpperStarIso`),
which is invertible on bounded constructible complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_projectionMap_derivedCondensedRealization`). -/
theorem nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso :
    Nonempty (((objectProperty k₀ l Z).ι ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor).prod
          (objectProperty k₀ l Y).ι ⋙ ProEtaleWeilSheaf.nativeDerivedTensor k₀ l Y ≅
      (objectProperty k₀ l Z).ι.prod
          ((objectProperty k₀ l Y).ι ⋙ ProEtaleWeilSheaf.nativeOpenPull k₀ l g) ⋙
        ProEtaleWeilSheaf.nativeDerivedTensor k₀ l Z ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor) := by
  exact ⟨rightDerivedLowerStarNativeDerivedTensorIso g⟩

end WeilComplex

end AlgebraicGeometry
