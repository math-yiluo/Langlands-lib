/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationAdjoint
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive

/-!

# The proper pushforward with `E`-coefficients is a left adjoint if it is so with `𝒪_E`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`g : Z ⟶ Y` a morphism of separated `k`-schemes of finite type, for a field `k` of
characteristic `p ≠ ℓ`. This file shows that if the derived pushforward
`Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` is a left adjoint, then so is
`Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧`
(`isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj_of_padicIntegersRingObj`).

Indeed `Dᵇc(-)⟦E̲⟧` is the rationalization (`ℓ` inverted) of `Dᵇc(-)⟦𝒪̲_E⟧`
(`ProEtale.isLocalization_boundedConstructibleExtendScalars`), the two pushforwards correspond
under it (the mate of the pullback comparison is an isomorphism), and an adjunction of
triangulated functors rationalizes to an adjunction
(`CategoryTheory.Rationalization.isLeftAdjoint_of_isLocalization`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (g : Z ⟶ Y)
  (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- If `Rg_*` on `Dᵇc(-)⟦𝒪̲_E⟧` is a left adjoint, so is `Rg_*` on `Dᵇc(-)⟦E̲⟧` (inverting ℓ). -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj_of_padicIntegersRingObj
    [(PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 g).IsLeftAdjoint] :
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).IsLeftAdjoint := by
  have hnoeth (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
      TopologicalSpace.NoetherianSpace X.left := by
    have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    have : IsNoetherian X.left := ⟨⟩
    infer_instance
  have := hnoeth Z
  have := hnoeth Y
  let : (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 g).CommShift ℤ := by
    delta PadicIntegersRingObj.boundedConstructibleLowerStar
    infer_instance
  have : (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 g).IsTriangulated := by
    delta PadicIntegersRingObj.boundedConstructibleLowerStar
    infer_instance
  have (X : Scheme.{u}) : (boundedConstructibleExtendScalars X ℓ E).Additive := by
    have := (Mod.derivedExtendMapDerivedCategoryAdjunction
      (padicIntegersToPadicSubfield X ℓ E)).left_adjoint_additive
    unfold boundedConstructibleExtendScalars
    infer_instance
  have := Rationalization.isIso_mateEquiv_of_isLocalization (M := Submonoid.powers (ℓ : ℤ))
    (boundedConstructibleExtendScalars Y.left ℓ E) (boundedConstructibleExtendScalars Z.left ℓ E)
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E.1 g)
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E g)
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E g)
  exact Rationalization.isLeftAdjoint_of_isLocalization (M := Submonoid.powers (ℓ : ℤ))
    (boundedConstructibleExtendScalars Z.left ℓ E) (boundedConstructibleExtendScalars Y.left ℓ E)
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 g) _
    (asIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E.1
      g) (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E g)
      (TwoSquare.mk _ _ _ _ (boundedConstructibleUpperStarExtendScalarsIso ℓ E g).inv)))

end AlgebraicGeometry.ProEtale.CondensedRing
