/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology

/-!
# `Rν_*` commutes with `⊗ᴸ` on bounded below complexes of étale origin

Let `Λ` be a noetherian commutative ring and `X` a scheme. The comparison `Rν_* : D(X_proét) ⥤
D(X_ét)` is not monoidal in general, but it is on the pro-étale complexes of étale origin: if
`P ≅ ν^* Q` and `P' ≅ ν^* Q'` with `Q`, `Q'` bounded below, and `P ⊗ᴸ P'` is bounded below, then
`Rν_* (P ⊗ᴸ P') ≅ Rν_* P ⊗ᴸ Rν_* P'`
(`AlgebraicGeometry.ProEtale.nonempty_rightDerivedComparisonLowerStarTensorIso`). Indeed
`ν^*(Q ⊗ᴸ Q') ≅ P ⊗ᴸ P'` (`ν^*` is strong monoidal), so `Q ⊗ᴸ Q'` is bounded below (`ν^*` is
exact and faithful), and the unit `𝟭 ⟶ Rν_* ν^*` is invertible on bounded below complexes
(`AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ] {X : Scheme.{u}}

/-- For `P ≅ ν^* Q` and `P' ≅ ν^* Q'` bounded below of étale origin, with `P ⊗ᴸ P'` bounded
below, `Rν_* (P ⊗ᴸ P') ≅ Rν_* P ⊗ᴸ Rν_* P'`: both sides are `Q ⊗ᴸ Q'`, using
`ν^*(Q ⊗ᴸ Q') ≅ P ⊗ᴸ P'`, the boundedness of `Q ⊗ᴸ Q'` (as `ν^*` is exact and faithful) and
`Rν_* ν^* ≅ 𝟭` on `D⁺(X_ét)`. -/
theorem nonempty_rightDerivedComparisonLowerStarTensorIso
    {P P' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hP : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X P)
    (hP' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X P')
    (h : DerivedCategory.TStructure.t.plus
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj P).obj P')) :
    Nonempty ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj
        (((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj P).obj P') ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj P)).obj
        ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj P')) := by
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hP
  obtain ⟨Q', hQ', ⟨eQ'⟩⟩ := hP'
  let e : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
      (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj Q).obj Q') ≅
        ((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj P).obj P' :=
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso _ Q).app Q' ≪≫
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso eQ).app _ ≪≫
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj P).mapIso eQ'
  obtain ⟨n, hn⟩ := DerivedCategory.TStructure.t.plus.prop_of_iso e.symm h
  have hQQ' : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj Q).obj Q') :=
    ⟨n, isGE_of_isGE_mapDerivedCategory_comparisonUpperStar hn⟩
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X _ hQQ'
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X _ hQ
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X _ hQ'
  exact ⟨(R(ν_*(X)[ModuleCat.{u + 1} Λ])).mapIso e.symm ≪≫
    (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app _)).symm ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso
        (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app Q) ≪≫
          (R(ν_*(X)[ModuleCat.{u + 1} Λ])).mapIso eQ)).app _ ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).mapIso
      (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app Q') ≪≫
        (R(ν_*(X)[ModuleCat.{u + 1} Λ])).mapIso eQ')⟩

end AlgebraicGeometry.ProEtale
