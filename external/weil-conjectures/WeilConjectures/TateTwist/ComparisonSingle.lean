/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# `Rν_* ν^*` on a sheaf placed in degree zero

Let `ν : X_proét ⥤ X_ét` be the comparison morphism of sites. For an étale sheaf of
`Λ`-modules `S`, the derived pushforward `Rν_*` sends the pro-étale sheaf `ν^* S` placed in
degree zero back to `S` placed in degree zero
(`AlgebraicGeometry.ProEtale.rightDerivedComparisonLowerStarSingleFunctorIso`): the derived
`ν^*` of the exact functor `ν^*` commutes with `singleFunctor`, and the unit `M ⟶ Rν_* ν^* M` of
the derived comparison adjunction is invertible on bounded below complexes
(`AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- `Rν_* ν^* S ≅ S` for an étale sheaf `S` placed in degree zero: `ν^*` of `S` placed in degree
zero is `ν^* S` placed in degree zero (`Functor.mapDerivedCategorySingleFunctor`), and the unit
`M ⟶ Rν_* ν^* M` of the comparison adjunction is invertible on the bounded below `M = S[0]`
(`isIso_derivedComparisonAdjunction_unit_app`). -/
noncomputable def rightDerivedComparisonLowerStarSingleFunctorIso (Λ : Type (u + 1))
    [CommRing Λ] (X : Scheme.{u}) (S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.singleFunctor _ 0).obj (ν^*(X)[ModuleCat.{u + 1} Λ].obj S)) ≅
      (DerivedCategory.singleFunctor _ 0).obj S :=
  haveI := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X
    ((DerivedCategory.singleFunctor _ 0).obj S) ⟨0, inferInstance⟩
  (R(ν_*(X)[ModuleCat.{u + 1} Λ])).mapIso
      (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app S).symm ≪≫
    (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app _)).symm

end AlgebraicGeometry.ProEtale
