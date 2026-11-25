/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjection

/-!
# The sheaf `S_X` is of étale origin

The sheaf `S_X` of `R`-modules underlying the unit sheaf of `S`-modules on `X_proét`
(`AlgebraicGeometry.ProEtale.sheafRestrictScalarsUnit`) is the constant sheaf with value `S`,
hence the pro-étale realization `ν^*` of an étale sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance] Sheaf.monoidalCategory

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

/-- The sheaf `S_X` of `R`-modules underlying the unit sheaf of `S`-modules on `X_proét` is of
étale origin: it is the constant sheaf with value `S`, which is `ν^*` of the constant étale sheaf
with value `S`. Indeed the unit sheaf is the sheafification of the constant presheaf with value
`S`, and restriction of scalars commutes with sheafification. -/
theorem exists_comparisonUpperStar_obj_iso_sheafRestrictScalarsUnit (X : Scheme.{u}) :
    ∃ c₀ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R),
      Nonempty ((ν^*(X)[ModuleCat.{u + 1} R]).obj c₀ ≅ sheafRestrictScalarsUnit R S X) := by
  have : (ProEt.topology X).PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap R S))
  exact ⟨(constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj (𝟙_ (ModuleCat.{u + 1} S))),
    ⟨(comparisonUpperStarConstantSheafIso R X).app _ ≪≫
      ((constantCommuteCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).app _).symm ≪≫
      (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapIso
        (Functor.Monoidal.εIso (presheafToSheaf (ProEt.topology X) (ModuleCat.{u + 1} S))).symm⟩⟩

end AlgebraicGeometry.ProEtale
