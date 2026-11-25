/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatFiniteResolution
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary

/-!
# The projection formula with a finite constant coefficient

Let `Λ` be a noetherian ring and `j : U ⟶ T` a morphism of schemes such that the derived direct
image `Rj_*` preserves countable coproducts. Then for every `K ∈ D(U_ét, Λ)`, bounded or not, and
every finitely generated `Λ`-module `N`, the projection map

`Rj_* K ⊗ᴸ N_T ⟶ Rj_*(K ⊗ᴸ Lj^* N_T) ≅ Rj_*(K ⊗ᴸ N_U)`

is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nat`,
blueprint `proposition-open-direct-image-preserves-finite`).

As a functor of `N ∈ D(Λ)`, through the constant complex functor `D(Λ) ⥤ D(T_ét, Λ)`
(`AlgebraicGeometry.Etale.constantFunctor`), the projection map is a natural transformation
between triangulated functors which preserve countable coproducts: the constant complex functor
is left adjoint to derived global sections, the derived tensor product and `Lj^*` are left
adjoints, and `Rj_*` preserves them by hypothesis. It is an isomorphism at the free modules of
finite rank, so at every finitely generated module
(`DerivedCategory.isIso_app_singleFunctor_obj_of_finite`), along the telescope of the stupid
truncations of a finite free resolution.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The constant complex functor `D(Λ) ⥤ D(X_ét, Λ)` preserves coproducts: it is left adjoint to
the derived global sections, the constant sheaf functor being an exact left adjoint of the global
sections functor. -/
instance preservesColimitsOfShape_constantFunctor (X : Scheme.{u}) (J : Type*) :
    PreservesColimitsOfShape (Discrete J) (constantFunctor Λ X) :=
  haveI : PreservesFiniteColimits (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteColimits (Functor.const _) (presheafToSheaf _ _)
  haveI : PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteLimits (Functor.const _) (presheafToSheaf _ _)
  haveI : ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (Opposite.op (etaleTerminal X))).Additive := { map_add := rfl }
  ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalEtaleTerminal X)).mapDerivedCategoryRightDerivedAdjunction
      ).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-- Blueprint `proposition-open-direct-image-preserves-finite`: Constant coefficient tensor
comparison.

Let `Λ` be a noetherian ring (in the blueprint: a finite ring) and `j : U ⟶ T` a morphism of
schemes (in the blueprint: an open immersion) such that `Rj_*` on the unbounded derived categories
of étale sheaves of `Λ`-modules preserves countable coproducts. For every `K ∈ D(U_ét, Λ)` and
every finitely generated `Λ`-module `N`, the projection map
`Rj_* K ⊗ᴸ N_T ⟶ Rj_*(K ⊗ᴸ Lj^* N_T)` is an isomorphism; its target is `Rj_*(K ⊗ᴸ N_U)`, as
`Lj^* N_T ≅ N_U` (`AlgebraicGeometry.Etale.leftDerivedUpperStarSingleConstantSheafIso`).

The projection map, composed with the constant complex functor, is a natural transformation of
coproduct-preserving triangulated functors out of `D(Λ)` which is an isomorphism at the free
modules of finite rank
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_pi`);
`DerivedCategory.isIso_app_singleFunctor_obj_of_finite` concludes, along a finite free resolution
of `N` and the telescope of its stupid truncations. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nat
    [IsNoetherianRing Λ] {U T : Scheme.{u}} (j : U ⟶ T)
    [PreservesColimitsOfShape (Discrete ℕ) (R((j)_*[ModuleCat.{u + 1} Λ]))]
    (K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : ModuleCat.{u + 1} Λ) [Module.Finite Λ N] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) j).app K).app
      (constantSingle (ModuleCat.{u + 1} Λ) T N)) := by
  let A := ModuleCat.{u + 1} Λ
  let τ := Functor.whiskerLeft (constantFunctor Λ T) (rightDerivedLowerStarProjectionMapApp Λ j K)
  have : PreservesColimitsOfShape (Discrete ℕ) (L((j)^*[A])) :=
    (derivedUpperStarLowerStarAdjunction _ j).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  -- the constant complex on a module placed in degree `0` is the constant sheaf placed there
  have e (M : A) : (constantFunctor Λ T).obj ((_root_.DerivedCategory.singleFunctor A 0).obj M) ≅
      constantSingle A T M :=
    (Functor.mapDerivedCategorySingleFunctor _ 0).app M
  have key := _root_.DerivedCategory.isIso_app_singleFunctor_obj_of_finite τ (fun n ↦ by
    change IsIso ((rightDerivedLowerStarProjectionMapApp Λ j K).app _)
    exact isIso_rightDerivedLowerStarProjectionMapApp_of_iso (e _).symm
      (isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_pi Λ j K n)) N
  exact isIso_rightDerivedLowerStarProjectionMapApp_of_iso (e N) key

end Etale

end AlgebraicGeometry
