/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary

/-!
# Direct images along morphisms of finite cohomological dimension

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes and `Λ` a ring, and assume
that `f` has cohomological dimension at most `d` for sheaves of `Λ`-modules: `Rᵠf_* F = 0` for
every étale sheaf `F` of `Λ`-modules on `X` and every `q > d`. This file proves:

* the scalar projection formula: for every `E ∈ D(X_ét, Λ)` and every complex `C` of
  `Λ`-modules, the projection map `Rf_* E ⊗ᴸ C_Y ⟶ Rf_*(E ⊗ᴸ C_X)` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantFunctor_obj`).
  Both sides are triangulated in `C` and commute with direct sums (`Rf_*` does, by the finite
  cohomological dimension, `proposition-open-direct-image-preserves-finite`), and the map is an
  isomorphism for `C = Λ`, which generates `D(Λ)`;
* for a finite ring `Λ`, `Rf_*` moves Tor amplitude from `[a, b]` to `[a, b + d]`
  (`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_cohomologicalDimension`), by
  the residue test.

These are parts (1) and (2) of blueprint `proposition-open-direct-image-preserves-finite`, where `f`
is an open immersion of schemes of finite type over a separably closed field (so that its
cohomological dimension is finite, `theorem-results-from-etale-theory--6`). Part (3), on the
pro-étale site, is in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  [QuasiSeparated f] (d : ℕ)
  (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
    IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))

include hd

omit [QuasiCompact f] [QuasiSeparated f] in
/-- A bound `d` for the higher direct images gives finite cohomological dimension. -/
lemma hasFiniteCohomologicalDimensionMorphism_of_isZero_rightDerived :
    HasFiniteCohomologicalDimensionMorphism Λ f := by
  refine ⟨d, fun F q hq ↦ ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by omega⟩
  exact (hd F n (by omega)).of_iso
    (((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso F n)

/-- The scalar projection formula along a morphism of finite cohomological dimension: for every
`E ∈ D(X_ét, Λ)` and every complex `C` of `Λ`-modules, with constant complexes `C_Y` and
`C_X = Lf^* C_Y`, the projection map `Rf_* E ⊗ᴸ C_Y ⟶ Rf_*(E ⊗ᴸ Lf^* C_Y)` is an isomorphism.

Both sides are triangulated functors of `C ∈ D(Λ)` commuting with direct sums: `Rf_*` does by
the finite cohomological dimension
(`AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar`,
`proposition-open-direct-image-preserves-finite`), and so do the derived tensor products, `Lf^*` and
the constant complex functor. The map is an isomorphism at `C = Λ`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit`), and
`Λ[0]` generates `D(Λ)` (`DerivedCategory.isIso_of_isIso_app_singleFunctor_obj_self`). -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_constantFunctor_obj
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : _root_.DerivedCategory (ModuleCat.{u + 1} Λ)) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app
      ((constantFunctor Λ Y).obj C)) := by
  have (J : Type (u + 1)) := preservesCoproducts_rightDerivedLowerStar Λ f
    (hasFiniteCohomologicalDimensionMorphism_of_isZero_rightDerived Λ f d hd) J
  let τ : (-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E) ⟶
      (L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj E) ⋙
        R((f)_*[ModuleCat.{u + 1} Λ]) :=
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E
  have h₂ (J : Type (u + 1)) : PreservesColimitsOfShape (Discrete J)
      ((L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj E) ⋙
        R((f)_*[ModuleCat.{u + 1} Λ])) :=
    have : PreservesColimitsOfShape (Discrete J) (L((f)^*[ModuleCat.{u + 1} Λ])) :=
      (derivedUpperStarLowerStarAdjunction _ f).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    inferInstance
  -- the constant complex functor is left adjoint to `RΓ(Y, -)`
  let adjC := constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalFinalObject Y)
  have : (constantFunctor Λ Y).IsLeftAdjoint :=
    have := adjC.right_adjoint_additive
    adjC.mapDerivedCategoryRightDerivedAdjunction.isLeftAdjoint
  have hτ : IsIso (Functor.whiskerLeft (constantFunctor Λ Y) τ) := by
    refine _root_.DerivedCategory.isIso_of_isIso_app_singleFunctor_obj_self
      (T := _root_.DerivedCategory _) (Functor.whiskerLeft (constantFunctor Λ Y) τ) ?_
    dsimp only [Functor.whiskerLeft_app]
    have hunit : IsIso (τ.app (𝟙_ _)) :=
      isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit _ f E
    refine (NatTrans.isIso_app_iff_of_iso τ ?_).2 hunit
    exact (Functor.mapDerivedCategorySingleFunctor _ 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso (Functor.Monoidal.εIso
        (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm ≪≫
      singleFunctorObjUnitIso _ _
  exact (NatTrans.isIso_iff_isIso_app _).1 hτ C

/-- The scalar projection formula at a module: for every `Λ`-module `M`, of arbitrary
projective dimension, the projection map `Rf_* E ⊗ᴸ M_Y ⟶ Rf_*(E ⊗ᴸ Lf^* M_Y)` is an
isomorphism, `f` having finite cohomological dimension. -/
theorem isIso_rightDerivedLowerStarProjectionMap_constantSingle_of_cohomologicalDimension
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y M)) :=
  (NatTrans.isIso_app_iff_of_iso _
    (((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapDerivedCategorySingleFunctor
      0).app M)).1
    (isIso_rightDerivedLowerStarProjectionMap_app_app_constantFunctor_obj Λ f d hd E
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M))

/-- For a finite ring `Λ` and a quasi-compact quasi-separated morphism `f` whose higher direct
images vanish above `d`, `Rf_*` carries complexes of Tor amplitude in `[a, b]` to complexes of
Tor amplitude in `[a, b + d]`.

Let `κ = Λ ⧸ J`, `J` the Jacobson radical. By the scalar projection formula,
`Rf_* K ⊗ᴸ κ_Y ≅ Rf_*(K ⊗ᴸ κ_X)`; the complex `K ⊗ᴸ κ_X` has homology in `[a, b]`, so its
direct image has homology in `[a, b + d]`, `Rf_*` being left t-exact and raising degrees by at
most `d` (`CategoryTheory.Functor.isLE_rightDerivedFunctor_obj`). The residue test
(`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn`)
concludes. -/
theorem torAmplitudeIn_rightDerivedLowerStar_of_cohomologicalDimension [Finite Λ] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + d) ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  rw [torAmplitudeIn_iff_tensorSingleConcentratedIn]
  let κ := ModuleCat.of Λ (Λ ⧸ Ring.jacobson Λ)
  have := isIso_rightDerivedLowerStarProjectionMap_constantSingle_of_cohomologicalDimension
    Λ f d hd K κ
  refine tensorSingleConcentratedIn_rightDerivedLowerStar_of_isIso _ f K κ ?_
  obtain ⟨h₁, h₂⟩ := (torAmplitudeIn_iff_forall_derivedTensor _ X a b K).1 hta
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj κ)
  exact ⟨@isGE_rightDerivedLowerStar_obj Λ _ X Y f _ a h₁,
    ((f)_*[ModuleCat.{u + 1} Λ]).isLE_rightDerivedFunctor_obj d hd _ b⟩

end AlgebraicGeometry.Etale
