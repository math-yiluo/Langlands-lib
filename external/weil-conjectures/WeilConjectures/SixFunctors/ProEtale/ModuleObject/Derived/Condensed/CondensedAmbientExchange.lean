/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# Ambient exchange for condensed coefficient module objects

Source: blueprint main-20261015, definition-pro-etale-base-change-map--1;
Stacks Project, Remark 07A7 (blueprint: definition-pro-etale-base-change-map--1).

The general ring-sheaf exchange is publicly retained. These definitions give its
internal-module-object form for coefficients pulled back from one condensed ring.
The comparison is the published canonical derived pullback composition comparison;
its mate uses the published derived module-object adjunctions. No completeness or
constructibility condition enters this construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The canonical pullback comparison around a square for one condensed coefficient ring.
The two coefficient identifications are those obtained by pullback from the same point;
the published composition comparison is induced from the ordinary tensor pullbacks.
Source: blueprint main-20261015, definition-pro-etale-base-change-map--1, displayed theta;
Stacks Project, Remark 07A7 (blueprint: definition-pro-etale-base-change-map--1). -/
def condensedAmbientPullbackComparison (sq : ChosenCartesianSquare g' f' f g) :
    (upperStar Λ g).leftDerivedFunctor ⋙ (upperStar Λ f').leftDerivedFunctor ≅
      (upperStar Λ f).leftDerivedFunctor ⋙ (upperStar Λ g').leftDerivedFunctor :=
  (leftDerivedUpperStarComp Λ f' g).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ (upperStar Λ h).leftDerivedFunctor)
      sq.toCommSq.w.symm) ≪≫ leftDerivedUpperStarComp Λ g' f

/-- The ambient exchange on ordinary unbounded internal module objects.
This is the mate of the canonical composition comparison, under the derived
adjunctions of the full module pushforward and tensor pullback composites.
Its component inserts the unit for f', applies the square comparison under Rf'_*,
then contracts the counit for f. It is defined for every condensed ring and before
any constructibility, properness or completeness condition.
Source: blueprint main-20261015, definition-pro-etale-base-change-map--1, final formula;
Stacks Project, Remark 07A7 (blueprint: definition-pro-etale-base-change-map--1). -/
def condensedAmbientExchange (sq : ChosenCartesianSquare g' f' f g) :
    (lowerStar Λ f).rightDerivedFunctor ⋙ (upperStar Λ g).leftDerivedFunctor ⟶
      (upperStar Λ g').leftDerivedFunctor ⋙ (lowerStar Λ f').rightDerivedFunctor :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (condensedAmbientPullbackComparison Λ sq).hom))

end AlgebraicGeometry.ProEtale.CondensedRing
