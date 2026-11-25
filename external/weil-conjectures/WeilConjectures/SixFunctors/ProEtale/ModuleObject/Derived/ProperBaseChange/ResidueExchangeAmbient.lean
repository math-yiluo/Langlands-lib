/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisons
public import WeilConjectures.CategoryTheory.ProperBaseChange.TransportedCompositeIso

/-! # The ambient residue exchange square and its mate

The pullback-square comparison and the exchange mate on the ambient residue categories, split
out of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedExchangeAmbient`
so that they do not import the bounded constructible six functors.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_residueExchangeAmbient
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The ambient pullback square uses precisely the library's composition constraints.
Source: the composition constraints used in MorphismDefs.
(blueprint: def-weil-pbc-residue-exchange-ambient). -/
noncomputable def residueExchangeSquare (sq : CommSq g' f' f g) :
    residueExchangeUpperStar Λ g ⋙ residueExchangeUpperStar Λ f' ≅
      residueExchangeUpperStar Λ f ⋙ residueExchangeUpperStar Λ g' :=
  transportedCompositeIso (residueExchangeUpperStarComp Λ f' g).symm
    (residueExchangeUpperStarComp Λ g' f)
    (congrArg (fun h : X' ⟶ Y ↦ residueExchangeUpperStar Λ h) sq.w.symm)

/-- The ambient exchange is the adjunction mate of the pullback-square comparison.
Source: the unit-square-counit definition of exchange.
(blueprint: def-weil-pbc-residue-exchange-ambient). -/
noncomputable def residueExchangeBaseChange (sq : CommSq g' f' f g) :
    residueExchangeLowerStar Λ f ⋙ residueExchangeUpperStar Λ g ⟶
      residueExchangeUpperStar Λ g' ⋙ residueExchangeLowerStar Λ f' :=
  (mateEquiv (residueExchangeAdjunction Λ f)
    (residueExchangeAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (residueExchangeSquare Λ sq).hom))

/-- The counit equation characterizing the ambient exchange mate.
Source: Mathlib, mateEquiv_counit.
(blueprint: lem-weil-pbc-residue-exchange-counit)
Proof. Apply the mates equivalence's counit identity to the pullback-square comparison.
-/
theorem residueExchangeBaseChange_counit (sq : CommSq g' f' f g)
    (K : residueExchangeDerived Λ X) :
    (residueExchangeUpperStar Λ f').map ((residueExchangeBaseChange Λ sq).app K) ≫
      (residueExchangeAdjunction Λ f').counit.app
        ((residueExchangeUpperStar Λ g').obj K) =
    (residueExchangeSquare Λ sq).hom.app ((residueExchangeLowerStar Λ f).obj K) ≫
      (residueExchangeUpperStar Λ g').map ((residueExchangeAdjunction Λ f).counit.app K) := by
  exact mateEquiv_counit (residueExchangeAdjunction Λ f)
    (residueExchangeAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (residueExchangeSquare Λ sq).hom) K

end AlgebraicGeometry.ProEtale.CondensedRing
