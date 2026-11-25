/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # The canonical exchange mate over a commutative square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Equality transport for internal derived inverse images, by equality induction.
Source: transport of the published derived inverse-image functor
(blueprint: def-sfb-finite-proper-exchange). -/
@[no_expose] noncomputable def finitePullbackCongr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (upperStar Λ f).leftDerivedFunctor ≅ (upperStar Λ g).leftDerivedFunctor :=
  h ▸ Iso.refl _

/-- Equality induction normalizes reflexive pullback transport.
Source: the reflexivity equation for equality transport
(blueprint: def-sfb-finite-proper-exchange). -/
@[simp] theorem finitePullbackCongr_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finitePullbackCongr Λ (rfl : f = f) = Iso.refl _ := by
  rfl

/-- Equality-induction transport is the original equality-to-isomorphism transport.
Source: equality induction for the published derived inverse-image functor
(blueprint: def-sfb-finite-proper-exchange). -/
theorem finitePullbackCongr_eqToIso
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    finitePullbackCongr Λ h =
      eqToIso (congrArg (fun (k : X ⟶ Y) ↦ (upperStar Λ k).leftDerivedFunctor) h) := by
  cases h
  rfl

/-- The canonical internal derived inverse-image square, kept as a named isomorphism.
Source: the published pullback compositors and equality transport
(blueprint: def-sfb-finite-proper-exchange). -/
@[no_expose] noncomputable def finitePullbackSquare
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    (upperStar Λ g).leftDerivedFunctor ⋙ (upperStar Λ p').leftDerivedFunctor ≅
      (upperStar Λ p).leftDerivedFunctor ⋙ (upperStar Λ g').leftDerivedFunctor :=
  (leftDerivedUpperStarComp Λ p' g).symm ≪≫
    finitePullbackCongr Λ sq.w.symm ≪≫
    leftDerivedUpperStarComp Λ g' p

/-- The unit-square-counit mate of the canonical derived pullback compositor.
Source: blueprint proper-base-change-finite, clause (2), and the canonical mate convention.
(blueprint: def-sfb-finite-proper-exchange). -/
@[no_expose] noncomputable def finiteProperExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    (lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ g).leftDerivedFunctor ⟶
      (upperStar Λ g').leftDerivedFunctor ⋙ (lowerStar Λ p').rightDerivedFunctor :=
  (mateEquiv
    (G := (upperStar Λ g).leftDerivedFunctor)
    (H := (upperStar Λ g').leftDerivedFunctor)
    (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p')
    (TwoSquare.mk _ _ _ _ (finitePullbackSquare Λ sq).hom))

/-- The canonical exchange is its defining mate, without exposing the construction.
Source: the definition of the unit-square-counit exchange
(blueprint: def-sfb-finite-proper-exchange). -/
theorem finiteProperExchange_eq_mate
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    finiteProperExchange Λ sq =
      (mateEquiv (derivedUpperStarLowerStarAdjunction Λ p)
        (derivedUpperStarLowerStarAdjunction Λ p')
        (TwoSquare.mk _ _ _ _ (finitePullbackSquare Λ sq).hom)) := by
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
