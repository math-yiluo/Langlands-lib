/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeSumFree

/-! # Ranges in a continuous-function presentation

Source: the continuous coefficient encoding and ordinary sectionwise range.
(blueprint: def-sfb-continuous-function-presentation-range)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] continuousRingModuleEquivalence

/-- The actual section range of an internal module map in a specified continuous
function presentation.
Source: blueprint, stratified lattice trace proof, Local computation.
(blueprint: def-sfb-continuous-function-presentation-range) -/
def continuousFunctionPresentationRange
    {E : Type} [NormedField E] [IsTopologicalRing E]
    (A : Subring E) [TotallyDisconnectedSpace A] {Y : Scheme.{u}} {r : ℕ}
    {N Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y)}
    (c : ContinuousFunctionPresentation Y A (Fin r → E) Q) (f : N ⟶ Q)
    (B : Y.ProEt) : Set C(B.left, Fin r → E) :=
  Set.range (fun x ↦ c.sections B
    (((continuousRingModuleEquivalence Y A).functor.map f).val.app (op B) x))

/-- The section range construction is the ordinary range of the encoded map.
Source: the defining formula.
(blueprint: def-sfb-continuous-function-presentation-range) -/
theorem continuousFunctionPresentationRange_eq
    {E : Type} [NormedField E] [IsTopologicalRing E]
    (A : Subring E) [TotallyDisconnectedSpace A] {Y : Scheme.{u}} {r : ℕ}
    {N Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y)}
    (c : ContinuousFunctionPresentation Y A (Fin r → E) Q) (f : N ⟶ Q)
    (B : Y.ProEt) :
    continuousFunctionPresentationRange A c f B =
      Set.range (fun x ↦ c.sections B
      (((continuousRingModuleEquivalence Y A).functor.map f).val.app (op B) x)) := rfl

end AlgebraicGeometry.ProEtale.CondensedRing
