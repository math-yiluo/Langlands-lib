/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralLocalizingCompactSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.Compactification.BoundaryRefinement

/-!
# The integral Brown exceptional adjoint

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-int-brown,
sk-prop-int-brown-adjoint.md and its proof (blueprint: theorem-existence-exceptional-inverse-image).

The left adjoint restricts the recorded compactification composite to Loc(Dbc).
Identification with the general Loc(Dctf) adjoint is expressed in the common ambient
category, by the unique natural isomorphism satisfying the counit equation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Restriction of the recorded compactification composite to Loc(Dbc). Membership
proofs change neither its objects nor its morphisms. This is the functor in
`integralLocalizingCompactSupport`, with its codomain restricted as well.
Source: blueprint sk-prop-int-brown-adjoint, displayed left adjoint
(blueprint: theorem-existence-exceptional-inverse-image). -/
def lowerShriek (c : Compactification f)
    (h : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c).obj K)) :
    (localizing Λ X).FullSubcategory ⥤ (localizing Λ Y).FullSubcategory :=
  (localizing Λ Y).lift ((localizing Λ X).ι ⋙ image Λ c)
    (fun K ↦ h K.obj K.property)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
