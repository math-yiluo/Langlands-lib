/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeLineTensorFiniteness
public import WeilConjectures.AlgebraicGeometry.Native.NativeSignedLine
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Ordinary derived finiteness for signed local lines
Source: definition-tate-twists--10 (blueprint: lem-twist-native-signed-finiteness).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Fix the site universe before generic imported enlargement instances are tried.
local instance (Y : Scheme.{u}) : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0} _

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- The native module category for the pulled-back condensed coefficient ring.
Source: definition-tate-twists--10 (blueprint: lem-twist-native-signed-finiteness). -/
abbrev NativeTwistModules : Type (u + 2) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

section SignedLine

variable (L : NativeTwistModules Λ X)

end SignedLine

end AlgebraicGeometry.ProEtale.CondensedRing
