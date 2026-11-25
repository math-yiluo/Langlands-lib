/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms

/-! # A named derived reduction functor for orientation reconstruction -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

/-- Derived reduction modulo a power of the coefficient prime. Naming the functor avoids
repeated elaboration of the derived-functor instance in reconstruction statements. -/
noncomputable def purityIntegralReduction (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ⥤
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)) :=
  (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor

end AlgebraicGeometry.ProEtale
