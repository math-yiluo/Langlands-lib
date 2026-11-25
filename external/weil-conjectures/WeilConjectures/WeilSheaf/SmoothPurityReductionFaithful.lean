/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms

/-! # Detecting equality through reductions with vanishing Milnor obstruction -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- Equality of reductions detects equality when the Milnor obstruction vanishes. -/
theorem eq_of_derivedReduction_map_eq
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    [∀ n : ℕ, Finite (K⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L))]
    {f g : K ⟶ L}
    (h : ∀ n : ℕ,
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map f =
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map g) :
    f = g := by
  apply eq_of_comp_unit_eq hL
  intro n
  rw [(derivedReduction_map_eq_iff (n + 1) f _).1 (h n),
    (derivedReduction_map_eq_iff (n + 1) g _).1 rfl]


end AlgebraicGeometry.ProEtale
