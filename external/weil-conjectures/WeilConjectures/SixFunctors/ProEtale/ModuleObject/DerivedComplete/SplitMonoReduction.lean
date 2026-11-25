/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted

/-!

# Split monomorphisms into derived complete complexes

A retract of a derived complete `𝒪_E`-complex is derived complete
(`ProEtale.derivedCompleteIntegers_of_isSplitMono`). Consequently a split monomorphism
`f : K ⟶ L` with `L` derived complete is invertible as soon as its reduction `𝔽_E ⊗ᴸ f` is
(`ProEtale.CondensedRing.isIso_of_isSplitMono_of_isIso_extendScalars_map`): by derived Nakayama
for the derived complete complexes `K` and `L`
(`ProEtale.CondensedRing.isIso_of_derivedCompleteIntegers_of_isIso_extendScalars_map`).

This is how the generic-slicing step of Gabber's Künneth formula passes from `𝔽_E`- to
`𝒪_E`-coefficients without knowing that the source of the Künneth map is derived complete.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] {X : Scheme.{u}}

/-- **A retract of a derived complete complex is derived complete**: if `f : K ⟶ L` is a split
monomorphism and `L` is derived complete, so is `K`. -/
lemma derivedCompleteIntegers_of_isSplitMono
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} (f : K ⟶ L)
    [IsSplitMono f] (hL : derivedCompleteIntegers ℓ E X L) :
    derivedCompleteIntegers ℓ E X K := fun _ hZ g ↦ by
  rw [← Category.comp_id g, ← IsSplitMono.id f, ← Category.assoc, hL hZ (g ≫ f),
    Limits.zero_comp]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {X : Scheme.{u}}

/-- **A split monomorphism into a derived complete complex is invertible if its reduction is**:
for a split monomorphism `f : K ⟶ L` of `𝒪_E`-complexes with `L` derived complete, if
`𝔽_E ⊗ᴸ f` is invertible, so is `f`. -/
theorem isIso_of_isSplitMono_of_isIso_extendScalars_map
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} (f : K ⟶ L)
    [IsSplitMono f] (hL : derivedCompleteIntegers ℓ E X L)
    (h : IsIso ((Mod.extendScalars (coefficientMap
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.map f)) :
    IsIso f :=
  isIso_of_derivedCompleteIntegers_of_isIso_extendScalars_map ℓ E f
    (derivedCompleteIntegers_of_isSplitMono f hL) hL h

end AlgebraicGeometry.ProEtale.CondensedRing
