/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.RetractionLift

/-!
# Split monomorphisms and the coefficient change `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`Φ_X = ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} -) : D(X_proét, 𝒪_E) ⥤ D(X_proét, ℚ̄_ℓ)` the extension of scalars
along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` (`ProEtale.integralToPadicAlgCl`). Like every functor, `Φ_X` sends split
monomorphisms to split monomorphisms. Hence a morphism `g` of `ℚ̄_ℓ`-complexes which is isomorphic,
as an arrow, to `Φ_X i` for a split monomorphism `i` of `𝒪_E`-complexes is a split monomorphism
(`ProEtale.isSplitMono_of_nonempty_arrowIso_integralToPadicAlgCl_map`). This is how split
injectivity passes from `𝒪_E`- to `ℚ̄_ℓ`-coefficients: the coefficient-change compatibilities of the
six operations provide the arrow isomorphism, for instance
`ProEtale.CondensedRing.nonempty_arrowIso_boundedConstructibleBaseChange_integralToPadicAlgCl`
for base change morphisms.

Combined with the lifting of compatible torsion retractions to `𝒪_E`
(`ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`), this gives
`ProEtale.isSplitMono_of_nonempty_arrowIso_integralToPadicAlgCl_of_unique_retractions`: `g` is a
split monomorphism as soon as `g ≅ Φ_X i` for a morphism `i : A ⟶ B` of `𝒪_E`-complexes with `A`
derived complete whose reductions modulo `ℓⁿ⁺¹` have unique retractions with a property preserved
by reduction (for nearby cycles: invariance under the inertia group, SGA 4½, [Th. finitude],
Lemme 3.4).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) {ℓ : ℕ} [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- The extension of scalars `Φ_X = ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} -)` along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`, from
complexes of `𝒪_{E,X}`-module objects to complexes of `ℚ̄_{ℓ,X}`-module objects on `X_proét`. -/
noncomputable abbrev integralToPadicAlgCl :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) :=
  L(Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)) ⋙
    derivedExtendScalarsToPadicAlgCl X ℓ E

variable {X E}

/-- **Split monomorphisms pass from `𝒪_E` to `ℚ̄_ℓ`**: a morphism of `ℚ̄_ℓ`-complexes isomorphic,
as an arrow, to the extension of scalars `Φ_X i` of a split monomorphism `i` of `𝒪_E`-complexes
is a split monomorphism. -/
theorem isSplitMono_of_nonempty_arrowIso_integralToPadicAlgCl_map
    {A' B' : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))}
    (g : A' ⟶ B') {A B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} (i : A ⟶ B) [IsSplitMono i]
    (e : Nonempty (Arrow.mk g ≅ Arrow.mk ((integralToPadicAlgCl X E).map i))) :
    IsSplitMono g :=
  Arrow.isSplitMono_of_iso e.some

/-- **Lifting unique torsion retractions to `ℚ̄_ℓ`-coefficients.** Let `g` be a morphism of
`ℚ̄_ℓ`-complexes isomorphic, as an arrow, to `Φ_X i` for a morphism `i : A ⟶ B` of
`𝒪_E`-complexes with `A` derived complete. Suppose that each reduction `i ⊗ᴸ 𝒪_E/ℓⁿ⁺¹` has a
retraction with a property `Pₙ`, that such a retraction is unique, and that the reduction modulo
`ℓⁿ⁺¹` of a retraction with property `Pₙ₊₁` has property `Pₙ`. Then `g` is a split monomorphism. -/
theorem isSplitMono_of_nonempty_arrowIso_integralToPadicAlgCl_of_unique_retractions
    {A' B' : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))}
    (g : A' ⟶ B') {A B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} (i : A ⟶ B)
    (e : Nonempty (Arrow.mk g ≅ Arrow.mk ((integralToPadicAlgCl X E).map i)))
    (hA : derivedCompleteIntegers ℓ E.1 X A)
    (P : ∀ n, (L(Mod.extendScalars (integersModPowReduction X ℓ E.1 (n + 1))).obj B ⟶
      L(Mod.extendScalars (integersModPowReduction X ℓ E.1 (n + 1))).obj A) → Prop)
    (hex : ∀ n, ∃ r, P n r ∧
      L(Mod.extendScalars (integersModPowReduction X ℓ E.1 (n + 1))).map i ≫ r = 𝟙 _)
    (huniq : ∀ n r r', P n r → P n r' →
      L(Mod.extendScalars (integersModPowReduction X ℓ E.1 (n + 1))).map i ≫ r = 𝟙 _ →
      L(Mod.extendScalars (integersModPowReduction X ℓ E.1 (n + 1))).map i ≫ r' = 𝟙 _ →
      r = r')
    (hred : ∀ n r, P (n + 1) r →
      L(Mod.extendScalars (integersModPowReduction X ℓ E.1 (n + 1 + 1))).map i ≫ r = 𝟙 _ →
      P n (Mod.derivedExtendScalarsReduction (integersModPowReduction X ℓ E.1 (n + 1 + 1))
        (modPowTransition X ℓ E.1 (n + 1)) (integersModPowReduction X ℓ E.1 (n + 1))
        (integersModPowReduction_comp_modPowTransition X ℓ E.1 (n + 1)) r)) :
    IsSplitMono g :=
  have := isSplitMono_of_derivedCompleteIntegers_of_unique_retractions i hA P hex huniq hred
  isSplitMono_of_nonempty_arrowIso_integralToPadicAlgCl_map g i e

end AlgebraicGeometry.ProEtale
