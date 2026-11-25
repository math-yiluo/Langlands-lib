/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsRetractionLift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ModPowReduction

/-!
# Lifting retractions from torsion coefficients to `𝒪_E`-coefficients

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, `X` a scheme and
`i : A ⟶ B` a morphism of complexes of `𝒪_{E,X}`-module objects on `X_proét`, with `A` derived
complete. For `n ≥ 1` write `Aₙ = A ⊗ᴸ_{𝒪_E} 𝒪_E/ℓⁿ` and `iₙ : Aₙ ⟶ Bₙ` for the reductions,
complexes of `(𝒪_E/ℓⁿ)_X`-module objects
(`L(Mod.extendScalars (ProEtale.integersModPowReduction X ℓ E n))`).

* `ProEtale.isSplitMono_of_derivedCompleteIntegers_of_retractions`: if there are morphisms
  `rₙ : Bₙ ⟶ Aₙ`, compatible with reduction (`Bₙ₊₁ ⟶ Aₙ₊₁` reduces modulo `ℓⁿ` to `rₙ`,
  `Mod.derivedExtendScalarsReduction`), with `r₁` a retraction of `i₁`, then `i` is a split
  monomorphism. The retraction is obtained by lifting `(rₙ)ₙ` through `A = R lim Aₙ` (the Milnor
  sequence, of which only the surjectivity onto `lim Hom(B, Aₙ)` is used) and correcting by
  derived Nakayama; see `CategoryTheory.Mod.isSplitMono_of_isCenterComplete_of_retractions`.
* `ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`: the compatibility is
  automatic when each `iₙ` has a unique retraction with a property `Pₙ` preserved by reduction,
  for instance the unique retraction invariant under a Galois action, which exists for the
  exchange maps of torsion nearby cycles along a pro-`p` Galois layer (SGA 4½, [Th. finitude],
  Lemme 3.4). The `lim¹` term of the Milnor sequence need not vanish.

The derived complete complexes are complete with respect to the action of `ℓ`
(`ProEtale.isCenterComplete_of_derivedCompleteIntegers`): if `ℓ` acts invertibly on `Z`, the first
derived reduction of `Z` vanishes, since `ℓ = 0` in `𝔽_E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]
  {X : Scheme.{u}}

/-- A derived complete `𝒪_E`-complex is complete with respect to the action of `ℓ`: a complex on
which `ℓ` acts invertibly has vanishing first derived reduction, `ℓ` being zero in `𝔽_E`. -/
lemma isCenterComplete_of_derivedCompleteIntegers
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : derivedCompleteIntegers ℓ E X K) :
    IsCenterComplete ((ℓ : ℤ) • (1 : CatCenter (DerivedCategory (Mod
      (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))))) K := by
  intro Z hZ f
  rw [CatCenter.zsmul_one_app] at hZ
  refine hK ?_ f
  refine DerivedCategory.isZero_of_isIso_zsmul_id
    (Sheaf.zsmul_id_eq_zero_of_intCast_eq_zero ?_) (m := (ℓ : ℤ)) ?_
  · rw [Int.cast_natCast, natCast_eq_zero_residueFieldCoeff]
  · have : (derivedReduction X ℓ E).Additive := inferInstanceAs (Functor.Additive (_ ⋙ _))
    rw [← (derivedReduction X ℓ E).map_id, ← Functor.map_zsmul]
    infer_instance

/-- **Lifting compatible retractions from `𝒪_E/ℓⁿ` to `𝒪_E`.** Let `i : A ⟶ B` be a morphism of
`𝒪_E`-complexes on `X_proét` with `A` derived complete, and let
`rₙ : B ⊗ᴸ 𝒪_E/ℓⁿ⁺¹ ⟶ A ⊗ᴸ 𝒪_E/ℓⁿ⁺¹` be compatible with reduction, with `r₀` a retraction of
`i ⊗ᴸ 𝒪_E/ℓ`. Then `i` is a split monomorphism. -/
theorem isSplitMono_of_derivedCompleteIntegers_of_retractions
    {A B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} (i : A ⟶ B)
    (hA : derivedCompleteIntegers ℓ E X A)
    (r : ∀ n, L(Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).obj B ⟶
      L(Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).obj A)
    (hr : L(Mod.extendScalars (integersModPowReduction X ℓ E (0 + 1))).map i ≫ r 0 = 𝟙 _)
    (hcompat : ∀ n, Mod.derivedExtendScalarsReduction (integersModPowReduction X ℓ E (n + 1 + 1))
      (modPowTransition X ℓ E (n + 1)) (integersModPowReduction X ℓ E (n + 1))
      (integersModPowReduction_comp_modPowTransition X ℓ E (n + 1)) (r (n + 1)) = r n) :
    IsSplitMono i :=
  Mod.isSplitMono_of_isCenterComplete_of_retractions
    (S := fun n ↦ condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) X)
    (fun n ↦ integersModPowReduction_comp_modPowTransition X ℓ E (n + 1)) (ℓ : ℤ)
    (fun n ↦ zsmul_id_comp_integersModPowReduction X ℓ E (n + 1))
    (fun n ↦ shortExact_integersModPowReduction X ℓ E (n + 1)) i
    (isCenterComplete_of_derivedCompleteIntegers hA) r hr hcompat

/-- **Lifting unique retractions from `𝒪_E/ℓⁿ` to `𝒪_E`.** Let `i : A ⟶ B` be a morphism of
`𝒪_E`-complexes on `X_proét` with `A` derived complete. Suppose that each reduction
`i ⊗ᴸ 𝒪_E/ℓⁿ⁺¹` has a retraction with a property `Pₙ` (for instance, invariance under a Galois
action), that such a retraction is unique, and that the reduction modulo `ℓⁿ⁺¹` of a retraction
with property `Pₙ₊₁` has property `Pₙ`. Then `i` is a split monomorphism. -/
theorem isSplitMono_of_derivedCompleteIntegers_of_unique_retractions
    {A B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} (i : A ⟶ B)
    (hA : derivedCompleteIntegers ℓ E X A)
    (P : ∀ n, (L(Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).obj B ⟶
      L(Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).obj A) → Prop)
    (hex : ∀ n, ∃ r, P n r ∧
      L(Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).map i ≫ r = 𝟙 _)
    (huniq : ∀ n r r', P n r → P n r' →
      L(Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).map i ≫ r = 𝟙 _ →
      L(Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).map i ≫ r' = 𝟙 _ →
      r = r')
    (hred : ∀ n r, P (n + 1) r →
      L(Mod.extendScalars (integersModPowReduction X ℓ E (n + 1 + 1))).map i ≫ r = 𝟙 _ →
      P n (Mod.derivedExtendScalarsReduction (integersModPowReduction X ℓ E (n + 1 + 1))
        (modPowTransition X ℓ E (n + 1)) (integersModPowReduction X ℓ E (n + 1))
        (integersModPowReduction_comp_modPowTransition X ℓ E (n + 1)) r)) :
    IsSplitMono i :=
  Mod.isSplitMono_of_isCenterComplete_of_unique_retractions
    (S := fun n ↦ condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) X)
    (fun n ↦ integersModPowReduction_comp_modPowTransition X ℓ E (n + 1)) (ℓ : ℤ)
    (fun n ↦ zsmul_id_comp_integersModPowReduction X ℓ E (n + 1))
    (fun n ↦ shortExact_integersModPowReduction X ℓ E (n + 1)) i
    (isCenterComplete_of_derivedCompleteIntegers hA) P hex huniq hred

end AlgebraicGeometry.ProEtale
