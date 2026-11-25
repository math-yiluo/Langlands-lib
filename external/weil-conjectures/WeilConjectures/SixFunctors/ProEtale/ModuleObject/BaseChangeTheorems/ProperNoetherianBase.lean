/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeResidueExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Proper base change for `ℚ̄_ℓ`-sheaves over noetherian bases

Consider a cartesian square of schemes
```
X' --g'--> X
|p'        |p
v          v
Y' --g---> Y
```
with `p` proper, where `Y` is a noetherian `k`-scheme and `Y'` is a noetherian `k₂`-scheme for
possibly different fields `k` and `k₂` in which `ℓ` is invertible, and `g` is arbitrary. We show
that the base change map `Lg^* Rp_* ⟶ Rp'_* Lg'^*` on the ambient derived categories of
`ℚ̄_ℓ`-module objects is invertible at every bounded constructible complex
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`).

The proof follows blueprint `theorem-smooth-base-change-all-admissible`, on the ambient derived
categories since the square mixes the two base fields:
* a bounded constructible `ℚ̄_ℓ`-complex has an integral model `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)`
  (`ProEtale.CondensedRing.exists_padicAlgCl_iso_integralModel_obj`), and the base change map
  at it is invertible as soon as the integral one at `K₀` is
  (`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral`);
* the integral base change map at `K₀` is a morphism of bounded constructible complexes
  (`boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj`), so by
  derived Nakayama (`ProEtale.isIso_of_isIso_derivedReduction_map`) it suffices that its first
  derived reduction is invertible. This is the pro-étale base change map with coefficients `𝔽_E`
  at a complex of étale origin
  (`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_map_exchangeRight`), an isomorphism
  by finite-level proper base change (`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`).

## Main statements

- `ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_isProper_of_isNoetherian`:
  the integral case.
- `ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`:
  `ℚ̄_ℓ` proper base change over noetherian bases over fields.

## Implementation notes

The base change maps `baseChangeMap Λ sq` are by definition exchange morphisms, but the two
elaborations carry different proofs of instances; they are identified by `cast_proofs`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Integral proper base change over noetherian bases**: for a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper, `X` noetherian, `Y` a noetherian `k`-scheme and `Y'` a
noetherian `k₂`-scheme (`ℓ` invertible in `k` and `k₂`), the base change map with coefficients
`𝒪_E` is invertible at every bounded constructible `𝒪_E`-complex `K₀`. Both sides are bounded
constructible, so by derived Nakayama (`ProEtale.isIso_of_isIso_derivedReduction_map`) it
suffices that the first derived reduction is invertible; this is the base change map with
coefficients `𝔽_E` (`nonempty_arrowIso_derivedReduction_map_exchangeRight`) at a complex of
étale origin, invertible by finite-level proper base change
(`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`). -/
theorem isIso_baseChangeMap_app_padicIntegers_of_isProper_of_isNoetherian {k k₂ : Type u}
    [Field k] [Field k₂] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar k₂ ≠ ℓ)]
    {X Y X' Y' : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Y']
    (aY : Y ⟶ Spec (.of k)) (aY' : Y' ⟶ Spec (.of k₂)) {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'}
    {g' : X' ⟶ X} [IsProper p] (sq : CommSq g' p' p g) (hsq : IsPullback g' p' p g)
    (E : FiniteIntermediateField ℓ)
    (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) sq).app K₀.obj) := by
  have : IsProper p' := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E.1)))
  have h₁ := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g _
    (boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj ℓ E.1
      aY p K₀.obj K₀.property)
  have h₂ := boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj ℓ
    E.1 aY' p' _ (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g' K₀.obj
      K₀.property)
  have hfin := isIso_derivedBaseChangeMap_app_of_isProper (ResidueFieldCoeff.{u} ℓ E) hsq _
    (boundedConstructible_derivedReduction_obj X ℓ E _ K₀.property).plusEtaleOrigin
  have : K₀.obj.IsGE K₀.property.1.1.choose := K₀.property.1.1.choose_spec
  have h₃ := isIso_of_nonempty_arrowIso_map (𝟭 _) hfin
    ((nonempty_arrowIso_derivedReduction_map_exchangeRight ℓ E
      hsq.toCommSq K₀.obj K₀.property.1.1.choose).map Iso.symm)
  have h₄ : IsIso ((derivedReduction Y' ℓ E).map
      ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) sq).app K₀.obj)) := by
    unfold baseChangeMap
    cast_proofs h₃
  let φ : (⟨_, by exact_mod_proofs h₁⟩ : BoundedConstructible _) ⟶ ⟨_, by exact_mod_proofs h₂⟩ :=
    ObjectProperty.homMk ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) sq).app K₀.obj)
  have h₅ := (ObjectProperty.isIso_hom_iff _).2 (isIso_of_isIso_derivedReduction_map Y' ℓ E φ h₄)
  rw [ObjectProperty.homMk_hom] at h₅
  exact h₅

/-- **Proper base change for `ℚ̄_ℓ`-sheaves over noetherian bases over fields**: for a cartesian
square of schemes
```
X' --g'--> X
|p'        |p
v          v
Y' --g---> Y
```
with `p` proper, `Y` a noetherian `k`-scheme and `Y'` a noetherian `k₂`-scheme for fields `k` and
`k₂` in which `ℓ` is invertible, and `g` arbitrary, the base change map
`Lg^* Rp_* ⟶ Rp'_* Lg'^*` on the ambient derived categories of `ℚ̄_ℓ`-module objects is
invertible at every bounded constructible complex `K`.

As in the proof of blueprint `theorem-smooth-base-change-all-admissible`: `K` has an integral model
(`exists_padicAlgCl_iso_integralModel_obj`), which reduces the claim to the integral base change
map (`isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral`), invertible by
`isIso_baseChangeMap_app_padicIntegers_of_isProper_of_isNoetherian`. -/
theorem isIso_baseChangeMap_app_padicAlgCl_of_isProper
    {k k₂ : Type u} [Field k] [Field k₂] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar k₂ ≠ ℓ)]
    {X Y X' Y' : Scheme.{u}} [IsNoetherian Y] [IsNoetherian Y'] (aY : Y ⟶ Spec (.of k))
    (aY' : Y' ⟶ Spec (.of k₂)) {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    [IsProper p] (sq : CommSq g' p' p g) (hsq : IsPullback g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq).app K) := by
  have : IsProper p' := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  have k := exists_padicAlgCl_iso_integralModel_obj ℓ X K hK
  obtain ⟨E, K₀, he⟩ := k
  have ha := K₀.property.1.1.choose_spec
  have : K₀.obj.IsGE K₀.property.1.1.choose := ha
  exact isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral ℓ sq E K₀.obj
    K₀.property.1.1.choose
    (isIso_baseChangeMap_app_padicIntegers_of_isProper_of_isNoetherian ℓ aY aY' sq hsq E K₀)
    he.some

end AlgebraicGeometry.ProEtale.CondensedRing
