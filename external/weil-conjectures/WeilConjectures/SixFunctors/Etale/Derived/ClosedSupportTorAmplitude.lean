/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.ConstantTensorProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion

/-!
# Finite Tor amplitude of the exceptional inverse image along a closed immersion

Let `i : Z ⟶ T` be a closed immersion with quasi-compact open complement `j : U ⟶ T`, and `Λ`
a finite ring. If `(U, T)` satisfies the open-complement condition with constant `c`
(`AlgebraicGeometry.Etale.OpenComplementCondition`), then `Ri^!` carries bounded constructible
complexes of Tor amplitude in `[a, b]` to bounded constructible complexes of Tor amplitude in
`[a, b + c + 1]`
(`AlgebraicGeometry.Etale.boundedConstructible_torAmplitudeIn_rightDerivedUpperShriek`,
blueprint `theorem-f-shriek-finite-coefficients--1`).

In the supported localization triangle `Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶`, the third term has Tor
amplitude in `[a, b + c]`: `j^* K` has Tor amplitude in `[a, b]`, and by the projection formula
with a finite constant coefficient
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nat`,
`proposition-open-direct-image-preserves-finite`; `Rj_*` preserves coproducts, having finite
cohomological dimension) and the residue test (`theorem-f-shriek-finite-coefficients--1`), `Rj_*`
raises the Tor amplitude by at most `c`. Tor amplitude being two out of three in triangles,
`Ri_! Ri^! K` has Tor amplitude in `[a, b + c + 1]`, and so has its pullback
`i^* Ri_! Ri^! K ≅ Ri^! K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {Z T U : Scheme.{u}}

omit [Finite Λ] in
/-- Under the vanishing clause of the open-complement condition, a quasi-compact open immersion
has finite cohomological dimension, so `Rj_*` preserves countable coproducts
(`AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar`). -/
lemma preservesColimitsOfShape_rightDerivedLowerStar_of_isZero_higherDirectImage
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M)) :
    PreservesColimitsOfShape (Discrete ℕ) (R((j)_*[ModuleCat.{u + 1} Λ])) :=
  have := preservesCoproducts_rightDerivedLowerStar Λ j (⟨c, fun F q hq ↦ by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by lia⟩
    exact (hc F n (by exact_mod_cast hq)).of_iso
      (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ j F n)⟩) (ULift.{u + 1} ℕ)
  preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

/-- The direct image along a quasi-compact open immersion `j` with `R^q j_* = 0` for `q > c`
carries complexes of Tor amplitude in `[a, b]` to complexes of Tor amplitude in `[a, b + c]`.
This is the argument of `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_finite`,
with the projection formula with a finite constant coefficient
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nat`,
`proposition-open-direct-image-preserves-finite`) and the residue test. -/
theorem torAmplitudeIn_rightDerivedLowerStar_of_isZero_higherDirectImage (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M)) {a b : ℤ}
    {L : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b L) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) T a (b + c) ((R((j)_*[ModuleCat.{u + 1} Λ])).obj L) := by
  have := preservesColimitsOfShape_rightDerivedLowerStar_of_isZero_higherDirectImage j hc
  rw [torAmplitudeIn_iff_tensorSingleConcentratedIn]
  let κ := ModuleCat.of Λ (Λ ⧸ Ring.jacobson Λ)
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nat Λ j L κ
  refine tensorSingleConcentratedIn_rightDerivedLowerStar_of_isIso _ j L κ ?_
  obtain ⟨h₁, h₂⟩ := (torAmplitudeIn_iff_forall_derivedTensor _ U a b L).1 hta
    ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj κ)
  exact ⟨@isGE_rightDerivedLowerStar_obj Λ _ U T j _ a h₁,
    @isLE_rightDerivedLowerStar_obj_of_isZero_higherDirectImage Λ _ U T j c hc _ b h₂⟩

omit [Finite Λ] in
/-- Tor amplitude is two out of three in the first term: if `X₂` has Tor amplitude in `[a, b]` and
`X₃` in `[a, b']` with `b ≤ b'`, then `X₁` has Tor amplitude in `[a, b' + 1]`, tensoring the
triangle with a sheaf being a triangulated functor. -/
lemma torAmplitudeIn_obj₁_of_distTriang
    (Tr : Triangle (_root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hTr : Tr ∈ distTriang _) {a b b' : ℤ} (hbb : b ≤ b')
    (h₂ : torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b Tr.obj₂)
    (h₃ : torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b' Tr.obj₃) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) T a (b' + 1) Tr.obj₁ := fun F ↦
  homologyConcentratedIn_obj₁ (ModuleCat.{u + 1} Λ)
    (((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).mapTriangle.obj Tr)
    (Functor.map_distinguished _ _ hTr) hbb (h₂ F) (h₃ F)

variable (i : Z ⟶ T) (j : U ⟶ T) [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
  [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)

include hij in
/-- The Tor amplitude part of blueprint `theorem-f-shriek-finite-coefficients--1`: under the
vanishing clause of the open-complement condition with constant `c`, `Ri^!` carries complexes of Tor
amplitude in `[a, b]` to complexes of Tor amplitude in `[a, b + c + 1]`, for a finite ring `Λ`. No
constructibility is needed.

In the supported localization triangle `Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶`, the second term has Tor
amplitude in `[a, b]` and the third in `[a, b + c]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_isZero_higherDirectImage`), so
the first has Tor amplitude in `[a, b + c + 1]`, and so has its pullback
`i^* Ri_! Ri^! K ≅ Ri^! K`. -/
theorem torAmplitudeIn_rightDerivedUpperShriek {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M))
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + c + 1) ((R(i)^![Λ]).obj K) := by
  have h₃ := torAmplitudeIn_rightDerivedLowerStar_of_isZero_higherDirectImage j hc
    (torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) j a b hta)
  have h₁ := torAmplitudeIn_obj₁_of_distTriang _
    (supportedLocalizationTriangle_mem_distTriang Λ i j hij K) (le_add_of_nonneg_right
      (Int.natCast_nonneg c)) hta h₃
  exact (torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + c + 1)).prop_of_iso
    (((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) i).app _) ≪≫
      mapDerivedUpperStarRightDerivedLowerShriekIso i _)
    (torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) i a (b + c + 1) h₁)

include hij in
/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: Finite Tor amplitude for closed support.

Let `Λ` be a finite ring (in the blueprint `Λ = 𝒪_E / ϖⁿ`), `i : Z ⟶ T` a closed immersion with
quasi-compact open complement `j : U ⟶ T`, such that `R^q j_*` vanishes on all sheaves of
`Λ`-modules for `q > c` and carries constructible sheaves to constructible sheaves
(`AlgebraicGeometry.Etale.OpenComplementCondition`). If `K` is bounded constructible with Tor
amplitude in `[a, b]`, then `Ri^! K` is bounded constructible with Tor amplitude in
`[a, b + c + 1]`.

Constructibility is `AlgebraicGeometry.Etale.constructibleIn_rightDerivedUpperShriek`
(`theorem-f-shriek-finite-coefficients--1`), `K` having homology in `[a, b]`; the Tor amplitude is
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedUpperShriek`. -/
theorem boundedConstructible_torAmplitudeIn_rightDerivedUpperShriek {c : ℕ}
    (h : OpenComplementCondition Λ j c) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K)
    (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z
        ((R(i)^![Λ]).obj K) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + c + 1)
        ((R(i)^![Λ]).obj K) :=
  ⟨(constructibleIn_rightDerivedUpperShriek i j hij h
      ⟨hK, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta⟩).1,
    torAmplitudeIn_rightDerivedUpperShriek i j hij h.1 hta⟩

end Etale

end AlgebraicGeometry
