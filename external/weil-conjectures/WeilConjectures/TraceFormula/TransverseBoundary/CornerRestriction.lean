/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.GroupTheory.SpecificGroups.Cyclic
public import WeilConjectures.TraceFormula.TransverseBoundary.LocalPurity
public import WeilConjectures.TraceFormula.TransverseBoundary.PuncturedTrait

/-!
# The restriction to the punctured trait at a transverse corner

Let `S` be the strict localization of the surface `Z` of a transverse corner
(`AlgebraicGeometry.Scheme.TransverseCorner`) at a geometric point `z̄` over the corner point,
`X_S, Y_S` the two transverse divisors and `ℓ` a prime invertible in `k`. The restriction map
`RΓ(S - Y_S, 𝔽_ℓ) ⟶ RΓ(X_S - z, 𝔽_ℓ)` is an isomorphism (blueprint
`lemma-punctured-surface-punctured-curve--1`).

Both sides have cohomology `𝔽_ℓ` in degrees `0` and `1` and none in higher degrees: for the
surface by purity along the regular divisor `Y`
(`AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_pullback_strictLocalizationToBase`), for the
punctured trait by Galois cohomology
(`AlgebraicGeometry.Scheme.TransverseCorner.nonempty_addEquiv_sheafH_puncturedTrait`). In degree
`0` both are the constants of connected schemes, and in degree `1` the restriction is nonzero
(Kummer classes, `TransverseCorner.cohomologyMap_one_puncturedTraitι_ne_zero`),
hence bijective between groups of order `ℓ`.

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.bijective_cohomologyMap_puncturedTraitι`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] [IsAlgClosed k] (C : TransverseCorner k) {Ω : Type u} [Field Ω]
  [IsAlgClosed Ω] (zbar : Spec (.of Ω) ⟶ C.Z) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
  (hz : Set.range zbar = {C.z})

omit [IsAlgClosed k] [IsAlgClosed Ω] in
include hz in
/-- The geometric point `z̄` lies on the divisor `Y`. -/
lemma range_zbar_subset_range_iY : Set.range zbar ⊆ Set.range C.iY := by
  rw [hz, Set.singleton_subset_iff]
  exact (C.range_inter ▸ Set.mem_singleton C.z : C.z ∈ Set.range C.iX ∩ Set.range C.iY).2

include hℓ hz

/-- Blueprint `lemma-punctured-surface-punctured-curve--1`, *the surface*: `H^q(S - Y_S, ℤ/ℓ) = 0`
for `q ≥ 2`. -/
theorem subsingleton_sheafH_puncturedStrictLocalization (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H ((C.puncturedStrictLocalization zbar).constantZMod ℓ) q) :=
  subsingleton_sheafH_pullback_strictLocalizationToBase C.aZ C.isEtaleLimitOfSmoothSurfaces C.iY
    C.j C.range_j hℓ zbar (C.range_zbar_subset_range_iY zbar hz) q hq

/-- Blueprint `lemma-punctured-surface-punctured-curve--1`, *the surface*: `H^0(S - Y_S, ℤ/ℓ)` and
`H^1(S - Y_S, ℤ/ℓ) ≅ 𝔽_ℓ(-1)` are free of rank one over `𝔽_ℓ`. -/
theorem nonempty_addEquiv_sheafH_puncturedStrictLocalization (q : ℕ) (hq : q ≤ 1) :
    Nonempty (Sheaf.H ((C.puncturedStrictLocalization zbar).constantZMod ℓ) q ≃+ ZMod ℓ) :=
  nonempty_addEquiv_sheafH_pullback_strictLocalizationToBase C.aZ C.isEtaleLimitOfSmoothSurfaces
    C.iY C.j C.range_j hℓ zbar (C.range_zbar_subset_range_iY zbar hz) q hq

/-- Blueprint `lemma-punctured-surface-punctured-curve--1`: Constant coefficients near a transverse
corner. The restriction map `RΓ(S - Y_S, 𝔽_ℓ) ⟶ RΓ(X_S - z, 𝔽_ℓ)` is an isomorphism: in every
degree `q` the restriction `H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` is bijective. In degree `0`
both sides are the constants of connected schemes; in degrees `q ≥ 2` both sides vanish; in
degree `1` both sides have `ℓ` elements and the map is nonzero (Kummer classes). -/
theorem bijective_cohomologyMap_puncturedTraitι (q : ℕ) :
    Function.Bijective
      (Etale.cohomologyMap (C.puncturedTraitι zbar)
        ((C.puncturedStrictLocalization zbar).constantZMod ℓ) q) := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q
    · exact C.bijective_cohomologyMap_zero_puncturedTraitι zbar hz
    · obtain ⟨e₁⟩ := C.nonempty_addEquiv_sheafH_puncturedStrictLocalization zbar hℓ hz 1 le_rfl
      obtain ⟨e₂⟩ := C.nonempty_addEquiv_sheafH_puncturedTrait zbar hℓ hz 1 le_rfl
      refine AddMonoidHom.bijective_of_card_eq_prime (p := ℓ) ?_ ?_ _
        (C.cohomologyMap_one_puncturedTraitι_ne_zero zbar hℓ hz)
      · rw [Nat.card_congr e₁.toEquiv, Nat.card_zmod]
      · rw [Nat.card_congr (C.sheafHUpperStarConstantZModEquiv zbar 1), Nat.card_congr e₂.toEquiv,
          Nat.card_zmod]
  · have := C.subsingleton_sheafH_puncturedStrictLocalization zbar hℓ hz q hq
    have : Subsingleton (Sheaf.H (((C.puncturedTraitι zbar)^*[AddCommGrpCat.{u + 1}]).obj
        ((C.puncturedStrictLocalization zbar).constantZMod ℓ)) q) := by
      have := C.subsingleton_sheafH_puncturedTrait zbar hℓ hz q hq
      exact (C.sheafHUpperStarConstantZModEquiv zbar q).subsingleton
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end AlgebraicGeometry.Scheme.TransverseCorner
