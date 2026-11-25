/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.SepClosedPoint
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerRestriction
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerVanishingDevissage

/-!
# Vanishing at the transverse corner

Let `C` be a transverse corner over an algebraically closed field `k`
(`AlgebraicGeometry.Scheme.TransverseCorner`), `ℓ` a prime invertible in `k`, `Λ` a finite
commutative `ℓ`-primary ring and `E` a bounded complex of `Λ`-modules on `Z - (X ∪ Y)` with
finite locally constant cohomology whose monodromy factors through a finite `ℓ`-group. Then the
stalk of `M = Rj_* i_! E` at the corner point vanishes:

`(Rj_* i_! E)_z ≅ RΓ(S - Y_S, i_! E) = 0` in `D(Λ)`

(blueprint `lemma-cohomology-near-two-transverse-divisors--1`).

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.isZero_leftDerivedUpperStar_boundaryComplex`: the
  stalk `M_z̄` of `M = Rj_* i_! E` at a geometric point `z̄` over the corner point is zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] [IsAlgClosed k] (C : TransverseCorner k) {ℓ : ℕ} [Fact ℓ.Prime]
  (hℓ : (ℓ : k) ≠ 0) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)

include hℓ hΛ in
/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`: Vanishing at the transverse
corner. For a bounded complex `E` on `Z - (X ∪ Y)` with finite locally constant cohomology whose
monodromy factors through a finite `ℓ`-group, the stalk of `M = Rj_* i_! E` at a geometric point
`z̄` over the corner point vanishes: `M_z̄ ≅ RΓ(S - Y_S, i_! E) = 0` in `D(Λ)`. -/
theorem isZero_leftDerivedUpperStar_boundaryComplex
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : Etale.IsBoundedFiniteEllGroupMonodromy ℓ E) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (zbar : Spec (.of Ω) ⟶ C.Z) (hz : Set.range zbar = {C.z}) :
    IsZero ((L((zbar)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E)) := by
  let a : Spec (.of (AlgebraicClosure Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
  refine Etale.isZero_leftDerivedUpperStar_of_isZero_comp a zbar _ ?_
  have hz' : Set.range (a ≫ zbar) = {C.z} := by
    rw [← hz]
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨a x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      rw [Scheme.Hom.comp_apply, Subsingleton.elim (a _) x]
  exact C.isZero_leftDerivedUpperStar_boundaryComplex_of_bijective Λ (a ≫ zbar) hΛ
    (C.bijective_cohomologyMap_puncturedTraitι (a ≫ zbar) hℓ hz') E hE

end AlgebraicGeometry.Scheme.TransverseCorner
