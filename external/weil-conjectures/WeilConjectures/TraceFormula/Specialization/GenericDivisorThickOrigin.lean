/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ThickOrigin
public import WeilConjectures.TraceFormula.Specialization.ThickOriginPowUnit

/-!

# The constant case of generic vanishing along a smooth pulled-back thick origin

Let `f : X ⟶ 𝔸¹_k` be smooth and `Z = f⁻¹ V(x^m)`. By the smooth exchange for the defect and the
thick origin (blueprint `lemma-case-z-v-x-m--1`), the defect `C_{X,Z}(ℚ̄_ℓ)` of the constant complex
vanishes, and so does `C_{X,Z}(j_! ℚ̄_ℓ)` for the complement `j : X ∖ Z ⟶ X`
(`ProEtale.CondensedRing.isZero_specializationDefect_lowerShriek_unit_of_smooth`). This is the
argument of blueprint `lemma-vanishing-generic-points-principal-divisor` once `X` has been shrunk
around a generic point of the divisor so that `Z = h⁻¹ V(x^m)` for a smooth `h : X ⟶ 𝔸¹`.

## The thick origin

`ProEtale.CondensedRing.isZero_specializationDefect_polyAffineThickOrigin_unit_padicAlgCl` is the
node `lemma-case-z-v-x-m--1`, for `ℚ̄_ℓ`-coefficients. `ThickOrigin.lean` reduces it to the
invertibility of the restricted specialization unit of the deformation, which is
`ProEtale.CondensedRing.isIso_upperStar_zeroSection_unit_polyAffineThickOrigin`
(`ThickOriginPowUnit.lean`, through the power map `t ↦ t^m` and the proper exchange).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **The thick origin** (blueprint `lemma-case-z-v-x-m--1`, a node of the subsection
`lemma-case-z-v-x-m`, for `ℚ̄_ℓ`-coefficients): for `m ≥ 1`, the defect
`C_{𝔸¹, V(x^m)}(ℚ̄_ℓ)` of the constant complex vanishes. -/
theorem isZero_specializationDefect_polyAffineThickOrigin_unit_padicAlgCl {m : ℕ} (hm : 0 < m) :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
      (Profinite.padicAlgClRingObj ℓ) (𝟙_ _)) := by
  have := isIso_upperStar_zeroSection_unit_polyAffineThickOrigin (ℓ := ℓ) k k' hm.ne'
  exact isZero_specializationDefect_polyAffineThickOrigin_unit _ k' hm

/-- **Generic vanishing for constant coefficients along a smooth pulled-back thick origin**
(the argument of blueprint `lemma-vanishing-generic-points-principal-divisor`): for `f : X ⟶ 𝔸¹_k`
smooth, `Z = f⁻¹ V(x^m)` with `m ≥ 1`, and the complement `j : X ∖ Z ⟶ X`, the defect
`C_{X,Z}(j_! ℚ̄_ℓ)` vanishes. -/
theorem isZero_specializationDefect_lowerShriek_unit_of_smooth {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (f : X ⟶ polyAffine k 1) [Smooth f.left] {m : ℕ} (hm : 0 < m) :
    IsZero (specializationDefect X ((polyAffineThickOrigin k m).comap f.left) k'
      (Profinite.padicAlgClRingObj ℓ)
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X ((polyAffineThickOrigin k m).comap f.left).support.compl)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X ((polyAffineThickOrigin k m).comap f.left).support.compl)).obj
            (𝟙_ _))).obj) :=
  isZero_specializationDefect_lowerShriek_unit k' _
    (isZero_specializationDefect_unit_of_smooth k' f _
      (isZero_specializationDefect_polyAffineThickOrigin_unit_padicAlgCl k' hm))

end AlgebraicGeometry.ProEtale.CondensedRing
