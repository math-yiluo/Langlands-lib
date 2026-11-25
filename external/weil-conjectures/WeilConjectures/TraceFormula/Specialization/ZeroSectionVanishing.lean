/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ZeroSectionAffine
public import WeilConjectures.TraceFormula.Specialization.ZeroSectionCartier

/-!

# Verdier's zero-section theorem: vanishing of the defect

For a separated `k`-scheme `X` of finite type, a closed subscheme `Z = V(I)` and a bounded
constructible `ℚ̄_ℓ`-complex `L` on `X`, the defect `C_{X,Z}(L)` of the specialization to the
normal cone vanishes, that is, the zero-section map
`ε_{X,Z}(L) : Le^* Sp_{X,Z}(L) ⟶ Ψ_{Z × S}(Li^* L)` is an isomorphism
(`ProEtale.CondensedRing.isZero_specializationDefect`,
`ProEtale.CondensedRing.isIso_zeroSectionMap`; blueprint
`theorem-verdier-s-theorem-specialization-zero--1`).

The proof follows the blueprint:
* replacing `L` by `j_! j^* L` does not change the defect, so we may assume `Li^* L = 0`
  (blueprint `lemma-base-change-cone-x-z`);
* blowing up `Z` reduces to the case of an effective Cartier divisor
  (`ProEtale.CondensedRing.nonempty_specializationDefect_iso_blowup`, blueprint
  `theorem-verdier-s-theorem-specialization-zero`);
* the assertion is local (`ProEtale.CondensedRing.isZero_specializationDefect_of_cover`), so we may
  assume that `X` is affine and `Z = V(h)` is principal
  (`ProEtale.CondensedRing.isZero_specializationDefect_of_isInvertible`);
* embedding `V(h) ⊆ X` into a coordinate hyperplane of an affine space reduces to the coordinate
  hyperplane (`ProEtale.CondensedRing.isZero_specializationDefect_ofIdealTop_span_singleton`,
  blueprint `theorem-verdier-s-theorem-specialization-zero`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The defect vanishes along an effective Cartier divisor** (proof of blueprint
`theorem-verdier-s-theorem-specialization-zero--1`): if `I` is invertible, then `C_{X,Z}(L) = 0`.
The assertion is local (`ProEtale.CondensedRing.isZero_specializationDefect_of_cover`), and on an
affine open where `I` is principal it is
`ProEtale.CondensedRing.isZero_specializationDefect_ofIdealTop_span_singleton`. -/
theorem isZero_specializationDefect_of_isInvertible (I : X.left.IdealSheafData)
    (hI : I.IsInvertible) (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  choose U hxU hU using hI
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X.left ↦ ((U x).1 : Set X.left))
    (fun x ↦ (U x).1.isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  refine isZero_specializationDefect_of_cover (ℓ := ℓ) I k' (ι := t)
    (fun a ↦ overRestrictι X (U a.1).1) ?_ L fun a ↦ ?_
  · refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    rw [range_overRestrictι]
    exact hy
  · obtain ⟨b, -, hb⟩ := hU a.1
    have h := IdealSheafData.comap_ι_eq_ofIdealTop_span_singleton I (U a.1) hb
    have : IsAffine (overRestrict X (U a.1).1).left := (U a.1).2
    change IsZero (specializationDefect (overRestrict X (U a.1).1) (I.comap (U a.1).1.ι) k' _ _)
    rw [h]
    exact isZero_specializationDefect_ofIdealTop_span_singleton k' _ _

variable (X) in
/-- **The zero-section map is invertible** (blueprint
`theorem-verdier-s-theorem-specialization-zero--1`, for `ℚ̄_ℓ`-coefficients): for every closed
subscheme `Z = V(I)` of `X` and every bounded constructible `L`, the defect `C_{X,Z}(L)`
vanishes. -/
theorem isZero_specializationDefect (I : X.left.IdealSheafData)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  refine isZero_specializationDefect_of_forall_isZero_upperStar (k' := k') X I (fun L₀ h₀ ↦ ?_) L
  have e₂ := (nonempty_specializationDefect_iso_blowup X I k' L₀ h₀).some
  have h₃ := isZero_specializationDefect_of_isInvertible k' _
    (isInvertible_comap_blowupOverHom X I)
    ((boundedConstructibleUpperStar _ ℓ (blowupOverHom X I)).obj L₀)
  exact (R(((centreSpecialFibreMap (blowupOverHom X I) I k').left)_*⟦
    Profinite.padicAlgClRingObj ℓ⟧).map_isZero h₃).of_iso e₂

variable (X) in
/-- **The zero-section map is invertible** (blueprint
`theorem-verdier-s-theorem-specialization-zero--1`, for `ℚ̄_ℓ`-coefficients):
`ε_{X,Z}(L) : Le^* Sp_{X,Z}(L) ⟶ Ψ_{Z × S}(Li^* L)` is an isomorphism. -/
theorem isIso_zeroSectionMap (I : X.left.IdealSheafData)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (zeroSectionMap X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) :=
  (isZero_specializationDefect_iff X I k' _ L.obj).mp
    (isZero_specializationDefect (ℓ := ℓ) k' X I L)

end AlgebraicGeometry.ProEtale.CondensedRing
