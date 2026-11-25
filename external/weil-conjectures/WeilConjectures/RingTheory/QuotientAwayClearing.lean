/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Quotient localizations after clearing the difference of ideals

Source: Stacks Project, Algebra, Lemma 00SC (lemma-lci), proof of (2) implies (1).
-/
@[expose] public section
universe u v
namespace Ideal
/-- (blueprint: lem-weil-pbc-quotient-away-clearing)
Source: Stacks Project, Algebra, Lemma 00SC, proof of (2) implies (1).
For J contained in I and A I contained in J, the canonical quotient map becomes
an isomorphism after inverting A B. Indeed A is a unit there, so every element of
I already vanishes in the localization of R/J. This gives an inverse map from
R/I and then from its localization by the universal property. Both composites
fix the base ring, hence are identities by quotient and localization uniqueness.
This remains valid for B=0, when both localizations are the zero ring. -/
theorem nonempty_quotient_away_equiv_of_clearing
    {k : Type u} {R : Type v} [CommRing k] [CommRing R] [Algebra k R]
    (J I : Ideal R) (hJI : J ≤ I) (A B : R)
    (hclear : ∀ x ∈ I, A * x ∈ J) :
    Nonempty (Localization.Away (Ideal.Quotient.mk J (A * B)) ≃ₐ[k]
      Localization.Away (Ideal.Quotient.mk I (A * B))) := by
  let T := R ⧸ J
  let S := R ⧸ I
  let t : T := Ideal.Quotient.mk J (A * B)
  let s : S := Ideal.Quotient.mk I (A * B)
  let LT := Localization.Away t
  let LS := Localization.Away s
  let π : T →ₐ[k] S := Ideal.Quotient.factorₐ k hJI
  let toLS : T →ₐ[k] LS := (Algebra.algHom k S LS).comp π
  have ht : IsUnit (toLS t) := IsLocalization.Away.algebraMap_isUnit (S := LS) s
  let forward : LT →ₐ[k] LS := IsLocalization.Away.liftAlgHom t ht
  have hforward (x : T) : forward (algebraMap T LT x) = toLS x :=
    IsLocalization.Away.lift_eq t ht x
  let base : R →ₐ[k] LT := (Algebra.algHom k T LT).comp (Ideal.Quotient.mkₐ k J)
  have hA : IsUnit (base A) := by
    apply isUnit_of_mul_isUnit_left (y := base B)
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (S := LT) t
  have hI : ∀ x ∈ I, base x = 0 := by
    intro x hx
    apply hA.mul_left_cancel
    rw [mul_zero, ← map_mul]
    change algebraMap T LT (Ideal.Quotient.mk J (A * x)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hclear x hx), map_zero]
  let inverseBase : S →ₐ[k] LT := Ideal.Quotient.liftₐ I base hI
  have hinverseBase (x : R) : inverseBase (Ideal.Quotient.mk I x) = base x := rfl
  have hs : IsUnit (inverseBase s) :=
    IsLocalization.Away.algebraMap_isUnit (S := LT) t
  let backward : LS →ₐ[k] LT := IsLocalization.Away.liftAlgHom s hs
  have hbackward (x : S) : backward (algebraMap S LS x) = inverseBase x :=
    IsLocalization.Away.lift_eq s hs x
  have hleft : backward.comp forward = AlgHom.id k LT := by
    apply IsLocalization.algHom_ext (Submonoid.powers t)
    apply Ideal.Quotient.algHom_ext
    ext x
    change backward (forward (algebraMap T LT (Ideal.Quotient.mk J x))) = _
    rw [hforward]
    change backward (algebraMap S LS (Ideal.Quotient.mk I x)) = _
    rw [hbackward, hinverseBase]
    rfl
  have hright : forward.comp backward = AlgHom.id k LS := by
    apply IsLocalization.algHom_ext (Submonoid.powers s)
    apply Ideal.Quotient.algHom_ext
    ext x
    change forward (backward (algebraMap S LS (Ideal.Quotient.mk I x))) = _
    rw [hbackward, hinverseBase]
    change forward (algebraMap T LT (Ideal.Quotient.mk J x)) = _
    rw [hforward]
    rfl
  exact ⟨AlgEquiv.ofAlgHom forward backward hright hleft⟩
end Ideal
