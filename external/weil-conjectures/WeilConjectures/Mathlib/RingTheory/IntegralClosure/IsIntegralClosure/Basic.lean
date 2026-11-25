/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral algebras over a field with a rational point

- `RingHom.IsIntegral.isNilpotent_of_eq_zero`: let `A` be integral over a field `K`, with no
  idempotents other than `0` and `1`, and let `φ : A → K` be a retraction of `K → A`. Then every
  element of the kernel of `φ` is nilpotent; that is, `A` is local with nil maximal ideal `ker φ`.
-/

@[expose] public section

open Polynomial

/-- Let `g : K → A` be an integral ring homomorphism from a field, such that `A` has no
idempotents other than `0` and `1`, and let `φ : A → K` be a retraction of `g`. Then every element
of the kernel of `φ` is nilpotent.

Indeed, if `a` is a root of the monic polynomial `X ^ m * q` with `q(0) ≠ 0`, then `X ^ m` and `q`
are coprime, say `u X ^ m + v q = 1`, and `v(a) q(a)` is an idempotent. It is not `0`, since
`a ^ m` is not a unit, so it is `1`, which forces `a ^ m = 0`. -/
theorem RingHom.IsIntegral.isNilpotent_of_eq_zero {K A : Type*} [Field K] [CommRing A]
    {g : K →+* A} (hg : g.IsIntegral) (φ : A →+* K) (hφ : φ.comp g = RingHom.id K)
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) {a : A} (ha : φ a = 0) :
    IsNilpotent a := by
  obtain ⟨p, hpm, hp⟩ := hg a
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hpm.ne_zero 0
  set m := p.rootMultiplicity 0
  have hm : 0 < m := by
    refine (rootMultiplicity_pos hpm.ne_zero).mpr ?_
    have := congrArg φ hp
    rwa [hom_eval₂, hφ, ha, map_zero, ← eval] at this
  simp only [map_zero, sub_zero] at hpq hq
  obtain ⟨u, v, huv⟩ := (irreducible_X.coprime_iff_not_dvd.mpr hq).pow_left (m := m)
  let ev := eval₂RingHom g a
  have h1 : ev u * a ^ m + ev v * ev q = 1 := by
    simpa [ev] using congrArg ev huv
  have h0 : a ^ m * ev q = 0 := by
    simpa [ev, hpq] using hp
  rcases hA (ev v * ev q) (by
      rw [IsIdempotentElem]
      linear_combination (ev v * ev q) * h1 - ev v * ev u * h0) with he | he
  · rw [he, add_zero] at h1
    have := congrArg φ h1
    simp [ha, hm.ne'] at this
  · exact ⟨m, by linear_combination (ev v) * h0 - a ^ m * he⟩
