/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Trace.Basic

import Mathlib.RingTheory.Etale.Field

import WeilConjectures.Mathlib.RingTheory.Trace.Basic

/-! # Nondegenerate trace forms of finite algebras over fields

Source: Stacks Project, Tag 0BJF, finite-dimensional algebra argument.
(blueprint: lem-sbc-trace-form-nondegenerate-iff-etale-field)
-/

@[expose] public section

namespace Algebra

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
/-- A finite-dimensional commutative algebra over a field has nondegenerate trace form
exactly when it is etale.

Source: Stacks Project, Tag 0BJF, finite-dimensional fibre-algebra argument.
(blueprint: lem-sbc-trace-form-nondegenerate-iff-etale-field)

Proof: If a is nilpotent, multiplication by a times any b is a nilpotent endomorphism,
so its trace is zero. Nondegeneracy forces a = 0; the algebra is therefore reduced.
A finite-dimensional reduced algebra is an Artinian reduced ring, hence a finite
product of fields. Its algebra trace form is the orthogonal direct sum of the traces
on those fields: use block diagonal multiplication matrices in the concatenated
bases. Each field factor has nondegenerate trace form precisely when it is separable,
by the field trace criterion. Thus all factors are finite separable extensions,
equivalently the algebra is etale by Algebra.Etale.iff_exists_algEquiv_prod.
Conversely this product characterization of an etale algebra and nondegeneracy on
each finite separable factor imply nondegeneracy of the direct-sum trace form.
The zero algebra corresponds to an empty product; its trace form is nondegenerate
because its underlying module has only zero, and it is etale. -/
theorem traceForm_nondegenerate_iff_etale
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] :
    (traceForm K A).Nondegenerate ↔ Etale K A := by
  classical
  constructor
  · intro hn
    have : IsReduced A := (isReduced_iff A).mpr fun a ha ↦ hn.1 a fun b ↦ by
      rw [traceForm_apply]
      exact isNilpotent_iff_eq_zero.mp
        (isNilpotent_trace_of_isNilpotent ((Commute.all a b).isNilpotent_mul_right ha))
    have : IsArtinianRing A := .of_finite K A
    let e := (IsArtinianRing.equivPi A).restrictScalars K
    have hsep (i : MaximalSpectrum A) : Algebra.IsSeparable K (A ⧸ i.asIdeal) := by
      apply ((traceForm_nondegenerate_tfae K (A ⧸ i.asIdeal)).out 2 1).mp
      intro hz
      have hezero := hn.1 (e.symm (Pi.single i 1)) fun b ↦ by
        rw [traceForm_apply, ← trace_eq_of_algEquiv e]
        rw [map_mul, AlgEquiv.apply_symm_apply]
        have hmul : Pi.single i (1 : A ⧸ i.asIdeal) * e b =
            Pi.single i (e b i) := by
          ext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [hj]
        rw [hmul, trace_pi_single]
        simp [hz]
      have h := congrArg (fun a ↦ e a i) hezero
      simp at h
    exact (Etale.iff_exists_algEquiv_prod K A).mpr
      ⟨MaximalSpectrum A, inferInstance, fun i ↦ A ⧸ i.asIdeal,
        inferInstance, inferInstance, e, fun i ↦ ⟨inferInstance, hsep i⟩⟩
  · intro he
    let := he
    constructor
    · intro a ha
      by_contra h
      obtain ⟨b, hb⟩ := Etale.exists_trace_mul_ne_zero (K := K) h
      exact hb (by simpa [traceForm_apply] using ha b)
    · intro a ha
      by_contra h
      obtain ⟨b, hb⟩ := Etale.exists_trace_mul_ne_zero (K := K) h
      exact hb (by simpa [traceForm_apply, mul_comm] using ha b)

end Algebra
