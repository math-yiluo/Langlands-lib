/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Evaluation at zero on quotients of polynomial rings

`R[X] ⧸ (X) ⟶ R ⧸ J`, induced by evaluation at `0`, is natural in the pair `(R, J)`.

## Main results

- `Polynomial.quotientMap_comp_lift_evalRingHom_zero`: the naturality of `R[X] ⧸ (X) ⟶ R ⧸ J`.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

lemma span_X_le_ker_mk_comp_evalRingHom_zero (J : Ideal R) :
    Ideal.span {(X : R[X])} ≤ RingHom.ker ((Ideal.Quotient.mk J).comp (evalRingHom 0)) := by
  rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  simp

lemma quotientMap_comp_lift_evalRingHom_zero (φ : R →+* S) (J : Ideal R) (J' : Ideal S)
    (h : J ≤ J'.comap φ)
    (h' : Ideal.span {(X : R[X])} ≤ (Ideal.span {(X : S[X])}).comap (mapRingHom φ)) :
    (Ideal.quotientMap J' φ h).comp (Ideal.Quotient.lift _ _
      (fun _ ha ↦ span_X_le_ker_mk_comp_evalRingHom_zero J ha)) =
      (Ideal.Quotient.lift _ _ (fun _ ha ↦ span_X_le_ker_mk_comp_evalRingHom_zero J' ha)).comp
        (Ideal.quotientMap _ (mapRingHom φ) h') := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
  simp [eval_zero_map]

end Polynomial
