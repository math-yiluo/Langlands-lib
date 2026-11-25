/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Localization away from an idempotent, as a quotient

For an idempotent `e` of a commutative ring `R`, the quotient `R ⧸ (1 - e)` is the localization
of `R` away from `e` (`IsLocalization.Away.quotient_span_one_sub`), and this is compatible with
base change: `A ⊗[S] (R ⧸ (1 - e))` is the localization of `A ⊗[S] R` away from `1 ⊗ e`
(`IsLocalization.Away.tensor_quotient_span_one_sub`).

-/

@[expose] public section

open TensorProduct

namespace IsLocalization.Away

variable {R : Type*} [CommRing R] {e : R}

/-- The quotient by the ideal `(1 - e)` is the localization away from the idempotent `e`. -/
theorem quotient_span_one_sub (he : IsIdempotentElem e) :
    IsLocalization.Away e (R ⧸ Ideal.span {1 - e}) :=
  IsLocalization.away_of_isIdempotentElem he
    (by rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]) Ideal.Quotient.mk_surjective

/-- The quotient by the ideal `(1 - e)` is a finite module for an idempotent `e`, over any
ring of scalars. -/
theorem _root_.Module.Finite.quotient_span_one_sub (S : Type*) [CommRing S] [Algebra S R]
    [Module.Finite S R] : Module.Finite S (R ⧸ Ideal.span {1 - e}) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ S _).toLinearMap
    (Ideal.Quotient.mkₐ_surjective S _)

variable {S A : Type*} [CommRing S] [CommRing A] [Algebra S R] [Algebra S A]

/-- The `A ⊗[S] R`-algebra structure on `A ⊗[S] (R ⧸ (1 - e))` given by the base change of
the quotient map. -/
@[instance_reducible]
def tensorQuotientAlgebra : Algebra (A ⊗[S] R) (A ⊗[S] (R ⧸ Ideal.span {1 - e})) :=
  (Algebra.TensorProduct.map (AlgHom.id S A) (Ideal.Quotient.mkₐ S (Ideal.span {1 - e}))).toAlgebra

/-- Base change is compatible with localization away from an idempotent: `A ⊗[S] (R ⧸ (1 - e))`
is the localization of `A ⊗[S] R` away from `1 ⊗ e`, with respect to the base change of the
quotient map. -/
theorem tensor_quotient_span_one_sub (he : IsIdempotentElem e) :
    letI := tensorQuotientAlgebra (S := S) (A := A) (e := e)
    IsLocalization.Away (Algebra.TensorProduct.includeRight e : A ⊗[S] R)
      (A ⊗[S] (R ⧸ Ideal.span {1 - e})) := by
  let := tensorQuotientAlgebra (S := S) (A := A) (e := e)
  refine IsLocalization.away_of_isIdempotentElem (he.map _) ?_ ?_
  · rw [RingHom.algebraMap_toAlgebra]
    change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id S A)
      (Ideal.Quotient.mkₐ S (Ideal.span {1 - e}))) = _
    rw [Algebra.TensorProduct.lTensor_ker _ (Ideal.Quotient.mkₐ_surjective S _)]
    change Ideal.map _ (RingHom.ker (Ideal.Quotient.mk (Ideal.span {1 - e}))) = _
    rw [Ideal.mk_ker, Ideal.map_span, Set.image_singleton, map_sub, map_one]
  · exact Algebra.TensorProduct.map_surjective _ _ Function.surjective_id
      (Ideal.Quotient.mkₐ_surjective S _)

end IsLocalization.Away
