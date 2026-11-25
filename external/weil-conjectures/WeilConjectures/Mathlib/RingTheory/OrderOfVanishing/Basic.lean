/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Invariance of the order of vanishing under ring isomorphisms

- `Ring.ord_ringEquiv`: `ord_{R'}(e x) = ord_R x` for a ring isomorphism `e : R ≃+* R'`.
- `Ring.ordFrac_ringEquiv`: the same for the extension `ordFrac` to fraction fields, along a
  compatible isomorphism of the fraction fields.
-/

@[expose] public section

namespace Ring

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- The order of vanishing is invariant under ring isomorphisms. -/
theorem ord_ringEquiv (e : R ≃+* R') (x : R) : ord R' (e x) = ord R x := by
  have : RingHomSurjective (e : R →+* R') := ⟨e.surjective⟩
  let q : R ⧸ Ideal.span {x} ≃+* R' ⧸ Ideal.span {e x} :=
    Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  let f : R ⧸ Ideal.span {x} →ₛₗ[(e : R →+* R')] R' ⧸ Ideal.span {e x} :=
    { toFun := q
      map_add' := map_add q
      map_smul' := fun r y ↦ by
        induction y using Submodule.Quotient.induction_on with
        | H z =>
        change q (Ideal.Quotient.mk _ (r * z)) = e r • q (Ideal.Quotient.mk _ z)
        rw [map_mul, Algebra.smul_def]
        simp [q] }
  rw [ord, ord, Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f q.bijective)]

variable [Nontrivial R] [Nontrivial R']

/-- `ordMonoidWithZeroHom` is invariant under ring isomorphisms. -/
theorem ordMonoidWithZeroHom_ringEquiv (e : R ≃+* R') (x : R) :
    ordMonoidWithZeroHom R' (e x) = ordMonoidWithZeroHom R x := by
  by_cases hx : x ∈ nonZeroDivisors R
  · have hx' : e x ∈ nonZeroDivisors R' := by
      rw [← MulEquivClass.map_nonZeroDivisors e]
      exact ⟨x, hx, rfl⟩
    rw [ordMonoidWithZeroHom_eq_ord hx, ordMonoidWithZeroHom_eq_ord hx', ord_ringEquiv]
  · have hx' : e x ∉ nonZeroDivisors R' := by
      rw [← MulEquivClass.map_nonZeroDivisors e]
      rintro ⟨y, hy, hyx⟩
      exact hx (e.injective hyx ▸ hy)
    rw [ordMonoidWithZeroHom_eq_zero hx, ordMonoidWithZeroHom_eq_zero hx']

variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsNoetherianRing R'] [Ring.KrullDimLE 1 R']
variable {K K' : Type*} [Field K] [Field K'] [Algebra R K] [Algebra R' K'] [IsFractionRing R K]
  [IsFractionRing R' K']

/-- `ordFrac` is invariant under compatible isomorphisms of rings and fraction fields. -/
theorem ordFrac_ringEquiv (e : R ≃+* R') (E : K ≃+* K')
    (h : ∀ r, E (algebraMap R K r) = algebraMap R' K' (e r)) (f : K) :
    ordFrac R' (E f) = ordFrac R f := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have key (r : R) : ordFrac R' (algebraMap R' K' (e r)) = ordFrac R (algebraMap R K r) := by
    by_cases hr : r = 0
    · simp [hr]
    rw [ordFrac_eq_ord _ hr, ordFrac_eq_ord _ (e.map_ne_zero_iff.2 hr),
      ordMonoidWithZeroHom_ringEquiv]
  rw [map_div₀, h, h, map_div₀, map_div₀, key, key]

end Ring
