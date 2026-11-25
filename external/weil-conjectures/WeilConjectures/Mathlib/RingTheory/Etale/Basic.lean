/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Unramified.Field

/-!
# Tensor products of étale algebras, and reducedness

The tensor product of two étale `R`-algebras is étale over `R`, and an étale algebra over a
domain is reduced.

## Main statements

- `Algebra.Etale.tensorProduct`: the tensor product of two étale algebras is étale.
- `Algebra.Etale.isReduced_of_isDomain`: an étale algebra over a domain is reduced.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.Etale

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The tensor product of two étale `R`-algebras is étale over `R`: it is a base change of
`B` to `A`, followed by `R → A`. -/
instance tensorProduct [Etale R A] [Etale R B] : Etale R (A ⊗[R] B) :=
  comp R A (A ⊗[R] B)

variable (R A) in
/-- An étale algebra `A` over a domain `R` is reduced. Since `A` is flat over `R`, it embeds
into its generic fibre `Frac(R) ⊗[R] A`, which is unramified and of finite type over the field
`Frac(R)`, hence reduced. This is a special case of [Stacks 033B]. -/
theorem isReduced_of_isDomain [IsDomain R] [Etale R A] : IsReduced A := by
  let L := FractionRing R
  have hinj : Function.Injective (TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R L)
      (IsFractionRing.injective R L)
    intro a b hab
    have := @h (1 ⊗ₜ a) (1 ⊗ₜ b) (by simpa using hab)
    simpa using congrArg (_root_.TensorProduct.lid R A) this
  have : IsReduced (L ⊗[R] A) := FormallyUnramified.isReduced_of_field L _
  exact isReduced_of_injective _ hinj

end Algebra.Etale
