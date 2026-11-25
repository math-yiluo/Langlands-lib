/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.CompletionFiniteExtensionTensorBijective

@[expose] public section
universe u v
open scoped TensorProduct
namespace AdicCompletion

-- The inherited statement binds an unused D; keep its signature unchanged.
set_option linter.unusedVariables false in
/-- The completed tensor product is nonempty as an algebra equivalence to the completed
localized finite algebra. Source: Stacks Project, Algebra, Lemma 10.97.8 (Tag 07N9), step 5.
(blueprint: lem-weil-pbc-completion-finite-extension-tensor)

The proof uses the completion-tensor equivalence for a finite module over a
Noetherian ring. Apply it after localizing `R` at `p` and identify the resulting
finite module tensor with `B = A ⊗[R] S` by tensor cancellation. The ideal induced
by `p` on `B` is the ideal used for the target completion, while the maximal ideal
of `A` induces the same adic filtration after localization. Naturality of the
completion map supplies the canonical algebra structure, and composing these two
identifications yields an `S`-algebra equivalence
`(C ⊗[R] S) ≃ₐ[S] AdicCompletion J B`; wrapping it in `Nonempty` gives the claim. -/
theorem completion_finite_extension_tensor
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    Nonempty ((C ⊗[R] S) ≃ₐ[S] AdicCompletion J B) := by
  intro A m C B J Q D
  clear D Q
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
  exact ⟨AlgEquiv.ofBijective (completionFiniteExtensionTensorMap R S p)
    (completion_finite_extension_tensor_bijective R S p)⟩
end AdicCompletion
