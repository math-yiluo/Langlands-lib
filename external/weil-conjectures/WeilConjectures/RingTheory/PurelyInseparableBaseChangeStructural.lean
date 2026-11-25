/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Noetherian.Basic
@[expose] public section
set_option autoImplicit false
universe u v w
open scoped TensorProduct
namespace Algebra.TensorProduct
/-- Finite free, flat, and Noetherian properties of tensor base change.
Source: Stacks Project, More on Algebra, proof of Proposition Tag 07E5, (3) => (1).
(blueprint: lem-weil-pbc-purely-inseparable-base-change-structural)

Proof: Extend the finite k-basis of k' to an A-basis of A tensor k' using
`Algebra.TensorProduct.basis`. A finite basis gives freeness and finite generation.
Free modules are flat, and a finite algebra over a Noetherian ring is Noetherian. -/
theorem purelyInseparable_baseChange_structural
    (k : Type u) (k' : Type v) (A : Type w)
    [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A]
    [IsPurelyInseparable k k'] [Module.Finite k k']
    [IsLocalRing A] [IsNoetherianRing A] :
    Nonempty (Module.Basis (Fin (Module.finrank k k')) A (A ⊗[k] k')) ∧
      Module.Free A (A ⊗[k] k') ∧ Module.Finite A (A ⊗[k] k') ∧
      RingHom.Flat (algebraMap A (A ⊗[k] k')) ∧ IsNoetherianRing (A ⊗[k] k') := by
  let b := Algebra.TensorProduct.basis A (Module.finBasis k k')
  have : Module.Free A (A ⊗[k] k') := Module.Free.of_basis b
  have : Module.Finite A (A ⊗[k] k') := Module.Finite.of_basis b
  exact ⟨⟨b⟩, inferInstance, inferInstance,
    RingHom.flat_algebraMap_iff.mpr inferInstance,
    IsNoetherianRing.of_finite A (A ⊗[k] k')⟩
end Algebra.TensorProduct
