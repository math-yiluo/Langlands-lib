/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import WeilConjectures.RepresentationTheory.PiTensorProduct

/-!
# Tensor powers of a representation

The `n`-th tensor power `ρ^{⊗ n}` of a representation `ρ` on `V` is the representation on
`⨂[k]^n V` with `g (v₁ ⊗ ⋯ ⊗ vₙ) = g v₁ ⊗ ⋯ ⊗ g vₙ`. This file defines it and identifies
`ρ^{⊗ 1}` with `ρ` and `ρ^{⊗ (n + 1)}` with `ρ^{⊗ n} ⊗ ρ`.

## Main definitions

- `Representation.tensorPower`: the tensor power `ρ^{⊗ n}`.
- `Representation.tensorPowerOneEquiv`: `ρ^{⊗ 1} ≅ ρ`.
- `Representation.tensorPowerSuccEquiv`: `ρ^{⊗ (n + 1)} ≅ ρ^{⊗ n} ⊗ ρ`.
-/

@[expose] public section

open PiTensorProduct

open scoped TensorProduct

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

/-- The `n`-th tensor power `ρ^{⊗ n}` of a representation, on `⨂[k]^n V`, with
`g (v₁ ⊗ ⋯ ⊗ vₙ) = g v₁ ⊗ ⋯ ⊗ g vₙ`: the tensor product of the constant family `ρ`. -/
noncomputable abbrev tensorPower (n : ℕ) : Representation k G (⨂[k]^n V) :=
  piTprod fun _ : Fin n ↦ ρ

theorem tensorPower_apply_tprod (n : ℕ) (g : G) (v : Fin n → V) :
    ρ.tensorPower n g (PiTensorProduct.tprod k v) = PiTensorProduct.tprod k fun i ↦ ρ g (v i) :=
  piTprod_apply_tprod _ _ _

/-- The first tensor power `ρ^{⊗ 1}` is `ρ`. -/
noncomputable def tensorPowerOneEquiv : (ρ.tensorPower 1).Equiv ρ :=
  .mk (subsingletonEquiv 0) fun g ↦ by
    ext v
    simp

/-- The tensor power `ρ^{⊗ (n + 1)}` is `ρ^{⊗ n} ⊗ ρ`. -/
noncomputable def tensorPowerSuccEquiv (n : ℕ) :
    (ρ.tensorPower (n + 1)).Equiv ((ρ.tensorPower n).tprod ρ) :=
  piTprodSuccEquiv fun _ : Fin (n + 1) ↦ ρ

end Representation
