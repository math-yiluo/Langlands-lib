/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# Square Jacobian presentations

A square Jacobian presentation of an `R`-algebra `S` is a presentation
`S = R[x₁, …, xₘ] / (f₁, …, fₘ)` with as many relations as variables, whose Jacobian
determinant `det (∂fᵢ / ∂xⱼ)` is a unit in `S`. It is a submersive presentation whose
relations and variables are indexed by the same type, the relation `fᵢ` being paired with the
variable `xᵢ`.

## Main definitions

- `Algebra.SquareJacobianPresentation`: a square Jacobian presentation.
-/

@[expose] public section

universe t u v

namespace Algebra

variable (R : Type u) (S : Type v) (ι : Type t) [CommRing R] [CommRing S] [Algebra R S]
  [Finite ι]

/-- A square Jacobian presentation of the `R`-algebra `S` (blueprint
`proposition-extension-zero-restriction-closed-subscheme`): a presentation
`S = R[xᵢ : i ∈ ι] / (fᵢ : i ∈ ι)` such that the full Jacobian determinant `det (∂fᵢ / ∂xⱼ)` is a
unit in `S`. It is recorded as a submersive presentation with relations indexed by `ι` whose
relation `fᵢ` is paired with the variable `xᵢ`, so that the Jacobian of the submersive presentation
is the full Jacobian determinant. -/
structure SquareJacobianPresentation extends SubmersivePresentation.{t, t} R S ι ι where
  map_eq_id : map = _root_.id

end Algebra
