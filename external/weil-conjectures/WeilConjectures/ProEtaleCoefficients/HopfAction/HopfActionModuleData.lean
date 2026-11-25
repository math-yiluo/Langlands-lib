/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Affine Hopf action module data

Source: Stacks, Tag 03LF, affine form of the identity and cocycle diagrams.
The target pullback is identified with M tensor_k C. The source uses the algebra
structure induced by rho, rather than the usual inclusion of E into E tensor_k C.
For composable arrows the coordinate ring is E tensor_k C tensor_k C, with maps
p_a(e tensor c)=e tensor c tensor 1, p_b(e tensor c)=rho(e) tensor c, and
p_ab(e tensor c)=e tensor Delta(c). Pullbacks are linear maps on actual balanced scalar
extensions, characterized on
all finite presentations of the image of each generator. Identity and cocycle are
equalities of these pullbacks, with all extension transports normalized on generators.
They are not defined as counitality and coassociativity of the generator map.
(blueprint: def-sfb-hopf-action-module-data)
-/

set_option autoImplicit false

@[expose] public section

universe u v w z z₂ t

open TensorProduct
open scoped TensorProduct

namespace HopfAction

variable (k : Type u) [Field k] (C : Type v) [CommRing C] [HopfAlgebra k C]
variable (E : Type w) [CommRing E] [Algebra k E]
variable (M : Type z) [AddCommGroup M] [Module E M] [Module k M]
variable [IsScalarTower k E M]

/-- Scalar extension to an arbitrary coordinate algebra along a specified map.
Source: Stacks Tag 03LF, pullbacks. (blueprint: def-sfb-hopf-action-module-data) -/
abbrev ScalarExtension (A : Type t) [CommRing A] [Algebra k A] (r : E →ₐ[k] A) :=
  letI := r.toRingHom.toAlgebra
  letI : Module E A := r.toRingHom.toAlgebra.toModule
  A ⊗[E] M

end HopfAction
