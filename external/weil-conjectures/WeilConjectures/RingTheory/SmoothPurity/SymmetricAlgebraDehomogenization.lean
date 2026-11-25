/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

set_option linter.privateModule false
/-! # Dehomogenizing a symmetric algebra

Source: Stacks Project, Constructions, Tags 01OA and 01NG.
(blueprint: lem-amb-symmetric-algebra-dehomogenization).
-/

@[expose] public section
set_option autoImplicit false
open scoped Pointwise
universe u v w
noncomputable section
namespace SymmetricAlgebra
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
variable {B : Type w} [CommRing B] [Algebra R B]
variable (e : SymmetricAlgebra R (R × M) ≃ₐ[R] B)
local notation "A" => B
variable (G : ℕ → Submodule R B) [GradedAlgebra G]
variable (hG : ∀ n, G n = (LinearMap.range (e.toLinearMap.comp (ι R (R × M)))) ^ n)
local notation "t" => e (ι R (R × M) (1, 0))
end SymmetricAlgebra
