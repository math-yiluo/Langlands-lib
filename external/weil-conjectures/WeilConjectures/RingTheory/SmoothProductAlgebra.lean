/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.Algebra.Prod

import Mathlib.RingTheory.Smooth.Pi
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.Algebra.Ring.Fin

/-!
# A product of two smooth algebras over one base is smooth

Source: Stacks Project, Algebra, Lemma Tag 0GIF (lemma-product-smooth), the forward construction
from smooth factors (blueprint: lem-weil-pbc-smooth-product-algebra).
-/

@[expose] public section

universe u v w

namespace Algebra.Smooth

/-- A binary product of smooth `R`-algebras, equipped with `Prod.algebra`, is smooth over `R`.
Source: Stacks Project, Algebra, Lemma Tag 0GIF (lemma-product-smooth), the implication from
smooth factors to a smooth product (blueprint: lem-weil-pbc-smooth-product-algebra).

Proof following the hint in 0GIF, expanded in the node:
1. In `S' × S''`, the idempotents `e₁ = (1, 0)` and `e₂ = (0, 1)` sum to one. The projections
   are surjective `R`-algebra maps, with kernels `e₂ S` and `e₁ S`, respectively.
2. By lem-weil-pbc-fg-idempotent-ideal-idempotent-generator (2), localization at `e₁` is
   isomorphic to `S'`, and localization at `e₂` to `S''`. These are `R`-algebra isomorphisms:
   each projection sends the image of `r` to its given image in the corresponding factor.
3. By lem-weil-pbc-smooth-ring-map-isomorphism-invariant, smoothness of the factors transfers
   to these two localizations (def-weil-pbc-smooth-ring-map).
4. Since the idempotents generate the unit ideal, lem-weil-pbc-smooth-ring-map-local-on-cover
   gives smoothness of the product. This implements the hints using Tags 00TC and 00ED. -/
theorem prod (R : Type u) (S' : Type v) (S'' : Type w)
    [CommRing R] [CommRing S'] [CommRing S''] [Algebra R S'] [Algebra R S'']
    [Smooth R S'] [Smooth R S''] : Smooth R (S' × S'') := by
  let A : Fin 2 → Type (max v w)
    | ⟨0, _⟩ => ULift.{w} S'
    | ⟨1, _⟩ => ULift.{v} S''
  let : (i : Fin 2) → CommRing (A i)
    | ⟨0, _⟩ => inferInstance
    | ⟨1, _⟩ => inferInstance
  let : (i : Fin 2) → Algebra R (A i)
    | ⟨0, _⟩ => inferInstance
    | ⟨1, _⟩ => inferInstance
  have : (i : Fin 2) → Smooth R (A i)
    | ⟨0, _⟩ => Smooth.of_equiv (ULift.algEquiv (R := R)).symm
    | ⟨1, _⟩ => Smooth.of_equiv (ULift.algEquiv (R := R)).symm
  have : Smooth R ((i : Fin 2) → A i) := {}
  let e : ((i : Fin 2) → A i) ≃ₐ[R] A 0 × A 1 :=
    { RingEquiv.piFinTwo A with commutes' := fun _ ↦ rfl }
  have : Smooth R (ULift.{w} S' × ULift.{v} S'') := Smooth.of_equiv e
  exact Smooth.of_equiv (AlgEquiv.prodCongr
    (ULift.algEquiv (R := R)) (ULift.algEquiv (R := R)))

end Algebra.Smooth
