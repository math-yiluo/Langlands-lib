/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Localization.Submodule

/-!
# Noetherian fibre rings

Source: Stacks Project, Algebra, Remark 00E6 and Lemma 00FN
(blueprint: lem-weil-pbc-fibre-ring-noetherian).

The fibre ring `B ⊗_A κ(p)` of the node is Mathlib's `p.Fiber B = κ(p) ⊗[A] B`
(the two tensor-factor orders are identified by `Algebra.TensorProduct.comm`).
-/

@[expose] public section

universe u v

namespace Ideal

/-- The fibre ring of a Noetherian algebra at any prime of the base is Noetherian.
Source: Stacks Project, Algebra, Remark 00E6 and Lemma 00FN
(blueprint: lem-weil-pbc-fibre-ring-noetherian).

Proof: Let `T` be the image of `A ∖ p` under the structure map and let `Bₚ = T⁻¹B`.
1. By lem-weil-pbc-fibre-ring-localization-quotient, the fibre is ring-isomorphic to
   `Bₚ / pBₚ`; the residue field is that of def-weil-pbc-localization-at-prime.
2. Since `p` is prime, its complement and hence `T` are multiplicative. By
   lem-weil-pbc-localization-noetherian, `Bₚ` is Noetherian because `B` is Noetherian
   (def-weil-pbc-noetherian-ring).
3. Compose the quotient map with the inverse of the isomorphism in step 1. This is a
   surjective ring map from `Bₚ` to the fibre. The fibre is therefore Noetherian by
   lem-weil-pbc-surjective-image-noetherian. -/
theorem isNoetherianRing_fiber
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] (p : Ideal A) [p.IsPrime] :
    IsNoetherianRing (p.Fiber B) := by
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let S := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  have : IsNoetherianRing S := inferInstance
  exact isNoetherianRing_of_ringEquiv _ (Fiber.algEquivQuotient (S := B) p).symm.toRingEquiv

end Ideal
