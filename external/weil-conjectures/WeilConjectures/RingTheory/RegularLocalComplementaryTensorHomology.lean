/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! Tensor Koszul homology for a complementary regular quotient.
Source: Stacks Project, `intersection.tex`, Tag 0B1I.
(blueprint: new-d3-regular-local-complementary-tensor-homology)

The statement isolates the base-change step converting regularity of the images of a
parameter sequence in `A ⧸ J` into acyclicity of the tensor Koszul complex over `A`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTheory

/-- The tensor Koszul complex on a sequence whose images form a regular sequence in a
quotient has no positive homology.
Source: Stacks Project, `intersection.tex`, Tag 0B1I.
(blueprint: new-d3-regular-local-complementary-tensor-homology)

Proof: `A` acts on the `A`-module `A ⧸ J` through the quotient map, so the images of
`g` form a weakly regular sequence on the `A ⧸ J`-module `A ⧸ J` exactly when `g` is
weakly regular on `A ⧸ J` as an `A`-module (`isWeaklyRegular_map_algebraMap_iff`).
A regular sequence is weakly regular, and a weakly regular sequence on a module `M` is
`M`-Koszul-regular (`isKoszulRegularOn_of_isWeaklyRegular`,
lem-weil-pbc-regular-sequence-koszul-regular): the tensor Koszul complex
`K_•(g) ⊗[A] M` has zero homology in every nonzero degree. Take `M = A ⧸ J`.
-/
theorem regularLocal_complementary_tensor_homology_vanishing
    (A : Type u) [CommRing A] (r : ℕ) (J : Ideal A) (g : Fin r → A)
    [IsRegularLocalRing (A ⧸ J)]
    (hreg : RingTheory.Sequence.IsRegular (A ⧸ J)
      (List.ofFn (fun i ↦ Ideal.Quotient.mk J (g i)))) :
    ∀ n : ℕ, 0 < n →
      IsZero ((ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J)).homology n) := by
  intro n hn
  have hweak : RingTheory.Sequence.IsWeaklyRegular (A ⧸ J) (List.ofFn g) := by
    rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (A ⧸ J) (A ⧸ J)]
    simpa [List.map_ofFn, Function.comp_def] using hreg.toIsWeaklyRegular
  exact RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular (A ⧸ J) g hweak n
    (Nat.pos_iff_ne_zero.mp hn)

end RingTheory
