/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Flatness descends through a faithfully flat module

Let `R → S` be a ring map and `M` an `S`-module. If `M` is flat over `R` and faithfully flat
over `S`, then `S` is flat over `R` (Stacks, Lemma 039V).

## Main results

- `Module.Flat.of_flat_of_faithfullyFlat_module`

## References

- Stacks Project, Lemma 10.39.10, <https://stacks.math.columbia.edu/tag/039V>
-/

@[expose] public section

open TensorProduct

namespace Module.Flat

/-- Let `R → S` be a ring map and `M` an `S`-module. If `M` is flat as an `R`-module and
faithfully flat as an `S`-module, then `S` is flat over `R`.
(blueprint: `lem-weil-pbc-flat-permanence`) -/
theorem of_flat_of_faithfullyFlat_module (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Flat R M]
    [Module.FaithfullyFlat S M] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  rw [← LinearMap.baseChange_eq_lTensor,
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective S M]
  have h' : (LinearMap.lTensor M (f.baseChange S) : _ → _) =
      (AlgebraTensorModule.cancelBaseChange R S S M P).symm ∘
        LinearMap.lTensor M f ∘ AlgebraTensorModule.cancelBaseChange R S S M N := by
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp_all
    | tmul m y =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp_all [TensorProduct.tmul_add]
      | tmul s n =>
        apply (AlgebraTensorModule.cancelBaseChange R S S M P).injective
        simp
  rw [h']
  exact (LinearEquiv.injective _).comp
    ((Module.Flat.lTensor_preserves_injective_linearMap f hf).comp (LinearEquiv.injective _))

end Module.Flat
