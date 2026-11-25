/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Adjoining a root of a monic polynomial is faithfully flat

For a monic polynomial `f : R[X]` of nonzero degree, `R[X]/(f)` is a free `R`-module with basis
`1, X, …, X^(deg f - 1)`, hence faithfully flat over `R`.

## Main results

- `AdjoinRoot.faithfullyFlat_of_monic`: `R[X]/(f)` is faithfully flat over `R` for `f` monic of
  nonzero degree.
- `Module.Flat.of_flat_of_faithfullyFlat`: flatness over `A` descends along a faithfully flat
  `B`-algebra `C`.
-/

@[expose] public section

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R]

/-- For a monic polynomial `f` of nonzero degree, `R[X]/(f)` is faithfully flat over `R`: it is
free with basis `1, X, …, X^(deg f - 1)`, and nonzero when `R` is. -/
theorem faithfullyFlat_of_monic {f : R[X]} (hf : f.Monic) (hdeg : f.degree ≠ 0) :
    Module.FaithfullyFlat R (AdjoinRoot f) := by
  let pb := powerBasis' hf
  have := Module.Free.of_basis pb.basis
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨fun m hm ↦ (hm.ne_top (Subsingleton.elim _ _)).elim⟩
  have hdim : 0 < pb.dim := by
    rw [degree_eq_natDegree hf.ne_zero] at hdeg
    simpa [pb] using Nat.pos_of_ne_zero (by exact_mod_cast hdeg)
  have : Nontrivial (AdjoinRoot f) :=
    nontrivial_of_ne _ 0 (pb.basis.linearIndependent.ne_zero ⟨0, hdim⟩)
  infer_instance

end AdjoinRoot

namespace Module.Flat

/-- **Flatness descends along faithfully flat algebras.** If `C` is faithfully flat over `B` and
flat over `A`, then `B` is flat over `A`: for an injection `N ⟶ P` of `A`-modules, the map
`B ⊗ N ⟶ B ⊗ P` becomes, after `C ⊗_B -`, the injective map `C ⊗ N ⟶ C ⊗ P`.
(blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem of_flat_of_faithfullyFlat {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat B C] [Module.Flat A C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  change Function.Injective (f.baseChange B)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective B C]
  have : ⇑((f.baseChange B).lTensor C) =
      ⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C P).symm ∘
        ⇑(f.lTensor C) ∘ ⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C N) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul c y =>
      induction y using TensorProduct.inductionOn with
      | tmul b n =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
        rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add y z hy hz => simp_all [TensorProduct.tmul_add]
    | add x y hx hy => simp_all
  rw [this]
  exact (LinearEquiv.injective _).comp
    ((Module.Flat.lTensor_preserves_injective_linearMap f hf).comp (LinearEquiv.injective _))

end Module.Flat

/-! ### Ported from the `proetale` package
(`Proetale.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`) -/

open TensorProduct

lemma Module.FaithfullyFlat.of_nontrivial_tensor_quotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (H : ∀ (m : Ideal R), m.IsMaximal → Nontrivial ((R ⧸ m) ⊗[R] M)) :
    Module.FaithfullyFlat R M where
  submodule_ne_top m hm := by
    rw [ne_eq, ← Submodule.Quotient.subsingleton_iff, not_subsingleton_iff_nontrivial,
      (TensorProduct.quotTensorEquivQuotSMul M m).symm.toEquiv.nontrivial_congr]
    exact H m hm
