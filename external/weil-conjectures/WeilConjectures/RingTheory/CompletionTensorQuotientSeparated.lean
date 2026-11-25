/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Quotient projections separate a completed finite tensor

Source: Stacks Project, Algebra, Tags 0316, 05GG, 05GI, 00DF and 00IQ,
as applied to the comparison of Tag 07N9.
(blueprint: lem-weil-pbc-completion-tensor-quotient-separated)
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The quotient projections jointly detect zero in the completed tensor.
Source: Stacks Project, Algebra, Tags 0316, 05GG, 05GI, 00DF and 00IQ;
this is the separation step of the comparison in Tag 07N9.
(blueprint: lem-weil-pbc-completion-tensor-quotient-separated)

Proof: Put A = R_p, m = its maximal ideal, C = its m-adic completion and
T = C tensor_R S. A is Noetherian by localization, and C is Noetherian by Tag 0316.
Tags 05GG and 05GI make C local with maximal ideal mC. Base change makes T finite
as a C-module. Krull intersection (Tag 00IQ) therefore makes T separated for mC.
For each n, Tag 05GG identifies the kernel of C -> A/m^n with m^n C; explicitly,
the completion's module evaluation and ring evaluation differ by the canonical
identification of quotients, and the module evaluation has kernel m^n times C.
Right exactness of tensor product (Tag 00DF) identifies the kernel after tensoring
with S with the extension of m^n C to T. Since mC is the maximal ideal of C, this
is its nth power times T. Every displayed vanishing thus puts x in that submodule.
Krull intersection gives x = 0. No nontriviality hypothesis on S or T is needed. -/
theorem completion_tensor_quotient_separated
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    ∀ x : C ⊗[R] S,
      (∀ n : ℕ, Algebra.TensorProduct.map ((evalₐ m n).restrictScalars R)
        (AlgHom.id R S) x = 0) → x = 0 := by
  dsimp only
  let A := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal A
  let C := AdicCompletion m A
  let T := C ⊗[R] S
  have : IsNoetherianRing A := inferInstance
  have : IsNoetherianRing C := isNoetherianRing m
  have : IsLocalRing C := inferInstance
  have : Module.Finite C T := inferInstance
  intro x hx
  apply IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal C) T) x
  intro n
  have hker : RingHom.ker (evalₐ m n).toRingHom =
      (m ^ n).map (algebraMap A C) := by
    rw [← Submodule.restrictScalars_inj A]
    rw [← Ideal.smul_top_eq_map, pow_smul_top_eq_ker_eval m.fg_of_isNoetherianRing]
    ext a
    change evalₐ m n a = 0 ↔ eval m A n a = 0
    have h := factor_evalₐ_eq_eval m (n := n) a (by simp)
    have he := factor_eval_eq_evalₐ m (n := n) a (by simp)
    constructor
    · intro ha
      rw [ha, _root_.map_zero] at h
      exact h.symm
    · intro ha
      rw [ha, _root_.map_zero] at he
      exact he.symm
  have hmem : x ∈ ((IsLocalRing.maximalIdeal C) ^ n).map (algebraMap C T) := by
    have hz : x ∈ RingHom.ker
        (Algebra.TensorProduct.map ((evalₐ m n).restrictScalars R) (AlgHom.id R S)) :=
      hx n
    rw [Algebra.TensorProduct.rTensor_ker ((evalₐ m n).restrictScalars R)
      (surjective_evalₐ m n)] at hz
    change x ∈ (RingHom.ker (evalₐ m n).toRingHom).map
      (Algebra.TensorProduct.includeLeft : C →ₐ[R] T) at hz
    rw [hker] at hz
    rw [show IsLocalRing.maximalIdeal C = m.map (algebraMap A C) from
      maximalIdeal_eq_map]
    change x ∈ ((m.map (algebraMap A C)) ^ n).map
      (Algebra.TensorProduct.includeLeft : C →ₐ[R] T)
    simpa only [Ideal.map_pow] using hz
  rw [SModEq.zero, Ideal.smul_top_eq_map]
  exact hmem

end AdicCompletion
