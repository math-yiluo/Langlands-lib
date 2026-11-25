/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Module base change across a ring tensor equivalence
Source: Stacks Project, Algebra, Tag 00R1, the final displayed isomorphisms.
(blueprint: lem-weil-pbc-module-base-change-across-pushout).
-/

@[expose] public section

universe u v
open scoped TensorProduct

namespace TensorProduct

/-- A canonical ring tensor equivalence allows module base change over the smaller ring.
Source: Stacks Project, Algebra, Tag 00R1, the second final displayed isomorphism.
(blueprint: lem-weil-pbc-module-base-change-across-pushout)

Proof:
Give N its A-module structure through f and M its R-module structure through R → S.
The given ring
isomorphism identifies B tensor_A R with S as a B-module and as an R-module:
check the scalar identities on pure tensors, using its prescribed formula.
Tensor cancellation identifies N tensor_B (B tensor_A R) with N tensor_A R.
Invert this equivalence, tensor the ring equivalence with N, and apply the assumed
module base-change equivalence, swapping tensor factors as necessary. Each map
is R-linear. On y tensor x the composite is x tensor (1 tensor y), then x tensor
algebraMap R S y, then algebraMap R S y times q x. This proves both bijectivity
and the asserted formula, including zero modules and zero rings.
-/
theorem moduleBaseChangeAcrossPushout
    (A B R S : Type u) (N M : Type v)
    [CommRing A] [CommRing B] [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module B N] [AddCommGroup M] [Module S M]
    (f : A →+* B) (g : A →+* R) (k : B →+* S) (q : N →+ M)
    (hring : letI := f.toAlgebra; letI := g.toAlgebra
      ∃ e : B ⊗[A] R ≃+* S,
        ∀ (x : B) (y : R), e (x ⊗ₜ[A] y) = k x * algebraMap R S y)
    (hmodule : letI := k.toAlgebra
      ∃ e : S ⊗[B] N ≃ₗ[S] M,
        ∀ (y : S) (x : N), e (y ⊗ₜ[B] x) = y • q x) :
    letI := g.toAlgebra
    letI : Module A N := Module.compHom N f
    letI : Module R M := Module.compHom M (algebraMap R S)
    ∃ e : R ⊗[A] N ≃ₗ[R] M,
      ∀ (y : R) (x : N), e (y ⊗ₜ[A] x) = algebraMap R S y • q x := by
  classical
  let := f.toAlgebra
  let := g.toAlgebra
  let := k.toAlgebra
  let : Module A N := Module.compHom N f
  let : IsScalarTower A B N := IsScalarTower.of_compHom A B N
  let : Module B M := Module.compHom M k
  let : IsScalarTower B S M := IsScalarTower.of_compHom B S M
  let : Module R M := Module.compHom M (algebraMap R S)
  obtain ⟨er, her⟩ := hring
  obtain ⟨em, hem⟩ := hmodule
  let β : B ⊗[A] R ≃ₗ[B] S :=
    { er.toAddEquiv with
      map_smul' := fun b t ↦ by
        change er (b • t) = b • er t
        rw [_root_.Algebra.smul_def, _root_.Algebra.smul_def, map_mul]
        congr 1
        change er (b ⊗ₜ[A] (1 : R)) = k b
        rw [her, map_one, mul_one] }
  let c : N ⊗[A] R ≃ₗ[B] M :=
    (AlgebraTensorModule.cancelBaseChange A B B N R).symm.trans
      ((TensorProduct.congr (LinearEquiv.refl B N) β).trans
        ((TensorProduct.comm B N S).trans (em.restrictScalars B)))
  let eadd : R ⊗[A] N ≃+ M :=
    (TensorProduct.comm A R N).toAddEquiv.trans c.toAddEquiv
  have eadd_tmul (y : R) (x : N) :
      eadd (y ⊗ₜ[A] x) = algebraMap R S y • q x := by
    change em (er ((1 : B) ⊗ₜ[A] y) ⊗ₜ[B] x) = _
    rw [her, map_one, one_mul, hem]
  let e : R ⊗[A] N ≃ₗ[R] M :=
    { eadd with
      map_smul' := fun r t ↦ by
        change eadd (r • t) = r • eadd t
        induction t using TensorProduct.inductionOn with
        | tmul y x =>
          rw [smul_tmul', eadd_tmul, eadd_tmul]
          change algebraMap R S (r * y) • q x =
            algebraMap R S r • (algebraMap R S y • q x)
          rw [map_mul, mul_smul]
        | add t t' ht ht' =>
          simp only [smul_add, map_add, ht, ht'] }
  exact ⟨e, eadd_tmul⟩

end TensorProduct
