/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Localization of ideal multiplication kernels

Source: Stacks Project, Algebra, Tag 00MO, second proof paragraph;
Tags 00CS and 00DK for localization exactness and tensor compatibility.
(blueprint: lem-weil-pbc-localization-ideal-kernel-generators)
-/

@[expose] public section
universe u v w z t
open scoped TensorProduct
namespace Module

/-- Localization generates the new kernel from the ordinary base-change kernel.
Source: Stacks Project, Algebra, Tag 00MO, second proof paragraph, expanded using
Tags 00CS (localization exactness) and 00DK (tensor-localization compatibility).
(blueprint: lem-weil-pbc-localization-ideal-kernel-generators)

Proof: set A = S tensor_R R', N = R' tensor_R M and J = IR'. Tensor cancellation
identifies S' tensor_S M with the localization of N over A. Multiplication
J tensor_R' N -> N is A-linear, with A acting on N. Exactness of localization
identifies its localized kernel with the kernel of multiplication into S' tensor_S M.
Tensor-localization compatibility identifies the localized tensor product with
J tensor_R' (S' tensor_S M). Construct alpha as tensoring the canonical map
N -> S' tensor_S M, r' tensor x |-> rho'(r') times (1 tensor x), with J.
This formula is R'-balanced by the scalar tower identities and S-balanced by
the tensor relation, and hence defines an R'-linear map. Symmetry puts N first.
Every element of the localized kernel is a fraction of an element of the original
kernel. Such a fraction is the image under alpha multiplied by q(w)^{-1},
an S'-scalar, and therefore lies in the displayed S'-span. No quotient flatness,
Tor vanishing, finiteness or local hypotheses are used. If the localization set
contains zero, both the target module and its kernel are zero. -/
theorem exists_localization_ideal_kernel_generators
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type z}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (I : Ideal R) (M : Type t) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M]
    (hloc : ∃ (q : S ⊗[R] R' →+* S') (W : Submonoid (S ⊗[R] R')),
      (∀ (s : S) (r' : R'), q (s ⊗ₜ[R] r') =
        algebraMap S S' s * algebraMap R' S' r') ∧
      (letI := q.toAlgebra; IsLocalization W S')) :
    ∃ α : (R' ⊗[R] M) ⊗[R'] (I.map (algebraMap R R')) →ₗ[R']
        (S' ⊗[S] M) ⊗[R'] (I.map (algebraMap R R')),
      (∀ (r' : R') (x : M) (b : I.map (algebraMap R R')),
        α ((r' ⊗ₜ[R] x) ⊗ₜ[R'] b) =
          (algebraMap R' S' r' • ((1 : S') ⊗ₜ[S] x)) ⊗ₜ[R'] b) ∧
      (∀ z : (I.map (algebraMap R R')) ⊗[R'] (S' ⊗[S] M),
        TensorProduct.lift
          ((LinearMap.lsmul R' (S' ⊗[S] M)).comp
            (I.map (algebraMap R R')).subtype) z = 0 →
        TensorProduct.comm R' (I.map (algebraMap R R')) (S' ⊗[S] M) z ∈
          Submodule.span S'
            ((fun y : (I.map (algebraMap R R')) ⊗[R'] (R' ⊗[R] M) ↦
              α (TensorProduct.comm R' (I.map (algebraMap R R')) (R' ⊗[R] M) y)) ''
              (LinearMap.ker (TensorProduct.lift
                ((LinearMap.lsmul R' (R' ⊗[R] M)).comp
                  (I.map (algebraMap R R')).subtype)) :
                Set ((I.map (algebraMap R R')) ⊗[R'] (R' ⊗[R] M))))) := by
  obtain ⟨q, W, hq, hloc⟩ := hloc
  let N := R' ⊗[R] M
  let P := S' ⊗[S] M
  let A := S ⊗[R] R'
  let f : N →ₗ[R'] P :=
    ((TensorProduct.mk S S' M 1).restrictScalars R).liftBaseChange R'
  have hf (r : R') (m : M) : f (r ⊗ₜ[R] m) =
      algebraMap R' S' r • ((1 : S') ⊗ₜ[S] m) := by
    change r • ((1 : S') ⊗ₜ[S] m) = _
    rw [algebraMap_smul]
  -- The S-action on N is obtained by base-changing the action on M.
  let φ : S →ₐ[R] Module.End R' N :=
    (Module.End.baseChangeHom R R' M).comp (Algebra.lsmul R R M)
  let : Module S N := Module.compHom N φ.toRingHom
  have hs (s : S) (r : R') (m : M) : s • (r ⊗ₜ[R] m : N) =
      r ⊗ₜ[R] (s • m) := rfl
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change φ (algebraMap R S r) x = r • x
    rw [φ.commutes]
    rfl
  have : SMulCommClass S R' N := ⟨fun s r x ↦ (φ s).map_smul r x⟩
  let : Module A N := TensorProduct.Algebra.module
  let : Algebra R' A := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R' A N := IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change (1 : S) • r • x = r • x
    rw [one_smul]
  let : Algebra A S' := q.toAlgebra
  let : Module A P := Module.compHom P q
  have : IsScalarTower A S' P := ⟨fun a b x ↦ by
    change (q a * b) • x = q a • b • x
    exact mul_smul _ _ _⟩
  have : IsScalarTower R' A S' := IsScalarTower.of_algebraMap_smul fun r x ↦ by
    rw [Algebra.smul_def]
    change q ((1 : S) ⊗ₜ[R] r) * x = r • x
    rw [hq, map_one, one_mul]
    exact (Algebra.smul_def r x).symm
  have : IsScalarTower R' A P := IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change q ((1 : S) ⊗ₜ[R] r) • x = r • x
    rw [hq, map_one, one_mul, algebraMap_smul]
  let fA : N →ₗ[A] P :=
    { f.toAddHom with
      map_smul' := by
        intro a n
        induction a using TensorProduct.inductionOn with
        | tmul s r =>
          change R' ⊗[R] M at n
          induction n using TensorProduct.inductionOn with
          | tmul r₁ m =>
            change f (s • r • (r₁ ⊗ₜ[R] m)) = q (s ⊗ₜ[R] r) • f (r₁ ⊗ₜ[R] m)
            rw [TensorProduct.smul_tmul', hs, hf, hf, hq]
            rw [TensorProduct.tmul_smul, ← algebraMap_smul S' s]
            simp only [smul_smul, Algebra.smul_def, map_mul]
            congr 1
            simp [mul_comm, mul_left_comm]
          | add x y hx hy => simp_all
        | add a b ha hb =>
          change f ((a + b) • n) = q (a + b) • f n
          change f (a • n) = q a • f n at ha
          change f (b • n) = q b • f n at hb
          rw [add_smul, map_add, ha, hb, map_add, add_smul] }
  have : IsLocalization W S' := hloc
  have : IsScalarTower S A S' := IsScalarTower.of_algebraMap_smul fun s x ↦ by
    rw [Algebra.smul_def]
    change q (s ⊗ₜ[R] (1 : R')) * x = s • x
    rw [hq, map_one, mul_one]
    exact (Algebra.smul_def s x).symm
  -- Tensor cancellation: ((s tensor r) tensor m) maps to r tensor (s • m).
  let eR : (A ⊗[S] M) ≃ₗ[R] N :=
    ((TensorProduct.AlgebraTensorModule.rightComm R S S S M R').symm.restrictScalars R).trans
      ((TensorProduct.AlgebraTensorModule.congr (TensorProduct.lid S M)
        (LinearEquiv.refl R R')).restrictScalars R |>.trans (TensorProduct.comm R M R'))
  have heR (s : S) (r : R') (m : M) : eR ((s ⊗ₜ[R] r) ⊗ₜ[S] m) =
      r ⊗ₜ[R] (s • m) := rfl
  let e : (A ⊗[S] M) ≃ₗ[A] N :=
    { eR.toAddEquiv with
      map_smul' := by
        intro a x
        induction a using TensorProduct.inductionOn with
        | tmul s r =>
          induction x using TensorProduct.inductionOn with
          | tmul b m =>
            change S ⊗[R] R' at b
            induction b using TensorProduct.inductionOn with
            | tmul s₁ r₁ =>
              change eR (((s ⊗ₜ[R] r) * (s₁ ⊗ₜ[R] r₁)) ⊗ₜ[S] m) =
                s • r • eR ((s₁ ⊗ₜ[R] r₁) ⊗ₜ[S] m)
              rw [Algebra.TensorProduct.tmul_mul_tmul, heR, heR, TensorProduct.smul_tmul', hs]
              simp [mul_smul]
            | add b c hb hc => simp_all [TensorProduct.add_tmul]
          | add x y hx hy => simp_all
        | add a b ha hb =>
          change eR ((a + b) • x) = (a + b) • eR x
          change eR (a • x) = a • eR x at ha
          change eR (b • x) = b • eR x at hb
          rw [add_smul, map_add, ha, hb, add_smul] }
  -- Tensoring the ring localization and transporting across e localizes fA.
  let f₀ : A →ₗ[A] S' := Algebra.linearMap A S'
  let fT := TensorProduct.AlgebraTensorModule.rTensor S M f₀
  have hfe : fA.comp e.toLinearMap = fT := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    induction a using TensorProduct.inductionOn with
    | tmul s r =>
      change f (r ⊗ₜ[R] (s • m)) = q (s ⊗ₜ[R] r) ⊗ₜ[S] m
      rw [hf, hq, TensorProduct.tmul_smul, ← algebraMap_smul S' s, smul_smul,
        TensorProduct.smul_tmul']
      simp [mul_comm]
    | add a b ha hb => simp_all [TensorProduct.add_tmul]
  have hfT : IsLocalizedModule W fT := inferInstance
  have hfA : IsLocalizedModule W fA := by
    apply (IsLocalizedModule.comp_iff_of_bijective_right W e.toLinearMap e.bijective).mp
    rw [hfe]
    exact hfT
  -- Put N first so multiplication and localization are A-linear.
  let J := I.map (algebraMap R R')
  let gN : N ⊗[R'] J →ₗ[A] N := TensorProduct.AlgebraTensorModule.lift
    (((Algebra.lsmul R' A N).toLinearMap.comp J.subtype).flip)
  let gP : P ⊗[R'] J →ₗ[A] P := TensorProduct.AlgebraTensorModule.lift
    (((Algebra.lsmul R' A P).toLinearMap.comp J.subtype).flip)
  let α : N ⊗[R'] J →ₗ[R'] P ⊗[R'] J := TensorProduct.map f LinearMap.id
  let αA : N ⊗[R'] J →ₗ[A] P ⊗[R'] J := TensorProduct.AlgebraTensorModule.rTensor R' J fA
  have : IsLocalizedModule W αA := inferInstance
  have hmap : IsLocalizedModule.map W αA fA gN = gP := by
    apply IsLocalizedModule.linearMap_ext W αA fA
    rw [IsLocalizedModule.map_comp]
    apply TensorProduct.AlgebraTensorModule.ext
    intro n b
    change f (b.val • n) = b.val • f n
    exact f.map_smul _ _
  -- Mathlib identifies the localized kernel with the span of the old kernel.
  have hspan : LinearMap.ker gP =
      (Submodule.span S' (αA '' (LinearMap.ker gN : Set (N ⊗[R'] J)))).restrictScalars A := by
    rw [← hmap, LinearMap.ker_localizedMap_eq_localized'_ker S' W αA fA gN,
      Submodule.localized'_eq_span]
  have hsymN (y : J ⊗[R'] N) :
      gN (TensorProduct.comm R' J N y) =
        TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype) y := by
    induction y using TensorProduct.inductionOn with
    | tmul b n => rfl
    | add x y hx hy => simp_all
  have hsymP (z : J ⊗[R'] P) :
      gP (TensorProduct.comm R' J P z) =
        TensorProduct.lift ((LinearMap.lsmul R' P).comp J.subtype) z := by
    induction z using TensorProduct.inductionOn with
    | tmul b n => rfl
    | add x y hx hy => simp_all
  -- Reindex those generators using the symmetries in the statement.
  have hset : αA '' (LinearMap.ker gN : Set (N ⊗[R'] J)) =
      (fun y : J ⊗[R'] N ↦ α (TensorProduct.comm R' J N y)) ''
        (LinearMap.ker (TensorProduct.lift
          ((LinearMap.lsmul R' N).comp J.subtype)) : Set (J ⊗[R'] N)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(TensorProduct.comm R' J N).symm y, ?_, ?_⟩
      · change TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype)
          ((TensorProduct.comm R' J N).symm y) = 0
        rw [← hsymN, LinearEquiv.apply_symm_apply]
        exact hy
      · simp only [LinearEquiv.apply_symm_apply]
        rfl
    · rintro ⟨y, hy, rfl⟩
      refine ⟨TensorProduct.comm R' J N y, ?_, rfl⟩
      change gN (TensorProduct.comm R' J N y) = 0
      rw [hsymN]
      exact hy
  refine ⟨α, ?_, ?_⟩
  · intro r x b
    change f (r ⊗ₜ[R] x) ⊗ₜ[R'] b = _
    rw [hf]
  · intro z hz
    rw [← hset]
    change TensorProduct.comm R' J P z ∈
      (Submodule.span S' (αA '' (LinearMap.ker gN : Set (N ⊗[R'] J)))).restrictScalars A
    rw [← hspan, LinearMap.mem_ker, hsymP]
    exact hz

end Module
