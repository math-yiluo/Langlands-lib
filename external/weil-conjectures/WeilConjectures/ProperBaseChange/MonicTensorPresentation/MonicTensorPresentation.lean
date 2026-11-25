/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-! # Tensor presentations by monic equations

Source: Stacks Project, Morphisms, Tag 03HW, proof of lemma-massage-finite
(blueprint: lem-weil-pbc-monic-tensor-presentation).
-/

@[expose] public section

universe u v

open scoped TensorProduct
open Polynomial

namespace MonicTensorPresentation

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
variable {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable {S : Type u} [CommRing S] [Algebra R S]

/-- The algebra map from a finite tensor product induced by maps on its factors. -/
noncomputable def tensorLift (g : ∀ i, A i →ₐ[R] S) : (⨂[R] i, A i) →ₐ[R] S :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra R ι S).compLinearMap (fun i ↦ (g i).toLinearMap))
    (by simp)
    (by intro x y; simp [Finset.prod_mul_distrib])

@[simp] theorem tensorLift_tprod (g : ∀ i, A i →ₐ[R] S) (x : ∀ i, A i) :
    tensorLift g (PiTensorProduct.tprod R x) = ∏ i, g i (x i) := by
  simp [tensorLift]

@[simp] theorem tensorLift_single [DecidableEq ι] (g : ∀ i, A i →ₐ[R] S)
    (i : ι) (x : A i) :
    tensorLift g (PiTensorProduct.singleAlgHom i x) = g i x := by
  rw [PiTensorProduct.singleAlgHom_apply, tensorLift_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · simp

/-- The finite free tensor algebra of the one-variable monic quotients. -/
abbrev Tensor (P : ι → R[X]) := ⨂[R] i, AdjoinRoot (P i)

/-- Evaluation of the tensor presentation at a tuple satisfying its equations. -/
noncomputable def presentationMap (P : ι → R[X]) (x : ι → S)
    (hx : ∀ i, aeval (x i) (P i) = 0) : Tensor P →ₐ[R] S :=
  tensorLift (fun i ↦ AdjoinRoot.liftAlgHom (P i) (Algebra.ofId R S) (x i) (hx i))

@[simp] theorem presentationMap_root [DecidableEq ι]
    (P : ι → R[X]) (x : ι → S) (hx : ∀ i, aeval (x i) (P i) = 0) (i : ι) :
    presentationMap P x hx (PiTensorProduct.singleAlgHom i (AdjoinRoot.root (P i))) =
      x i := by
  unfold presentationMap
  rw [tensorLift_single, AdjoinRoot.liftAlgHom_root]

/-- The tensor products of the power bases form a finite basis. -/
noncomputable def basis (P : ι → R[X]) (hP : ∀ i, (P i).Monic) :
    Module.Basis (∀ i, Fin (P i).natDegree) R (Tensor P) :=
  Basis.piTensorProduct (fun i ↦ (AdjoinRoot.powerBasis' (hP i)).basis)

/-- Algebra generators lift along the tensor presentation map.
Source: Stacks Project, Tag 03HW, the surjection from the monic presentation algebra.
The image contains each chosen generator since evaluation of its distinguished tensor root
is that generator. The algebraic span of the generators is therefore contained in the image;
by the generation hypothesis this is the whole target algebra.
(blueprint: lem-weil-pbc-monic-tensor-presentation). -/
theorem presentationMap_surjective (P : ι → R[X]) (x : ι → S)
    (hx : ∀ i, aeval (x i) (P i) = 0)
    (hgen : Algebra.adjoin R (Set.range x) = ⊤) :
    Function.Surjective (presentationMap P x hx) := by
  classical
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  exact ⟨PiTensorProduct.singleAlgHom i (AdjoinRoot.root (P i)),
    presentationMap_root P x hx i⟩

end MonicTensorPresentation
