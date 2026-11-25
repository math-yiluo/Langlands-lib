/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Lifting tensor cycles across a flat cokernel

Source: Stacks Project, Algebra, Tag 00MM, the kernel base-change paragraph.
(blueprint: lem-weil-pbc-tensor-cycles-flat-cokernel)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Algebra, Tag 00MM (lemma-surjective-on-tor-one),
the paragraph proving the surjection from the base change of the cycle module.

Proof: tensor the exact presentation X → Y → Z → 0 with A. Put I equal to the
image of X ⊗ A → Y ⊗ A and K equal to its kernel. The sequence
0 → I → Y ⊗ A → Z ⊗ A → 0 has flat final term, so tensoring with B over A
preserves injectivity at I. Tensor right exactness applied to
K → X ⊗ A → I → 0 then identifies the image of K ⊗[A] B with the kernel
of X ⊗ B → Y ⊗ B, using the associativity isomorphisms for scalar extension.
Write a preimage in K ⊗[A] B as a finite sum of pure tensors. Their images
are exactly the displayed coefficient maps, giving the claimed finite sum.
This is a statement about cycles only: it does not involve boundaries or Tor.
It also applies when the presentation terms are not projective.
(blueprint: lem-weil-pbc-tensor-cycles-flat-cokernel) -/
theorem tensor_cycles_flat_cokernel
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (X Y Z : ModuleCat.{u} R) (d : X ⟶ Y) (q : Y ⟶ Z)
    (hexact : Function.Exact d q) (hq : Function.Surjective q)
    (hflat : Module.Flat A (A ⊗[R] Z))
    (z : X ⊗ ModuleCat.of R B) (hz : (d ▷ ModuleCat.of R B) z = 0) :
    ∃ (n : ℕ) (x : Fin n → X ⊗ ModuleCat.of R A) (b : Fin n → B),
      (∀ i, (d ▷ ModuleCat.of R A) (x i) = 0) ∧
      z = ∑ i, (X ◁ ModuleCat.ofHom
        ((Algebra.lsmul R R B (b i)).comp
          (IsScalarTower.toAlgHom R A B).toLinearMap)) (x i) := by
  classical
  let dA := d.hom.baseChange A
  let qA := q.hom.baseChange A
  have heA : Function.Exact dA qA := lTensor_exact A hexact hq
  have hqA : Function.Surjective qA := LinearMap.lTensor_surjective A hq
  let I := LinearMap.range dA
  let K := LinearMap.ker dA
  let dI : (A ⊗[R] X) →ₗ[A] I := dA.rangeRestrict
  have hdI : Function.Surjective dI := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have heI : Function.Exact K.subtype dI := by
    intro x
    change dI x = 0 ↔ ∃ y : K, y.val = x
    constructor
    · intro h
      exact ⟨⟨x, congrArg Subtype.val h⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext y.property
  have heQ : Function.Exact I.subtype qA := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    exact LinearMap.exact_iff.mp heA
  let := hflat
  have hinj : Function.Injective (I.subtype.lTensor B) :=
    LinearMap.lTensor_injective_of_exact_of_flat qA hqA I.subtype
      I.subtype_injective heQ B
  let eX := TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B X
  let eY := TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B Y
  let z' := (TensorProduct.comm R X B) z
  let w := eX.symm z'
  have hcomm (v : B ⊗[A] (A ⊗[R] X)) :
      eY (dA.lTensor B v) = (d.hom.baseChange B) (eX v) := by
    induction v using TensorProduct.inductionOn with
    | tmul b v =>
      induction v using TensorProduct.inductionOn with
      | tmul a x => rfl
      | add v v' hv hv' => simp only [TensorProduct.tmul_add, map_add, hv, hv']
    | add v v' hv hv' => simp only [map_add, hv, hv']
  have hdz : d.hom.baseChange B z' = 0 := by
    have hc : ((d.hom.baseChange B).restrictScalars R).comp (TensorProduct.comm R X B).toLinearMap =
        (TensorProduct.comm R Y B).toLinearMap.comp (d ▷ ModuleCat.of R B).hom := by
      ext x b
      rfl
    change (((d.hom.baseChange B).restrictScalars R).comp
      (TensorProduct.comm R X B).toLinearMap) z = 0
    rw [hc]
    change (TensorProduct.comm R Y B) ((d ▷ ModuleCat.of R B) z) = 0
    rw [hz, map_zero]
  have hdw : dA.lTensor B w = 0 := by
    apply eY.injective
    rw [map_zero, hcomm]
    simpa [w] using hdz
  have hiw : dI.lTensor B w = 0 := by
    apply hinj
    rw [map_zero]
    have hf : I.subtype.comp dI = dA := rfl
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hf, hdw]
  obtain ⟨v, hv⟩ := (lTensor_exact B heI hdI w).mp hiw
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset v
  let e := (Fintype.equivFin S).symm
  let x : Fin (Fintype.card S) → X ⊗ ModuleCat.of R A := fun i ↦
    (TensorProduct.comm R A X) (e i).val.2.val
  let b : Fin (Fintype.card S) → B := fun i ↦ (e i).val.1
  refine ⟨Fintype.card S, x, b, ?_, ?_⟩
  · intro i
    have hc : (d ▷ ModuleCat.of R A).hom.comp (TensorProduct.comm R A X).toLinearMap =
        (TensorProduct.comm R A Y).toLinearMap.comp (dA.restrictScalars R) := by
      ext a x
      rfl
    change ((d ▷ ModuleCat.of R A).hom.comp
      (TensorProduct.comm R A X).toLinearMap) (e i).val.2.val = 0
    rw [hc]
    change (TensorProduct.comm R A Y) (dA (e i).val.2.val) = 0
    rw [(e i).val.2.property, map_zero]
  · have hsum : v = ∑ i, b i ⊗ₜ[A] (e i).val.2 := by
      rw [hS, ← Finset.sum_coe_sort S]
      exact (Fintype.sum_equiv e _ _ (fun i ↦ rfl)).symm
    have hval := congrArg (fun w ↦ (TensorProduct.comm R B X) (eX w)) hv
    have hterm (b : B) (k : K) :
        (TensorProduct.comm R B X) (eX (b ⊗ₜ[A] k.val)) =
        (X ◁ ModuleCat.ofHom ((Algebra.lsmul R R B b).comp
          (IsScalarTower.toAlgHom R A B).toLinearMap))
          ((TensorProduct.comm R A X) k.val) := by
      have h (v : A ⊗[R] X) :
          (TensorProduct.comm R B X) (eX (b ⊗ₜ[A] v)) =
          (X ◁ ModuleCat.ofHom ((Algebra.lsmul R R B b).comp
            (IsScalarTower.toAlgHom R A B).toLinearMap))
            ((TensorProduct.comm R A X) v) := by
        induction v using TensorProduct.inductionOn with
        | tmul a x =>
          change x ⊗ₜ[R] (a • b) = x ⊗ₜ[R] (b * algebraMap A B a)
          rw [Algebra.smul_def, mul_comm]
        | add v v' hv hv' => simp only [TensorProduct.tmul_add, map_add, hv, hv']
      exact h k.val
    have hr : (TensorProduct.comm R B X) (eX w) = z := by
      change (TensorProduct.comm R B X) (eX (eX.symm z')) = z
      rw [LinearEquiv.apply_symm_apply]
      exact (TensorProduct.comm R X B).symm_apply_apply z
    rw [← hr, ← hval, hsum, map_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact hterm (b i) (e i).val.2


end CategoryTheory
