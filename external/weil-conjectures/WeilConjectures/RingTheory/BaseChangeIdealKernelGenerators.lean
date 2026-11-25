/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Flat.Stability
import WeilConjectures.RingTheory.FlatQuotientPresentationIntersection

/-!
# Ideal multiplication kernels under ordinary base change

Source: Stacks Project, Algebra, Tags 00MO, 00MM, 00MN and 00M6.
(blueprint: lem-weil-pbc-base-change-ideal-kernel-generators)
-/

@[expose] public section
universe u w t
open scoped TensorProduct
namespace Module

private def idealMul {A X : Type*} [CommRing A] [AddCommGroup X] [Module A X]
    (J : Ideal A) : J ⊗[A] X →ₗ[A] X :=
  TensorProduct.lift ((LinearMap.lsmul A X).comp J.subtype)

private def idealTensorChange {A B X : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] (J : Ideal A) :
    J ⊗[A] X →+ J.map (algebraMap A B) ⊗[B] (B ⊗[A] X) := by
  let j : J →+ J.map (algebraMap A B) :=
    { toFun := fun a ↦ ⟨algebraMap A B a, Ideal.mem_map_of_mem _ a.property⟩
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  let g : X →+ B ⊗[A] X := (TensorProduct.mk A B X 1).toAddMonoidHom
  let f : J →+ X →+ J.map (algebraMap A B) ⊗[B] (B ⊗[A] X) :=
    { toFun := fun a ↦ ((TensorProduct.mk B _ _ (j a)).toAddMonoidHom).comp g
      map_zero' := by
        ext x
        change j 0 ⊗ₜ[B] g x = 0
        rw [j.map_zero, TensorProduct.zero_tmul]
      map_add' := fun a b ↦ by ext x; simp }
  refine TensorProduct.liftAddHom f ?_
  intro r a x
  change j (r • a) ⊗ₜ[B] (1 ⊗ₜ[A] x) = j a ⊗ₜ[B] (1 ⊗ₜ[A] (r • x))
  have hj : j (r • a) = algebraMap A B r • j a := by
    ext
    simp [j, Algebra.smul_def]
  rw [hj, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  simp [TensorProduct.tmul_smul]

private theorem idealTensorChange_tmul {A B X : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup X] [Module A X]
    (J : Ideal A) (a : J) (x : X) :
    idealTensorChange (B := B) J (a ⊗ₜ[A] x) =
      (⟨algebraMap A B a, Ideal.mem_map_of_mem _ a.property⟩ : J.map (algebraMap A B))
        ⊗ₜ[B] (1 ⊗ₜ[A] x) := by
  simp [idealTensorChange, TensorProduct.liftAddHom_tmul]

private theorem idealMul_tmul {A X : Type*} [CommRing A] [AddCommGroup X] [Module A X]
    (J : Ideal A) (a : J) (x : X) : idealMul J (a ⊗ₜ[A] x) = (a : A) • x := rfl

private theorem idealMul_range {A X : Type*} [CommRing A] [AddCommGroup X] [Module A X]
    (J : Ideal A) : LinearMap.range (idealMul (X := X) J) = J • (⊤ : Submodule A X) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a x => exact Submodule.smul_mem_smul a.property (Submodule.mem_top)
    | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro a ha x _
    exact ⟨(⟨a, ha⟩ : J) ⊗ₜ[A] x, rfl⟩

private theorem idealMul_injective {A X : Type*} [CommRing A] [AddCommGroup X] [Module A X]
    [Module.Flat A X] (J : Ideal A) : Function.Injective (idealMul (X := X) J) := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap
    (M := X) J.subtype J.injective_subtype
  intro x y h
  apply hinj
  apply (TensorProduct.lid A X).injective
  have he : (TensorProduct.lid A X).toLinearMap.comp (J.subtype.rTensor X) =
      idealMul J := by
    ext a x
    simp [idealMul]
  change ((TensorProduct.lid A X).toLinearMap.comp (J.subtype.rTensor X)) x =
    ((TensorProduct.lid A X).toLinearMap.comp (J.subtype.rTensor X)) y
  rw [he]
  exact h

private theorem idealTensorChange_mul {A B X : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup X] [Module A X]
    (J : Ideal A) (t : J ⊗[A] X) :
    idealMul (J.map (algebraMap A B)) (idealTensorChange (B := B) J t) =
      (1 : B) ⊗ₜ[A] idealMul J t := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [idealTensorChange_tmul, idealMul_tmul, idealMul_tmul]
    simp [TensorProduct.tmul_smul]
  | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add]

private theorem idealMul_naturality {A X Y : Type*}
    [CommRing A] [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (J : Ideal A) (q : X →ₗ[A] Y) (t : J ⊗[A] X) :
    q (idealMul J t) = idealMul J (q.lTensor J t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a x => simp [idealMul_tmul]
  | add x y hx hy => simp [hx, hy]

private theorem idealTensorChange_naturality {A B X Y : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (J : Ideal A) (q : X →ₗ[A] Y) (t : J ⊗[A] X) :
    (q.baseChange B).lTensor (J.map (algebraMap A B))
      (idealTensorChange (B := B) J t) =
        idealTensorChange (B := B) J (q.lTensor J t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a x => simp [idealTensorChange_tmul]
  | add x y hx hy => simp [hx, hy]

/-- Ordinary base change generates the ideal multiplication kernel when the quotient is flat.
Source: Stacks Project, Algebra, Tag 00MO, third proof paragraph, using Tags 00MM,
00MN and the connecting-map description of Tag 00M6.
(blueprint: lem-weil-pbc-base-change-ideal-kernel-generators)

Proof: write Q = R/I, J = IR', Q' = R'/J and N = R' tensor_R M.
Construct theta by the balanced bilinear rule a tensor x |-> rho(a) tensor (1 tensor x).
Tag 00MM for R -> Q -> Q' gives a canonical surjection from Tor_1(M,Q) tensor_Q Q'
to Tor_1(M,Q'); the flatness assumption is exactly the hypothesis of that tag.
Compose with the change-of-rings surjection of Tag 00MN. The connecting maps of
Tag 00M6 identify the target with ker(J tensor N -> N) and the original Tor with
ker(I tensor M -> M). Naturality identifies the map on generators with theta.
Since I annihilates the original Tor, tensoring this kernel over Q with Q' equals
tensoring it over R with R'. Every tensor is a finite sum of pure tensors, whose
images are R'-scalar multiples of theta(k). Tensor symmetry transfers this
statement into the displayed span. This constructs theta from its pure-tensor
formula, rather than choosing unspecified data from an existence assertion.
The zero ideal, unit ideal and zero base-change ring all give zero kernels. -/
theorem exists_baseChange_ideal_kernel_generators
    {R : Type u} {R' : Type w} [CommRing R] [CommRing R'] [Algebra R R']
    (I : Ideal R) (M : Type t) [AddCommGroup M] [Module R M]
    (hquot : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)) :
    ∃ θ : I ⊗[R] M →+ (I.map (algebraMap R R')) ⊗[R'] (R' ⊗[R] M),
      (∀ (a : I) (x : M), θ (a ⊗ₜ[R] x) =
        (⟨algebraMap R R' a, Ideal.mem_map_of_mem (algebraMap R R') a.property⟩ :
          I.map (algebraMap R R')) ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] x)) ∧
      (∀ y : (I.map (algebraMap R R')) ⊗[R'] (R' ⊗[R] M),
        TensorProduct.lift
          ((LinearMap.lsmul R' (R' ⊗[R] M)).comp
            (I.map (algebraMap R R')).subtype) y = 0 →
        TensorProduct.comm R' (I.map (algebraMap R R')) (R' ⊗[R] M) y ∈
          Submodule.span R'
            ((fun k : I ⊗[R] M ↦
              TensorProduct.comm R' (I.map (algebraMap R R')) (R' ⊗[R] M) (θ k)) ''
              (LinearMap.ker (TensorProduct.lift
                ((LinearMap.lsmul R M).comp I.subtype)) : Set (I ⊗[R] M)))) := by
  classical
  let J := I.map (algebraMap R R')
  let θ := idealTensorChange (B := R') (X := M) I
  refine ⟨θ, idealTensorChange_tmul I, ?_⟩
  intro y hy
  let P := Submodule.span R' (θ '' (idealMul (X := M) I).ker)
  suffices hyP : y ∈ P by
    apply Submodule.span_induction (p := fun z _ ↦
      TensorProduct.comm R' J (R' ⊗[R] M) z ∈
        Submodule.span R'
          ((fun k ↦ TensorProduct.comm R' J (R' ⊗[R] M) (θ k)) ''
            (idealMul (X := M) I).ker)) ?_ ?_ ?_ ?_ hyP
    · rintro _ ⟨k, hk, rfl⟩
      exact Submodule.subset_span ⟨k, hk, rfl⟩
    · simp
    · intro x z _ _ hx hz
      simpa using Submodule.add_mem _ hx hz
    · intro r x _ hx
      simpa using Submodule.smul_mem _ r hx
  let F := M →₀ R
  let q : F →ₗ[R] M := Finsupp.linearCombination R id
  have hq : Function.Surjective q := by
    intro x
    refine ⟨Finsupp.single x 1, ?_⟩
    change Finsupp.linearCombination R id (Finsupp.single x 1) = x
    rw [Finsupp.linearCombination_single]
    exact one_smul R x
  let γ := q.baseChange R'
  let β := γ.lTensor J
  let W := Submodule.map (idealMul (X := R' ⊗[R] F) J) (P.comap β)
  have hγ : q.ker.baseChange R' ≤ γ.ker := by
    rintro z ⟨t, rfl⟩
    rw [LinearMap.mem_ker]
    change γ (q.ker.subtype.baseChange R' t) = 0
    induction t using TensorProduct.inductionOn with
    | tmul r k => simp [γ, LinearMap.mem_ker.mp k.property]
    | add a b ha hb => simp [ha, hb]
  have hleft : (q.ker ⊓ I • (⊤ : Submodule R F)).baseChange R' ≤ W := by
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨t, ht⟩ := (idealMul_range (X := F) I ▸ hf.2 :
      f ∈ LinearMap.range (idealMul I))
    refine ⟨idealTensorChange (B := R') I t, ?_, ?_⟩
    · change β (idealTensorChange (B := R') I t) ∈ P
      rw [idealTensorChange_naturality]
      apply Submodule.subset_span
      refine ⟨q.lTensor I t, ?_, rfl⟩
      change idealMul I (q.lTensor I t) = 0
      rw [← idealMul_naturality, ht]
      exact LinearMap.mem_ker.mp hf.1
    · rw [idealTensorChange_mul, ht]
      rfl
  have hright : J • q.ker.baseChange R' ≤ W := by
    apply Submodule.smul_le.mpr
    intro a ha z hz
    refine ⟨(⟨a, ha⟩ : J) ⊗ₜ[R'] z, ?_, rfl⟩
    change β ((⟨a, ha⟩ : J) ⊗ₜ[R'] z) ∈ P
    have hz0 : γ z = 0 := LinearMap.mem_ker.mp (hγ hz)
    simp [β, hz0]
  have hintersection : q.ker.baseChange R' ⊓
      J • (⊤ : Submodule R' (R' ⊗[R] F)) ≤ W :=
    (flat_quotient_presentation_intersection I q hq hquot).trans
      (sup_le hleft hright)
  have hβ : Function.Surjective β :=
    LinearMap.lTensor_surjective J (LinearMap.baseChange_surjective R' hq)
  obtain ⟨x, rfl⟩ := hβ y
  have hxker : idealMul J x ∈ q.ker.baseChange R' := by
    have hx0 : γ (idealMul J x) = 0 := by
      rw [idealMul_naturality]
      exact hy
    exact (_root_.lTensor_exact R' q.exact_subtype_ker_map hq _).mp hx0
  have hxideal : idealMul J x ∈ J • (⊤ : Submodule R' (R' ⊗[R] F)) := by
    rw [← idealMul_range]
    exact ⟨x, rfl⟩
  obtain ⟨x', hx', heq⟩ := hintersection ⟨hxker, hxideal⟩
  have hx : x' = x := idealMul_injective J heq
  exact hx ▸ hx'

end Module
