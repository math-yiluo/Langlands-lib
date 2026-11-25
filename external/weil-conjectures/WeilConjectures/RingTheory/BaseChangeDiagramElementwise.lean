/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-! # Representatives in a diagram with tensor base-change isomorphisms
Source: Stacks Project, Algebra, Tags 00D6, 00D7 and 00DD, used in Tag 00QX.
(blueprint: lem-weil-pbc-base-change-diagram-elementwise).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- A compatible tensor base-change diagram has representatives and eventual zero.
Source: Stacks Project, Algebra, Tags 00D6, 00D7 and 00DD.
(blueprint: lem-weil-pbc-base-change-diagram-elementwise)

Proof: Fix a stage i₀ and restrict to its upper tail. Regard its rings as B(i₀)-modules.
Map their module direct limit to S using κ. Ring-colimit representatives and eventual
equality make this map a linear equivalence. Tensor it with D(i₀) and compose with
`TensorProduct.directLimitLeft` to identify the tensor direct limit with S tensor D(i₀).
Tensor induction checks the comparison on each stage.
Transport its representative assertion through the equivalences
B(j) tensor D(i₀) ≃ D(j) for j ≥ i₀ and S tensor D(i₀) ≃ M. The transport
intertwines the ring-induced tensor maps with D and ν, since both sides agree on
pure tensors by the assumed formulas, cocone naturality and scalar compatibility.
This gives representatives for every element of M. For an element x of D(i) with
ν(i)(x) = 0, apply the same argument with i₀ = i and the pure tensor 1 tensor x.
Its image in S tensor D(i) is zero, by injectivity of the given equivalence with M.
The eventual-zero assertion gives j ≥ i where its image in B(j) tensor D(i) vanishes.
The equivalence to D(j) carries this tensor to D(i → j)(x), proving eventual zero.
This argument uses neither finite presentation nor finite generation, and no additive
colimit criterion or restriction on the relative sizes of u and v.
-/
theorem baseChange_diagram_elementwise
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (B : I ⥤ CommRingCat.{u}) (S : Type u) [CommRing S]
    (κ : B ⟶ (Functor.const I).obj (CommRingCat.of S))
    (hκ : Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)))
    (M : Type v) [AddCommGroup M] [Module S M]
    (D : I ⥤ AddCommGrpCat.{v})
    (ν : D ⟶ (Functor.const I).obj (AddCommGrpCat.of M))
    [∀ i, Module (B.obj i) (D.obj i)]
    (hν : ∀ i (y : B.obj i) (x : D.obj i),
      (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
        (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) y •
          (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
    (hbase : ∀ (i j : I) (h : i ≤ j),
      letI := (B.map (homOfLE h)).hom.toAlgebra
      ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
        ∀ (y : B.obj j) (x : D.obj i),
          e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x)
    (hS : ∀ i,
      letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
      ∃ e : S ⊗[B.obj i] D.obj i ≃ₗ[S] M,
        ∀ (y : S) (x : D.obj i), e (y ⊗ₜ[B.obj i] x) =
          y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) :
    (∀ x : M, ∃ (i : I) (y : D.obj i),
      (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) y = x) ∧
    (∀ (i : I) (x : D.obj i), (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x = 0 →
      ∃ (j : I) (h : i ≤ j), (D.map (homOfLE h)).hom x = 0) := by
  classical
  have H (i₀ : I) :
      (∀ x : M, ∃ (i : I) (y : D.obj i), (ν.app i).hom y = x) ∧
      (∀ x : D.obj i₀, (ν.app i₀).hom x = 0 →
        ∃ (j : I) (h : i₀ ≤ j), (D.map (homOfLE h)).hom x = 0) := by
    classical
    let : IsFiltered I := inferInstance
    let : PreservesColimit B (forget CommRingCat) := inferInstance
    let R₀ := B.obj i₀
    let : Algebra R₀ S := (κ.app i₀).hom.toAlgebra
    let J := {i : I // i₀ ≤ i}
    let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
    let : IsDirectedOrder J := ⟨fun i j ↦ by
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
      exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
    let A : J → Type u := fun i ↦ B.obj i.val
    let : ∀ i, CommRing (A i) := fun i ↦ inferInstance
    let : ∀ i, Algebra R₀ (A i) := fun i ↦ (B.map (homOfLE i.property)).hom.toAlgebra
    let f (i j : J) (h : i ≤ j) : A i →ₗ[R₀] A j :=
      AlgHom.toLinearMap
        { (B.map (homOfLE h)).hom with
          commutes' := fun s ↦ congrArg (fun p : B.obj i₀ ⟶ B.obj j.val ↦ p s)
            (B.map_comp (homOfLE i.property) (homOfLE h)).symm }
    let α (i : J) : A i →ₗ[R₀] S :=
      AlgHom.toLinearMap
        { (κ.app i.val).hom with
          commutes' := fun s ↦ congrArg (fun p : B.obj i₀ ⟶ CommRingCat.of S ↦ p s)
            (κ.naturality (homOfLE i.property)) }
    have compat (i j : J) (h : i ≤ j) (a : A i) : α j (f i j h a) = α i a := by
      exact ConcreteCategory.congr_hom (κ.naturality (homOfLE h)) a
    let : DirectedSystem A (fun {i j} h ↦ f i j h) :=
      { map_self := by
          intro i a
          change B.map (homOfLE (le_refl i.val)) a = a
          simp
        map_map := by
          intro i j k hij hjk a
          change B.map (homOfLE hjk) (B.map (homOfLE hij) a) =
            B.map (homOfLE (hij.trans hjk)) a
          exact (ConcreteCategory.congr_hom
            (B.map_comp (homOfLE hij) (homOfLE hjk)) a).symm }
    let g : Module.DirectLimit A f →ₗ[R₀] S :=
      Module.DirectLimit.lift R₀ J A f α compat
    have ginj : Function.Injective g := by
      intro x y hxy
      obtain ⟨i, a, hx⟩ := Module.DirectLimit.exists_of x
      obtain ⟨j, b, hy⟩ := Module.DirectLimit.exists_of y
      rw [← hx, ← hy] at hxy ⊢
      simp only [g, Module.DirectLimit.lift_of] at hxy
      obtain ⟨k, u, v, he⟩ := Concrete.isColimit_rep_eq_iff_exists B hκ.some a b |>.mp hxy
      let k' : J := ⟨k, i.property.trans (leOfHom u)⟩
      have he' : f i k' (leOfHom u) a = f j k' (leOfHom v) b := he
      rw [← Module.DirectLimit.of_f (f := f) (i := i) (j := k') (hij := leOfHom u),
        ← Module.DirectLimit.of_f (f := f) (i := j) (j := k') (hij := leOfHom v), he']
    have gsurj : Function.Surjective g := by
      intro r
      obtain ⟨i, a, ha⟩ := Concrete.isColimit_exists_rep B hκ.some r
      obtain ⟨j, h₀j, hij⟩ := exists_ge_ge i₀ i
      let j' : J := ⟨j, h₀j⟩
      refine ⟨Module.DirectLimit.of R₀ J A f j' (B.map (homOfLE hij) a), ?_⟩
      simp only [g, Module.DirectLimit.lift_of]
      change κ.app j (B.map (homOfLE hij) a) = r
      exact (ConcreteCategory.congr_hom (κ.naturality (homOfLE hij)) a).trans ha
    let E : Module.DirectLimit A f ≃ₗ[R₀] S := LinearEquiv.ofBijective g ⟨ginj, gsurj⟩
    let ft (i j : J) (h : i ≤ j) := (f i j h).rTensor (D.obj i₀)
    let e : Module.DirectLimit (fun i ↦ A i ⊗[R₀] D.obj i₀) ft ≃ₗ[R₀] S ⊗[R₀] D.obj i₀ :=
      (TensorProduct.directLimitLeft f (D.obj i₀)).symm.trans (E.rTensor (D.obj i₀))
    have e_of (i : J) (t : A i ⊗[R₀] D.obj i₀) :
        e (Module.DirectLimit.of R₀ J (fun i ↦ A i ⊗[R₀] D.obj i₀) ft i t) =
          (α i).rTensor (D.obj i₀) t := by
      induction t using TensorProduct.inductionOn with
      | tmul a m =>
        dsimp only [e, ft]
        rw [LinearEquiv.trans_apply, TensorProduct.directLimitLeft_symm_of_tmul,
          LinearEquiv.rTensor_tmul, LinearMap.rTensor_tmul]
        change g (Module.DirectLimit.of R₀ J A f i a) ⊗ₜ[R₀] m = α i a ⊗ₜ[R₀] m
        simp only [g, Module.DirectLimit.lift_of]
      | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
    let : DirectedSystem (fun i ↦ A i ⊗[R₀] D.obj i₀) (fun {i j} h ↦ ft i j h) :=
      { map_self := by
          intro i t
          induction t using TensorProduct.inductionOn with
          | tmul a m => simp only [ft, LinearMap.rTensor_tmul, DirectedSystem.map_self']
          | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
        map_map := by
          intro i j k hij hjk t
          induction t using TensorProduct.inductionOn with
          | tmul a m => simp only [ft, LinearMap.rTensor_tmul, DirectedSystem.map_map']
          | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu }
    choose q hq using hS i₀
    have q_formula (y : S) (x : D.obj i₀) :
        q (y ⊗ₜ[R₀] x) =
          y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i₀)) x := hq y x
    have compare (i : J) (t : A i ⊗[R₀] D.obj i₀) :
        ∃ z : D.obj i.val,
          (ν.app i.val).hom z = q ((α i).rTensor (D.obj i₀) t) := by
      obtain ⟨p, hp⟩ := hbase i₀ i.val i.property
      refine ⟨p t, ?_⟩
      induction t using TensorProduct.inductionOn with
      | tmul a x =>
        rw [hp, LinearMap.rTensor_tmul, q_formula]
        have hv := hν i.val a ((D.map (homOfLE i.property)).hom x)
        have hn := ConcreteCategory.congr_hom (ν.naturality (homOfLE i.property)) x
        exact hv.trans (congrArg (fun m : M ↦
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i.val)) a • m) hn)
      | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
    constructor
    · intro x
      obtain ⟨i, t, ht⟩ := Module.DirectLimit.exists_of (e.symm (q.symm x))
      obtain ⟨z, hz⟩ := compare i t
      refine ⟨i.val, z, ?_⟩
      rw [hz, ← e_of, ht, e.apply_symm_apply, q.apply_symm_apply]
    · intro x hx
      let i : J := ⟨i₀, le_rfl⟩
      let : Module R₀ (A i) :=
        @Algebra.toModule R₀ (A i) _ _ (inferInstance : Algebra R₀ (A i))
      let t : A i ⊗[R₀] D.obj i₀ := 1 ⊗ₜ[R₀] x
      have hz : e (Module.DirectLimit.of R₀ J
          (fun i ↦ A i ⊗[R₀] D.obj i₀) ft i t) = 0 := by
        apply q.injective
        rw [map_zero, e_of]
        change q ((α i).rTensor (D.obj i₀) (1 ⊗ₜ[R₀] x)) = 0
        rw [LinearMap.rTensor_tmul, q_formula]
        have hα : α i 1 = 1 := by
          change (κ.app i.val).hom 1 = 1
          exact map_one _
        rw [hα, one_smul]
        exact hx
      have hz' : Module.DirectLimit.of R₀ J
          (fun i ↦ A i ⊗[R₀] D.obj i₀) ft i t = 0 := by
        apply e.injective
        simpa only [map_zero] using hz
      obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hz'
      obtain ⟨p, hp⟩ := hbase i₀ j.val hij
      refine ⟨j.val, hij, ?_⟩
      have hpz := congrArg p hj
      change p ((f i j hij).rTensor (D.obj i₀) (1 ⊗ₜ[R₀] x)) = p 0 at hpz
      have hf : f i j hij 1 = 1 := by
        change (B.map (homOfLE hij)).hom 1 = 1
        exact map_one _
      rw [LinearMap.rTensor_tmul, hf, hp, map_zero, one_smul] at hpz
      exact hpz
  exact ⟨(H (Classical.arbitrary I)).1, fun i ↦ (H i).2⟩

end Module
