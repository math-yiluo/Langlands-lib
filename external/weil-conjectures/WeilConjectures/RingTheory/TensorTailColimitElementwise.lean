/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Order.Directed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-! # Tensor products over an arbitrary colimit on a cofinal tail

Source: Stacks Project, Algebra, Tags 00D6, 00D7 and 00DD.
(blueprint: lem-pc-tensor-tail-colimit-elementwise)
-/

@[expose] public section

universe v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TensorProduct

/-- Tensor representatives and eventual vanishing over any colimit cocone,
with representatives restricted to a prescribed cofinal upper tail.

Source: Stacks Project, Algebra, Tags 00D6, 00D7 and 00DD.
(blueprint: lem-pc-tensor-tail-colimit-elementwise)

Proof: On the tail above k, regard the ring diagram as a diagram of F(i₀)-modules.
The elementwise criterion for a filtered ring colimit identifies its module direct
limit with c.pt: move representatives above k and use eventual equality for
injectivity. Tensor this linear equivalence with M₀ and use directLimitLeft.
Represent the inverse image of a tensor at a stage; injectivity and zero_exact
prove eventual vanishing. This works for preorders without taking a reflection.
-/
theorem tensorTailColimitElementwise
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) (c : Cocone F) (hc : IsColimit c)
    (i₀ : I) (M₀ : Type w) [AddCommGroup M₀] [Module (F.obj i₀) M₀] (k : I) (hik : i₀ ≤ k) :
    let S := F.obj i₀
    let R := c.pt
    letI : Algebra S R := (c.ι.app i₀).hom.toAlgebra
    (∀ x : R ⊗[S] M₀, ∃ (i : I) (h : k ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE (hik.trans h))).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (c.ι.app i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ c.pt ↦ f s) (c.w (homOfLE (hik.trans h))) }
      ∃ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = x) ∧
    (∀ (i : I) (h : k ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE (hik.trans h))).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (c.ι.app i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ c.pt ↦ f s) (c.w (homOfLE (hik.trans h))) }
      ∀ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = 0 →
        ∃ (i' : I) (h' : i ≤ i'),
          letI : Algebra S (F.obj i') := (F.map (homOfLE (hik.trans (h.trans h')))).hom.toAlgebra
          let αᵢ'ᵢ : F.obj i →ₐ[S] F.obj i' :=
            { (F.map (homOfLE h')).hom with
              commutes' := fun s ↦
                congrArg (fun f : F.obj i₀ ⟶ F.obj i' ↦ f s)
                  (F.map_comp (homOfLE (hik.trans h)) (homOfLE h')).symm }
          αᵢ'ᵢ.toLinearMap.rTensor M₀ t = 0) := by
  classical
  let : Nonempty I := ⟨i₀⟩
  let : IsFiltered I := inferInstance
  let : PreservesColimit F (forget CommRingCat) := inferInstance
  let S := F.obj i₀
  let R := c.pt
  let : Algebra S R := (c.ι.app i₀).hom.toAlgebra
  let J := {i : I // k ≤ i}
  let : Nonempty J := ⟨⟨k, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let A : J → Type v := fun i ↦ F.obj i.val
  let : ∀ i, CommRing (A i) := fun i ↦ inferInstance
  let : ∀ i, Algebra S (A i) := fun i ↦ (F.map (homOfLE (hik.trans i.property))).hom.toAlgebra
  let f (i j : J) (h : i ≤ j) : A i →ₗ[S] A j :=
    AlgHom.toLinearMap
      { (F.map (homOfLE h)).hom with
        commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ F.obj j.val ↦ p s)
          (F.map_comp (homOfLE (hik.trans i.property)) (homOfLE h)).symm }
  let α (i : J) : A i →ₗ[S] R :=
    AlgHom.toLinearMap
      { (c.ι.app i.val).hom with
        commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ c.pt ↦ p s)
          (c.w (homOfLE (hik.trans i.property))) }
  have compat (i j : J) (h : i ≤ j) (a : A i) : α j (f i j h a) = α i a := by
    exact ConcreteCategory.congr_hom (c.w (homOfLE h)) a
  let : DirectedSystem A (fun {i j} h ↦ f i j h) :=
    { map_self := by
        intro i a
        change F.map (homOfLE (le_refl i.val)) a = a
        simp
      map_map := by
        intro i j k hij hjk a
        change F.map (homOfLE hjk) (F.map (homOfLE hij) a) =
          F.map (homOfLE (hij.trans hjk)) a
        exact (ConcreteCategory.congr_hom
          (F.map_comp (homOfLE hij) (homOfLE hjk)) a).symm }
  let g : Module.DirectLimit A f →ₗ[S] R :=
    Module.DirectLimit.lift S J A f α compat
  have ginj : Function.Injective g := by
    intro x y hxy
    obtain ⟨i, a, hx⟩ := Module.DirectLimit.exists_of x
    obtain ⟨j, b, hy⟩ := Module.DirectLimit.exists_of y
    rw [← hx, ← hy] at hxy ⊢
    simp only [g, Module.DirectLimit.lift_of] at hxy
    obtain ⟨k, u, v, he⟩ := Concrete.isColimit_exists_of_rep_eq F hc a b hxy
    let k' : J := ⟨k, i.property.trans (leOfHom u)⟩
    have he' : f i k' (leOfHom u) a = f j k' (leOfHom v) b := he
    rw [← Module.DirectLimit.of_f (f := f) (i := i) (j := k') (hij := leOfHom u),
      ← Module.DirectLimit.of_f (f := f) (i := j) (j := k') (hij := leOfHom v), he']
  have gsurj : Function.Surjective g := by
    intro r
    obtain ⟨i, a, ha⟩ := Concrete.isColimit_exists_rep F hc r
    obtain ⟨j, h₀j, hij⟩ := exists_ge_ge k i
    let j' : J := ⟨j, h₀j⟩
    refine ⟨Module.DirectLimit.of S J A f j' (F.map (homOfLE hij) a), ?_⟩
    simp only [g, Module.DirectLimit.lift_of]
    change c.ι.app j (F.map (homOfLE hij) a) = r
    exact (ConcreteCategory.congr_hom (c.w (homOfLE hij)) a).trans ha
  let E : Module.DirectLimit A f ≃ₗ[S] R := LinearEquiv.ofBijective g ⟨ginj, gsurj⟩
  let ft (i j : J) (h : i ≤ j) := (f i j h).rTensor M₀
  let e : Module.DirectLimit (fun i ↦ A i ⊗[S] M₀) ft ≃ₗ[S] R ⊗[S] M₀ :=
    (TensorProduct.directLimitLeft f M₀).symm.trans (E.rTensor M₀)
  have e_of (i : J) (t : A i ⊗[S] M₀) :
      e (Module.DirectLimit.of S J (fun i ↦ A i ⊗[S] M₀) ft i t) =
        (α i).rTensor M₀ t := by
    induction t using TensorProduct.inductionOn with
    | tmul a m =>
      dsimp only [e, ft]
      rw [LinearEquiv.trans_apply, TensorProduct.directLimitLeft_symm_of_tmul,
        LinearEquiv.rTensor_tmul, LinearMap.rTensor_tmul]
      change g (Module.DirectLimit.of S J A f i a) ⊗ₜ[S] m = α i a ⊗ₜ[S] m
      simp only [g, Module.DirectLimit.lift_of]
    | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
  let : DirectedSystem (fun i ↦ A i ⊗[S] M₀) (fun {i j} h ↦ ft i j h) :=
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
  dsimp only
  constructor
  · intro x
    obtain ⟨i, t, ht⟩ := Module.DirectLimit.exists_of (e.symm x)
    refine ⟨i.val, i.property, t, ?_⟩
    change (α i).rTensor M₀ t = x
    rw [← e_of, ht, e.apply_symm_apply]
  · intro i h t ht
    let i' : J := ⟨i, h⟩
    have hz : Module.DirectLimit.of S J (fun i ↦ A i ⊗[S] M₀) ft i' t = 0 := by
      apply e.injective
      rw [e_of, map_zero]
      exact ht
    obtain ⟨j, hij, he⟩ := Module.DirectLimit.of.zero_exact hz
    exact ⟨j.val, hij, he⟩

end TensorProduct
