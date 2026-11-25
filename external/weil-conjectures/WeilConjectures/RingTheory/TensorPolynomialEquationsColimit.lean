/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.MvPolynomial.Eval
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Data.Fintype.Order

/-! # Descent of finite systems of polynomial equations

Source: Stacks Project, Algebra, Tag 07RI, proof, lifting finitely many coefficients
and imposing finitely many identities.
(blueprint: lem-weil-pbc-tensor-polynomial-equations-colimit).
-/

@[expose] public section

universe u v w w'

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

private theorem finite_equations_descent
    {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    {A : J → Type*} [∀ i, CommRing (A i)] {R P : Type*} [CommRing R] [CommRing P]
    (t : ∀ i j, i ≤ j → A i →+* A j) (a : ∀ i, A i →+* R)
    (s : ∀ i, P →+* A i) (r : P →+* R)
    (ta : ∀ i j h x, a j (t i j h x) = a i x)
    (ts : ∀ i j h, (t i j h).comp (s i) = s j)
    (as : ∀ i, (a i).comp (s i) = r)
    (tt : ∀ i j k hij hjk x, t j k hjk (t i j hij x) = t i k (hij.trans hjk) x)
    (surj : ∀ x : R, ∃ i, ∃ y : A i, a i y = x)
    (zero : ∀ i (x : A i), a i x = 0 → ∃ j, ∃ h : i ≤ j, t i j h x = 0)
    {α β : Type*} [Finite α] [Finite β] (q : β → MvPolynomial α P)
    (x : α → R) (hx : ∀ b, MvPolynomial.eval₂Hom r x (q b) = 0) :
    ∃ i, ∃ y : α → A i, ∀ b, MvPolynomial.eval₂Hom (s i) y (q b) = 0 := by
  classical
  choose ix yx hyx using fun b ↦ surj (x b)
  obtain ⟨i, hi⟩ := Finite.exists_le ix
  let y : α → A i := fun b ↦ t (ix b) i (hi b) (yx b)
  have ay : (fun b ↦ a i (y b)) = x := by
    funext b
    exact (ta _ _ _ _).trans (hyx b)
  have hz (b : β) : a i (MvPolynomial.eval₂Hom (s i) y (q b)) = 0 := by
    rw [MvPolynomial.map_eval₂Hom, as, ay]
    exact hx b
  choose iz hiz hzero using fun b ↦ zero i _ (hz b)
  obtain ⟨k₀, hk₀⟩ := Finite.exists_le iz
  obtain ⟨k, hik, hk₀k⟩ := exists_ge_ge i k₀
  let z : α → A k := fun b ↦ t i k hik (y b)
  refine ⟨k, z, fun b ↦ ?_⟩
  have heval : MvPolynomial.eval₂Hom (s k) z (q b) =
      t i k hik (MvPolynomial.eval₂Hom (s i) y (q b)) := by
    rw [MvPolynomial.map_eval₂Hom, ts]
  rw [heval, ← tt i (iz b) k (hiz b) ((hk₀ b).trans hk₀k), hzero, map_zero]

private theorem tensor_polynomial_coeff
    {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] {σ : Type*} :
    (MvPolynomial.rTensorAlgEquiv (R := S) (S := A) (N := B) (σ := σ)).toRingHom.comp
        (Algebra.TensorProduct.includeRight.toRingHom :
          MvPolynomial σ B →+* A ⊗[S] MvPolynomial σ B) =
      MvPolynomial.map (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[S] B) := by
  apply RingHom.ext
  intro p
  apply MvPolynomial.ext
  intro d
  change AddMonoidAlgebra.coeff (MvPolynomial.rTensorAlgEquiv (1 ⊗ₜ[S] p)) d = _
  simp [MvPolynomial.coeff_rTensorAlgEquiv_tmul, MvPolynomial.coeff_map]

private theorem tensor_map_linear
    {S A B P : Type*} [CommRing S] [CommRing A] [CommRing B] [CommRing P]
    [Algebra S A] [Algebra S B] [Algebra S P] (f : A →ₐ[S] B) (x : A ⊗[S] P) :
    Algebra.TensorProduct.map f (AlgHom.id S P) x = f.toLinearMap.rTensor P x := by
  induction x using TensorProduct.inductionOn with
  | tmul a p => rfl
  | add x y hx hy => simp [hx, hy]

/-- A finite system of polynomial equations over a fixed polynomial coefficient algebra
has a solution after tensor base change to a directed colimit only if it has a solution
at a stage above the fixed base stage.

Source: Stacks Project, Algebra, Tag 07RI (lemma-colimit-etale), proof,
lines 47654-47662; the finite-equation step, abstracted from the inverse identities.
(blueprint: lem-weil-pbc-tensor-polynomial-equations-colimit).

Proof: put P₀ = B₀[x₁,...,x_n]. The natural polynomial tensor equivalence identifies
A_i tensor P₀ with (A_i tensor B₀)[x], and likewise at the colimit. Apply elementwise
base-change descent to the finitely many entries of the solution. Choose a common
upper bound of their stages and i₀, and transport the entries there. The coefficient
maps from P₀ commute with all transition maps. Evaluation of a polynomial commutes
with a ring map (check constants and variables, addition and multiplication).
Consequently each equation evaluated at this tuple has zero image in the colimit.
Apply eventual vanishing to these finitely many evaluated differences and choose a
common later stage. Transport the tuple again: evaluation compatibility makes every
equation zero there. Empty variable or equation sets require no representatives or
vanishing conditions, respectively; use i₀ as the initial upper bound. No finite
presentation of B₀ or bound on the degrees of the lifted entries is used. -/
theorem exists_stage_tensorPolynomialEquations
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ : Type v) [CommRing B₀] [Algebra (F.obj i₀) B₀]
    (n : ℕ) {α : Type w} {β : Type w'} [Finite α] [Finite β]
    (q : β → MvPolynomial α (MvPolynomial (Fin n) B₀)) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (colimit.ι F i₀).hom.toAlgebra
    (∃ x : α → MvPolynomial (Fin n) ((colimit F : CommRingCat.{u}) ⊗[F.obj i₀] B₀),
      ∀ b, MvPolynomial.eval₂Hom
        (MvPolynomial.map (Algebra.TensorProduct.includeRight.toRingHom :
          B₀ →+* (colimit F : CommRingCat.{u}) ⊗[F.obj i₀] B₀)) x (q b) = 0) →
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
      ∃ x : α → MvPolynomial (Fin n) (F.obj i ⊗[F.obj i₀] B₀),
        ∀ b, MvPolynomial.eval₂Hom
          (MvPolynomial.map (Algebra.TensorProduct.includeRight.toRingHom :
            B₀ →+* F.obj i ⊗[F.obj i₀] B₀)) x (q b) = 0 := by
  classical
  let S := F.obj i₀
  let R := colimit F
  let : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
  let P := MvPolynomial (Fin n) B₀
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let A : J → Type u := fun i ↦ F.obj i.val
  let : ∀ i, CommRing (A i) := fun i ↦ inferInstance
  let : ∀ i, Algebra S (A i) := fun i ↦ (F.map (homOfLE i.property)).hom.toAlgebra
  let f (i j : J) (h : i ≤ j) : A i →ₐ[S] A j :=
    { (F.map (homOfLE h)).hom with
      commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ F.obj j.val ↦ p s)
        (F.map_comp (homOfLE i.property) (homOfLE h)).symm }
  let a (i : J) : A i →ₐ[S] R :=
    { (colimit.ι F i.val).hom with
      commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ colimit F ↦ p s)
        (colimit.w F (homOfLE i.property)) }
  let t (i j : J) (h : i ≤ j) : A i ⊗[S] P →+* A j ⊗[S] P :=
    (Algebra.TensorProduct.map (f i j h) (AlgHom.id S P)).toRingHom
  let ar (i : J) : A i ⊗[S] P →+* R ⊗[S] P :=
    (Algebra.TensorProduct.map (a i) (AlgHom.id S P)).toRingHom
  let s (i : J) : P →+* A i ⊗[S] P := Algebra.TensorProduct.includeRight.toRingHom
  let r : P →+* R ⊗[S] P := Algebra.TensorProduct.includeRight.toRingHom
  have ta (i j : J) (h : i ≤ j) (x : A i ⊗[S] P) : ar j (t i j h x) = ar i x := by
    induction x using TensorProduct.inductionOn with
    | tmul x p =>
      change ((colimit.ι F j.val) (F.map (homOfLE h) x)) ⊗ₜ[S] p =
        (colimit.ι F i.val x) ⊗ₜ[S] p
      exact congrArg (fun z : R ↦ z ⊗ₜ[S] p)
        (ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) x)
    | add x y hx hy => simp [hx, hy]
  have ts (i j : J) (h : i ≤ j) : (t i j h).comp (s i) = s j := by
    apply RingHom.ext
    intro p
    change Algebra.TensorProduct.map (f i j h) (AlgHom.id S P) (1 ⊗ₜ[S] p) = 1 ⊗ₜ[S] p
    simp
  have ars (i : J) : (ar i).comp (s i) = r := by
    apply RingHom.ext
    intro p
    change Algebra.TensorProduct.map (a i) (AlgHom.id S P) (1 ⊗ₜ[S] p) = 1 ⊗ₜ[S] p
    simp
  have tt (i j k : J) (hij : i ≤ j) (hjk : j ≤ k) (x : A i ⊗[S] P) :
      t j k hjk (t i j hij x) = t i k (hij.trans hjk) x := by
    induction x using TensorProduct.inductionOn with
    | tmul x p =>
      change (F.map (homOfLE hjk) (F.map (homOfLE hij) x)) ⊗ₜ[S] p =
        (F.map (homOfLE (hij.trans hjk)) x) ⊗ₜ[S] p
      exact congrArg (fun z : A k ↦ z ⊗ₜ[S] p)
        (ConcreteCategory.congr_hom (F.map_comp (homOfLE hij) (homOfLE hjk)) x).symm
    | add x y hx hy => simp [hx, hy]
  have hd := TensorProduct.directedColimitBaseChangeElementwise F i₀ P
  have surj (x : R ⊗[S] P) : ∃ i : J, ∃ y : A i ⊗[S] P, ar i y = x := by
    obtain ⟨i, hi, y, hy⟩ := hd.1 x
    refine ⟨⟨i, hi⟩, y, ?_⟩
    exact (tensor_map_linear _ _).trans hy
  have zero (i : J) (x : A i ⊗[S] P) (hx : ar i x = 0) :
      ∃ j : J, ∃ h : i ≤ j, t i j h x = 0 := by
    have hx' : (a i).toLinearMap.rTensor P x = 0 := by
      rw [← tensor_map_linear]
      exact hx
    obtain ⟨j, hij, hz⟩ := hd.2 i.val i.property x hx'
    refine ⟨⟨j, i.property.trans hij⟩, hij, ?_⟩
    exact (tensor_map_linear _ _).trans hz
  intro hx
  obtain ⟨x, hx⟩ := hx
  let er := MvPolynomial.rTensorAlgEquiv (R := S) (S := R) (N := B₀) (σ := Fin n)
  let x' : α → R ⊗[S] P := fun b ↦ er.symm (x b)
  have hx' (b : β) : MvPolynomial.eval₂Hom r x' (q b) = 0 := by
    apply er.injective
    change er.toRingHom (MvPolynomial.eval₂Hom r x' (q b)) = er.toRingHom 0
    rw [map_zero, MvPolynomial.map_eval₂Hom]
    change MvPolynomial.eval₂Hom (er.toRingHom.comp r) (fun b ↦ er (x' b)) (q b) = 0
    rw [tensor_polynomial_coeff]
    simpa [x'] using hx b
  obtain ⟨i, y, hy⟩ := finite_equations_descent t ar s r ta ts ars tt surj zero q x' hx'
  let ei := MvPolynomial.rTensorAlgEquiv (R := S) (S := A i) (N := B₀) (σ := Fin n)
  refine ⟨i.val, i.property, (fun b ↦ ei (y b)), fun b ↦ ?_⟩
  have hh := congrArg ei (hy b)
  change ei.toRingHom (MvPolynomial.eval₂Hom (s i) y (q b)) = ei.toRingHom 0 at hh
  rw [map_zero, MvPolynomial.map_eval₂Hom] at hh
  change MvPolynomial.eval₂Hom (ei.toRingHom.comp (s i)) (fun b ↦ ei (y b)) (q b) = 0 at hh
  rw [tensor_polynomial_coeff] at hh
  exact hh

end Algebra
