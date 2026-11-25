/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise

/-!
# Descent of a finite family of integral tensor elements

Source: Stacks Project, Algebra, Tag 07RG, proof of Lemma 10.168.3.
-/

@[expose] public section

universe u v t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

private theorem integral_at_stage
    {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (B C : J → Type*) [∀ j, CommRing (B j)] [∀ j, CommRing (C j)]
    {Bcolim Ccolim : Type*} [CommRing Bcolim] [CommRing Ccolim]
    (bmap : ∀ {i j : J}, i ≤ j → B i →+* B j)
    (cmap : ∀ {i j : J}, i ≤ j → C i →+* C j)
    (bι : ∀ j, B j →+* Bcolim) (cι : ∀ j, C j →+* Ccolim)
    (φ : ∀ j, B j →+* C j) (φcolim : Bcolim →+* Ccolim)
    (bcompat : ∀ {i j} (h : i ≤ j) b, bι j (bmap h b) = bι i b)
    (φcompat : ∀ j b, cι j (φ j b) = φcolim (bι j b))
    (φtrans : ∀ {i j} (h : i ≤ j) b, cmap h (φ i b) = φ j (bmap h b))
    (rep : ∀ b : Bcolim, ∃ j, ∃ t : B j, bι j t = b)
    (zero : ∀ j (z : C j), cι j z = 0 → ∃ k, ∃ h : j ≤ k, cmap h z = 0)
    (x : ∀ j, C j) (xcolim : Ccolim)
    (hx : ∀ j, cι j (x j) = xcolim)
    (htrans : ∀ {i j} (h : i ≤ j), cmap h (x i) = x j)
    (hi : φcolim.IsIntegralElem xcolim) : ∃ j, (φ j).IsIntegralElem (x j) := by
  classical
  obtain ⟨p, hp, heval⟩ := hi
  choose stage coeff hcoeff using fun k : Fin p.natDegree ↦ rep (p.coeff k)
  obtain ⟨j, hj⟩ := (Finset.univ.image stage).exists_le
  have hstage (k : Fin p.natDegree) : stage k ≤ j :=
    hj _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  let q : Polynomial (B j) := Polynomial.X ^ p.natDegree +
    ∑ k : Fin p.natDegree, Polynomial.C (bmap (hstage k) (coeff k)) * Polynomial.X ^ (k : ℕ)
  have hq : q.Monic :=
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hqmap : q.map (bι j) = p := by
    rw [hp.as_sum]
    simp only [q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, bcompat, hcoeff]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun k ↦ Polynomial.C (p.coeff k) * Polynomial.X ^ k) p.natDegree
  have hvanish : cι j (q.eval₂ (φ j) (x j)) = 0 := by
    have hcomm : (cι j).comp (φ j) = φcolim.comp (bι j) := by
      ext b
      exact φcompat j b
    rw [Polynomial.hom_eval₂, hcomm, ← Polynomial.eval₂_map, hx, hqmap]
    exact heval
  obtain ⟨k, hjk, hk⟩ := zero j (q.eval₂ (φ j) (x j)) hvanish
  refine ⟨k, q.map (bmap hjk), hq.map _, ?_⟩
  have hcomm : (cmap hjk).comp (φ j) = (φ k).comp (bmap hjk) := by
    ext b
    exact φtrans hjk b
  rw [Polynomial.eval₂_map, ← htrans hjk, ← hcomm, ← Polynomial.hom_eval₂]
  exact hk

/-- A finite family of elements integral after tensor base change to a directed colimit
is integral after base change to one common stage.
Source: Stacks Project, Algebra, Tag 07RG, the coefficient-lifting and eventual-zero
paragraphs of the proof of Lemma 10.168.3.
(blueprint: lem-weil-pbc-integral-tensor-generators-colimit-descent).

Proof: For each x in s choose a monic polynomial p over colimit F tensor B₀ annihilating
1 tensor x. The coefficients below p.natDegree lift to stages by
directedColimitBaseChangeElementwise for B₀, part (1). Choose one upper bound of these
stages in the directed upper tail above i₀ and transport the coefficients there.
Construct X^p.natDegree plus the sum of the lifted lower terms. The degree bound for this
sum makes the polynomial monic, even when p.natDegree is zero. Tensor transition maps
commute with the maps induced by φ₀ and fix 1 tensor x,
as checked on pure tensors, so evaluating these polynomials maps to zero at the colimit.
Part (2) of directedColimitBaseChangeElementwise for C₀ kills each evaluation at a later
stage. Choose a common upper bound for this finite family of later stages, and transport
all coefficients there. The transported monic polynomials still annihilate 1 tensor x,
by multiplicativity and compatibility of the transition maps. These polynomials witness
the required integrality. For an empty family choose i₀; no nontriviality assumption on
any ring is needed. -/
theorem exists_integral_tensor_generators_of_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ : Type v) (C₀ : Type t) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (s : Finset C₀) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
    (∀ x ∈ s,
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).toRingHom.IsIntegralElem
          ((1 : (colimit F : CommRingCat.{u})) ⊗ₜ[F.obj i₀] x)) →
      ∃ (i : I) (h : i₀ ≤ i),
        letI : Algebra (F.obj i₀) (F.obj i) :=
          (CommRingCat.Hom.hom (F.map (homOfLE h))).toAlgebra
        ∀ x ∈ s,
          (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).toRingHom.IsIntegralElem
            ((1 : F.obj i) ⊗ₜ[F.obj i₀] x) := by
  classical
  let S := F.obj i₀
  let R := colimit F
  let : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
  intro hint
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let T : J → Type u := fun j ↦ F.obj j.val
  let : ∀ j, CommRing (T j) := fun j ↦ inferInstance
  let : ∀ j, Algebra S (T j) := fun j ↦ (F.map (homOfLE j.property)).hom.toAlgebra
  let trans (i j : J) (h : i ≤ j) : T i →ₐ[S] T j :=
    { (F.map (homOfLE h)).hom with
      commutes' := fun a ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f a)
        (F.map_comp (homOfLE i.property) (homOfLE h)).symm }
  let incl (j : J) : T j →ₐ[S] R :=
    { (colimit.ι F j.val).hom with
      commutes' := fun a ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f a)
        (colimit.w F (homOfLE j.property)) }
  let B (j : J) := T j ⊗[S] B₀
  let C (j : J) := T j ⊗[S] C₀
  let bmap {i j : J} (h : i ≤ j) : B i →+* B j :=
    (Algebra.TensorProduct.map (trans i j h) (AlgHom.id S B₀)).toRingHom
  let cmap {i j : J} (h : i ≤ j) : C i →+* C j :=
    (Algebra.TensorProduct.map (trans i j h) (AlgHom.id S C₀)).toRingHom
  let bι (j : J) : B j →+* (R ⊗[S] B₀) :=
    (Algebra.TensorProduct.map (incl j) (AlgHom.id S B₀)).toRingHom
  let cι (j : J) : C j →+* (R ⊗[S] C₀) :=
    (Algebra.TensorProduct.map (incl j) (AlgHom.id S C₀)).toRingHom
  let φ (j : J) : B j →+* C j :=
    (Algebra.TensorProduct.map (AlgHom.id S (T j)) φ₀).toRingHom
  let φcolim : (R ⊗[S] B₀) →+* (R ⊗[S] C₀) :=
    (Algebra.TensorProduct.map (AlgHom.id S R) φ₀).toRingHom
  have bcompat {i j : J} (h : i ≤ j) (b : B i) :
      bι j (bmap h b) = bι i b := by
    induction b using TensorProduct.inductionOn with
    | tmul t b =>
      change incl j (trans i j h t) ⊗ₜ[S] b = incl i t ⊗ₜ[S] b
      congr 1
      exact ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) t
    | add x y hx hy => simp only [map_add, hx, hy]
  have φcompat (j : J) (b : B j) : cι j (φ j b) = φcolim (bι j b) := by
    induction b using TensorProduct.inductionOn with
    | tmul t b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have φtrans {i j : J} (h : i ≤ j) (b : B i) :
      cmap h (φ i b) = φ j (bmap h b) := by
    induction b using TensorProduct.inductionOn with
    | tmul t b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have rep (b : R ⊗[S] B₀) : ∃ j, ∃ t : B j, bι j t = b := by
    obtain ⟨i, h, t, ht⟩ := (TensorProduct.directedColimitBaseChangeElementwise F i₀ B₀).1 b
    exact ⟨⟨i, h⟩, t, ht⟩
  have zero (j : J) (z : C j) (hz : cι j z = 0) :
      ∃ k, ∃ h : j ≤ k, cmap h z = 0 := by
    obtain ⟨k, h, hk⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i₀ C₀).2 j.val j.property z hz
    exact ⟨⟨k, j.property.trans h⟩, h, hk⟩
  have hsingle (x : C₀) (hx : x ∈ s) :
      ∃ j, (φ j).IsIntegralElem ((1 : T j) ⊗ₜ[S] x) := by
    apply integral_at_stage B C bmap cmap bι cι φ φcolim bcompat φcompat φtrans rep zero
      (fun j ↦ (1 : T j) ⊗ₜ[S] x) ((1 : R) ⊗ₜ[S] x)
    · intro j
      change incl j 1 ⊗ₜ[S] x = (1 : R) ⊗ₜ[S] x
      rw [map_one]
    · intro i j h
      change trans i j h 1 ⊗ₜ[S] x = (1 : T j) ⊗ₜ[S] x
      rw [map_one]
    · exact hint x hx
  choose stage hstage using fun x : s ↦ hsingle x.val x.property
  obtain ⟨j, hj⟩ := (Finset.univ.image stage).exists_le
  refine ⟨j.val, j.property, ?_⟩
  intro x hx
  let x' : s := ⟨x, hx⟩
  have hle : stage x' ≤ j := hj _ (Finset.mem_image.mpr ⟨x', Finset.mem_univ _, rfl⟩)
  have hi := (hstage x').map (cmap hle)
  have heq : (cmap hle).comp (φ (stage x')) = (φ j).comp (bmap hle) := by
    exact RingHom.ext (φtrans hle)
  rw [heq] at hi
  have ht : cmap hle ((1 : T (stage x')) ⊗ₜ[S] x) = (1 : T j) ⊗ₜ[S] x := by
    change trans (stage x') j hle 1 ⊗ₜ[S] x = (1 : T j) ⊗ₜ[S] x
    rw [map_one]
  rw [ht] at hi
  exact hi.of_comp

end RingHom
