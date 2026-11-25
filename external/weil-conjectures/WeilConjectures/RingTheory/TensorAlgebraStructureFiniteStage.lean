/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise
import Mathlib.Data.Finset.Order

/-! # Descending an algebra structure on a tensor colimit

Source: Stacks Project, Algebra, Tags 00QO and 00DD.
(blueprint: lem-weil-pbc-tensor-algebra-structure-finite-stage)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- A finitely presented integer algebra acting on a tensor colimit acts at a stage.

Source: Stacks Project, Algebra, Tag 00QO (lemma-characterize-finite-presentation),
and Tag 00DD (tensor products commute with colimits), used in Tag 02JO (3).
(blueprint: lem-weil-pbc-tensor-algebra-structure-finite-stage)

Proof: restrict F to the nonempty directed upper tail of i₀. Define the
canonical tensor ring maps and transition maps; tensor induction proves their
compatibility and composition laws. The elementwise base-change lemma gives
representatives and eventual vanishing. Choose a finite polynomial presentation
π : ℤ[X₁,...,Xₙ] → P with finitely generated kernel. Represent the images of
its generators at stages and move them to one upper stage. Evaluate polynomials
there. Its composite with the canonical map equals algebraMap P B composed
with π, by polynomial extensionality. Each kernel generator therefore evaluates
to an element that is zero in the limit. Move to a common stage where all these
elements vanish; transition composition ensures that the evaluation kills the
whole kernel. Descend it through the surjection π using liftOfSurjective. The
resulting ring map P → Bᵢ defines aPi, and its composite with Bᵢ → B equals
algebraMap P B by surjectivity of π, yielding μB as a P-algebra map. Nonempty
upper tails supply bounds even when the finite generator or relation sets are
empty. No injectivity or nonzero-ring assumption is used.
-/
theorem exists_tensor_algebra_structure_finite_stage
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) [CommRing B₀] [Algebra (F.obj i₀) B₀]
    (P : Type y) [CommRing P] [Algebra.FinitePresentation ℤ P]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀)) :
    ∃ (i : I) (hi : i₀ ≤ i),
    letI := (colimit.ι F i₀).hom.toAlgebra
    letI := (F.map (homOfLE hi)).hom.toAlgebra
    let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
      { (colimit.ι F i).hom with
        commutes' := fun s ↦
          congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
    ∃ (aPi : Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀)),
      letI := aPi
      letI := aP
      ∃ (μB : (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P]
          (↥(colimit F) ⊗[F.obj i₀] B₀)),
        μB.toRingHom =
          (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom
    := by
  classical
  let := (colimit.ι F i₀).hom.toAlgebra
  let := aP
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let B (i : J) :=
    let := (F.map (homOfLE i.property)).hom.toAlgebra
    ↥(F.obj i.val) ⊗[F.obj i₀] B₀
  let : ∀ i, CommRing (B i) := fun i ↦ by dsimp [B]; infer_instance
  let α (i : J) :
      let := (F.map (homOfLE i.property)).hom.toAlgebra
      F.obj i.val →ₐ[F.obj i₀] ↥(colimit F) :=
    let := (F.map (homOfLE i.property)).hom.toAlgebra
    { (colimit.ι F i.val).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
        (colimit.w F (homOfLE i.property)) }
  let μ (i : J) : B i →+* (↥(colimit F) ⊗[F.obj i₀] B₀) :=
    let := (F.map (homOfLE i.property)).hom.toAlgebra
    (Algebra.TensorProduct.map (α i) (AlgHom.id (F.obj i₀) B₀)).toRingHom
  let t (i j : J) (h : i ≤ j) : B i →+* B j :=
    let := (F.map (homOfLE i.property)).hom.toAlgebra
    let := (F.map (homOfLE j.property)).hom.toAlgebra
    let β : F.obj i.val →ₐ[F.obj i₀] F.obj j.val :=
      { (F.map (homOfLE h)).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
          (F.map_comp (homOfLE i.property) (homOfLE h)).symm }
    (Algebra.TensorProduct.map β (AlgHom.id (F.obj i₀) B₀)).toRingHom
  have compat (i j : J) (h : i ≤ j) : (μ j).comp (t i j h) = μ i := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      dsimp [μ, t]
      exact congrArg (fun a ↦ a ⊗ₜ[F.obj i₀] b)
        (ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) a)
    | add z u hz hu => simpa only [map_add] using congrArg₂ (· + ·) hz hu
  have trans (i j k : J) (hij : i ≤ j) (hjk : j ≤ k) :
      (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk) := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      let := (F.map (homOfLE k.property)).hom.toAlgebra
      dsimp [t]
      exact congrArg (fun a ↦ a ⊗ₜ[F.obj i₀] b)
        (ConcreteCategory.congr_hom (F.map_comp (homOfLE hij) (homOfLE hjk)) a).symm
    | add z u hz hu => simpa only [map_add] using congrArg₂ (· + ·) hz hu
  have rep (z : ↥(colimit F) ⊗[F.obj i₀] B₀) : ∃ i : J, ∃ x : B i, μ i x = z := by
    obtain ⟨i, hi, x, hx⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i₀ B₀).1 z
    exact ⟨⟨i, hi⟩, x, hx⟩
  have vanish (i : J) (z : B i) (hz : μ i z = 0) :
      ∃ (j : J) (h : i ≤ j), t i j h z = 0 := by
    obtain ⟨j, hij, he⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i₀ B₀).2 i.val i.property z hz
    exact ⟨⟨j, i.property.trans hij⟩, hij, he⟩
  obtain ⟨n, π, hπ, s, hs⟩ := Algebra.FinitePresentation.out (R := ℤ) (A := P)
  choose l x hx using fun k : Fin n ↦ rep (algebraMap P _ (π (MvPolynomial.X k)))
  obtain ⟨i, hi⟩ := Finset.exists_le (Finset.univ.image l)
  have hli (k : Fin n) : l k ≤ i := hi _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  let p : MvPolynomial (Fin n) ℤ →+* B i :=
    MvPolynomial.eval₂Hom (Int.castRingHom _) (fun k ↦ t (l k) i (hli k) (x k))
  have hp : (μ i).comp p = (algebraMap P _).comp π.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [p]
    · intro k
      simp only [RingHom.comp_apply, p, MvPolynomial.eval₂Hom_X', AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom]
      change μ i (t (l k) i (hli k) (x k)) = algebraMap P _ (π (MvPolynomial.X k))
      exact (RingHom.congr_fun (compat (l k) i (hli k)) (x k)).trans (hx k)
  have relations (r : s) : ∃ (j : J) (h : i ≤ j), t i j h (p r) = 0 := by
    apply vanish
    have hr : π r = 0 := hs.le (Ideal.subset_span r.property)
    exact (RingHom.congr_fun hp r).trans (by simp [hr])
  choose j hij hj using relations
  obtain ⟨k, hk⟩ := Finset.exists_le (insert i (Finset.univ.image j))
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  have hjk (r : s) : j r ≤ k := hk _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩))
  let pk := (t i k hik).comp p
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker pk := by
    rw [← hs, Ideal.span_le]
    intro r hr
    change t i k hik (p r) = 0
    let r' : s := ⟨r, hr⟩
    rw [← trans i (j r') k (hij r') (hjk r')]
    change t (j r') k (hjk r') (t i (j r') (hij r') (p r')) = 0
    rw [hj, map_zero]
  let pP : P →+* B k := RingHom.liftOfSurjective π.toRingHom hπ ⟨pk, hker⟩
  have hfactor : (μ k).comp pP = algebraMap P _ := by
    apply RingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := hπ z
    change μ k (pP (π z)) = algebraMap P _ (π z)
    rw [show pP (π z) = pk z from
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ _]
    change μ k (t i k hik (p z)) = algebraMap P _ (π z)
    exact (RingHom.congr_fun (compat i k hik) (p z)).trans (RingHom.congr_fun hp z)
  let := pP.toAlgebra
  let μP : B k →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] B₀) :=
    { μ k with commutes' := fun r ↦ RingHom.congr_fun hfactor r }
  exact ⟨k.val, k.property, pP.toAlgebra, μP, rfl⟩

end RingHom
