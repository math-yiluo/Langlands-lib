/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Maps

import WeilConjectures.RingTheory.ColimitFlatRelationDescentElementwise

/-!
# Descent of finite subsets of an ideal multiplication kernel

Source: Stacks Project, Algebra, Tag 00R6, tensor-colimit descent paragraph.
(blueprint: lem-weil-pbc-finite-ideal-kernel-descent)
-/

@[expose] public section

universe u v w z
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace RingTheory

private theorem exists_ideal_tensor_map
    {R : Type v} {S : Type w} {M : Type z} {P : Type u}
    [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup P]
    [Module R M] [Module S P]
    (α : R →+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : ∀ a ∈ I, α a ∈ J) (η : M →+ P)
    (hη : ∀ r x, η (r • x) = α r • η x) :
    ∃ θ : I ⊗[R] M →+ J ⊗[S] P,
      ∀ a x, θ (a ⊗ₜ[R] x) = (⟨α a, hIJ a a.property⟩ : J) ⊗ₜ[S] η x := by
  let g : I →ₛₗ[α] J :=
    { toFun := fun a ↦ ⟨α a, hIJ a a.property⟩
      map_add' := fun a b ↦ by ext; simp
      map_smul' := fun r a ↦ by ext; simp [smul_eq_mul] }
  let h : M →ₛₗ[α] P :=
    { η with map_smul' := hη }
  exact ⟨(TensorProduct.map g h).toAddMonoidHom, fun _ _ ↦ rfl⟩

/-- Any finite subset of an ideal multiplication kernel dies at a common later stage.
The forgetful functor to sets preserves the specified colimit of the first ring diagram.
Source: Stacks Project, Algebra, Tag 00R6, descent of finitely many generators xi.
(blueprint: lem-weil-pbc-finite-ideal-kernel-descent)

Proof: Assemble single-element descent from finite-relation factorization for
every element of the finite subset, keeping the independent carrier universes.
Directedness gives an index l above i and all the finitely many witness stages;
for the empty subset l=i suffices. Construct the canonical ideal-tensor map to
l from the semilinear ring and module transitions. For each witness stage j,
the ideal I A_j maps to I A_l since extension of ideals commutes with ring-map
composition. The induced tensor transition from j to l composes with the
single-element witness map to give the canonical map from i to l: on pure
tensors this is functoriality of A and N and equality of parallel morphisms
in the preorder, and tensor induction gives equality on every tensor.
Thus an element killed at its witness stage remains zero at l. The canonical
map to l kills all elements of the finite subset and has the required formula.
No flatness argument is repeated here and no generation assumption is used. -/
theorem exists_stage_finite_ideal_kernel_vanishes
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [PreservesColimit A (forget CommRingCat.{v})]
    [∀ i, Module (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z}))
    (i : Λ) (I : Ideal (A.obj i)) :
    letI := Module.compHom (N.obj i) (φ i)
    ∀ (s : Finset (I ⊗[A.obj i] N.obj i)),
      (∀ k ∈ s,
        TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype) k = 0) →
    ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj i) (φ i)
      letI := Module.compHom (N.obj j) (φ j)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧
        (∀ k ∈ s, θ k = 0)  := by
  classical
  let := Module.compHom (N.obj i) (φ i)
  intro s hs
  have hR (a b : Λ) (g : a ⟶ b) (r : A.obj a) (x : N.obj a) :
      (N.map g).hom ((φ a) r • x) =
        (φ b) ((A.map g).hom r) • (N.map g).hom x := by
    rw [hscalar]
    exact congrArg (fun c ↦ c • (N.map g).hom x) (DFunLike.congr_fun (hcomm a b g) r)
  have hpoint : ∀ k : {k // k ∈ s}, ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj j) (φ j)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧ θ k = 0 := by
    intro k
    have hk := hs k k.property
    obtain ⟨n, a, x, heq⟩ := TensorProduct.exists_sum_tmul_eq (k : I ⊗[A.obj i] N.obj i)
    have hrel : ∑ p, (φ i) (a p) • x p = 0 := by
      change ∑ p, (a p : A.obj i) • x p = 0
      rw [heq, map_sum] at hk
      simpa only [TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply,
        Submodule.subtype_apply] using hk
    obtain ⟨j, f, m, c, y, hx, hc⟩ :=
      exists_stage_flat_relation_factorization_of_preserves
      A B N φ hcomm hscalar ψ hψ hlimitScalar hflat i (fun p ↦ (a p : A.obj i)) x hrel
    let := Module.compHom (N.obj j) (φ j)
    obtain ⟨θ, ht⟩ := exists_ideal_tensor_map (A.map f).hom I
      (I.map (A.map f).hom) (fun a ha ↦ Ideal.mem_map_of_mem _ ha) (N.map f).hom (hR i j f)
    refine ⟨j, f, θ, ht, ?_⟩
    let b : Fin n → I.map (A.map f).hom :=
      fun p ↦ ⟨(A.map f).hom (a p), Ideal.mem_map_of_mem _ (a p).property⟩
    rw [heq, map_sum]
    simp only [ht, hx]
    change ∑ p, b p ⊗ₜ[A.obj j] (∑ q, (φ j) (c p q) • y q) = 0
    have hbalance (p : Fin n) (q : Fin m) :
        b p ⊗ₜ[A.obj j] ((φ j) (c p q) • y q) =
          (c p q • b p) ⊗ₜ[A.obj j] y q := by
      exact (TensorProduct.smul_tmul (c p q) (b p) (y q)).symm
    simp only [TensorProduct.tmul_sum, hbalance]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q _
    rw [← TensorProduct.sum_tmul]
    have hzero : ∑ p, c p q • b p = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
      change ∑ p, c p q * (A.map f).hom (a p) = 0
      simpa only [mul_comm] using hc q
    rw [hzero, TensorProduct.zero_tmul]
  choose j f θ ht hz using hpoint
  have hb : ∀ t : Finset Λ, ∃ l : Λ, i ≤ l ∧ ∀ a ∈ t, a ≤ l := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨i, le_rfl, by simp⟩
    | @insert a t _ ih =>
      obtain ⟨l, hil, hl⟩ := ih
      obtain ⟨m, ham, hlm⟩ := exists_ge_ge a l
      refine ⟨m, hil.trans hlm, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ham
      · exact (hl b hb).trans hlm
  obtain ⟨l, hil, hl⟩ := hb (s.attach.image j)
  let fl : i ⟶ l := homOfLE hil
  let := Module.compHom (N.obj l) (φ l)
  obtain ⟨Θ, hΘ⟩ := exists_ideal_tensor_map (A.map fl).hom I
    (I.map (A.map fl).hom) (fun a ha ↦ Ideal.mem_map_of_mem _ ha)
    (N.map fl).hom (hR i l fl)
  refine ⟨l, fl, Θ, hΘ, ?_⟩
  intro k hk
  let e : {k // k ∈ s} := ⟨k, hk⟩
  have hjl : j e ≤ l := hl (j e) (Finset.mem_image.mpr ⟨e, by simp, rfl⟩)
  let g : j e ⟶ l := homOfLE hjl
  let := Module.compHom (N.obj (j e)) (φ (j e))
  have hf : f e ≫ g = fl := Subsingleton.elim _ _
  have hα : (A.map g).hom.comp (A.map (f e)).hom = (A.map fl).hom := by
    rw [← hf, A.map_comp]
    rfl
  have hJ : (I.map (A.map (f e)).hom).map (A.map g).hom = I.map (A.map fl).hom := by
    rw [Ideal.map_map, hα]
  obtain ⟨δ, hδ⟩ := exists_ideal_tensor_map (A.map g).hom
    (I.map (A.map (f e)).hom) (I.map (A.map fl).hom)
    (fun a ha ↦ by rw [← hJ]; exact Ideal.mem_map_of_mem _ ha)
    (N.map g).hom (hR (j e) l g)
  have hcomp : ∀ x, δ (θ e x) = Θ x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      rw [ht, hδ, hΘ]
      congr 1
      · apply Subtype.ext
        exact DFunLike.congr_fun hα (a : A.obj i)
      · have heq : (N.map g).hom.comp (N.map (f e)).hom = (N.map fl).hom := by
          rw [← hf, N.map_comp]
          rfl
        exact DFunLike.congr_fun heq x
  rw [← hcomp k, hz e, map_zero]


end RingTheory
