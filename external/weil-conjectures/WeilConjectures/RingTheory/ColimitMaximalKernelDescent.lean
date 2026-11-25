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
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.RingTheory.FiniteTensorKernelGenerators
import WeilConjectures.RingTheory.FiniteIdealKernelDescent

/-!
# Descent of the maximal-ideal multiplication kernel

Source: Stacks Project, Algebra, Tag 00R6 (lemma-colimit-eventually-flat),
proof of eventual vanishing of the maximal-ideal multiplication kernel.
(blueprint: lem-weil-pbc-colimit-maximal-kernel-descent)
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTheory

/-- The maximal-ideal multiplication kernel at any fixed stage dies after base change
at a later stage. The forgetful functor to sets preserves the colimit of `A`.
Source: Stacks Project, Algebra, Tag 00R6, proof preceding the
application of Tag 00MO; ideal-tensor description in Remark 00M6.
(blueprint: lem-weil-pbc-colimit-maximal-kernel-descent)

Proof: Restrict to the cofinal directed set above `i`. The maximal ideal of `A_i`
is finite since `A_i` is Noetherian. Its tensor product with `N_i` is finite over
`B_i`, and the multiplication kernel is finite since `B_i` is Noetherian. Choose
finitely many generators. Regard all later rings and modules as `A_i`-modules.
Their colimits remain the given ring and additive-group colimits, by the
representative and eventual-equality criteria for filtered colimits. Tensoring
with the maximal ideal commutes with these colimits. Write `s` for multiplication
from the maximal ideal tensored with the limit ring to the limit ring. Flatness
of the limit module implies that every image of a chosen kernel generator is a
finite sum of elements of `ker s` tensored with limit-module elements, using
exactness of tensoring the sequence `ker s → domain s → codomain s`.
Descend those finitely many elements to a common stage. Descend the equations
`s(k)=0`, and then the expressions for the chosen generators, to one later
stage using eventual vanishing in the ring and module colimits. Mapping to the
extended ideal tensored with the stage module kills each expression: the image
of `k` is `s(k)`, which is zero. The canonical map is semilinear over `B_i`, so
it kills the whole kernel. This gives exactly `θ` and its
pure-tensor formula and kernel vanishing. No localization or tensor base-change
hypothesis, or locality of the transition maps, is used in this descent argument.
-/
theorem exists_stage_maximal_kernel_vanishes
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [PreservesColimit A (forget CommRingCat.{v})]
    [∀ i, IsLocalRing (A.obj i)]
    [∀ i, IsNoetherianRing (A.obj i)] [∀ i, IsNoetherianRing (B.obj i)]
    [∀ i, Module (B.obj i) (N.obj i)] [∀ i, Module.Finite (B.obj i) (N.obj i)]
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
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z})) (i : Λ) :
    ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj i) (φ i)
      letI := Module.compHom (N.obj j) (φ j)
      let I := IsLocalRing.maximalIdeal (A.obj i)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧
        (∀ k : I ⊗[A.obj i] N.obj i,
          TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype) k = 0 →
            θ k = 0) := by
  classical
  let := Module.compHom (N.obj i) (φ i)
  let : SMulCommClass (A.obj i) (B.obj i) (N.obj i) :=
    ⟨fun a b x ↦ smul_comm ((φ i) a) b x⟩
  let I := IsLocalRing.maximalIdeal (A.obj i)
  let μ := TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype)
  let e := TensorProduct.comm (A.obj i) (N.obj i) I
  obtain ⟨s, hs, hspan⟩ := exists_finite_tensor_kernel_generators (M := N.obj i) (φ i) I
  obtain ⟨j, f, θ, hθ, hz⟩ := exists_stage_finite_ideal_kernel_vanishes
    A B N φ hcomm hscalar ψ hψ hlimitScalar hflat i I (s.image e) (by
      intro k hk
      obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hk
      subst k
      exact hs x hx)
  let := Module.compHom (N.obj j) (φ j)
  let : SMulCommClass (A.obj j) (B.obj j) (N.obj j) :=
    ⟨fun a b x ↦ smul_comm ((φ j) a) b x⟩
  let J := I.map (A.map f).hom
  let e' := TensorProduct.comm (A.obj j) J (N.obj j)
  let τ := e'.toAddMonoidHom.comp (θ.comp e.toAddMonoidHom)
  have ht (x : N.obj i) (a : I) :
      τ (x ⊗ₜ[A.obj i] a) = (N.map f).hom x ⊗ₜ[A.obj j]
        (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ : J) := by
    change e' (θ (e (x ⊗ₜ[A.obj i] a))) = _
    simp only [e, TensorProduct.comm_tmul]
    rw [hθ]
    exact TensorProduct.comm_tmul _ _ _ _ _
  have hτscalar (b : B.obj i) (k : N.obj i ⊗[A.obj i] I) :
      τ (b • k) = (B.map f).hom b • τ k := by
    induction k using TensorProduct.inductionOn with
    | tmul x a =>
      simp only [TensorProduct.smul_tmul', ht, hscalar]
    | add k l hk hl => simp only [smul_add, map_add, hk, hl]
  refine ⟨j, f, θ, hθ, ?_⟩
  intro k hk
  have hmem := hspan (e.symm k) (by
    change μ (e (e.symm k)) = 0
    simpa only [LinearEquiv.apply_symm_apply] using hk)
  have hall : ∀ x ∈ Submodule.span (B.obj i) (s : Set (N.obj i ⊗[A.obj i] I)),
      τ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have hxzero := hz (e x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      change e' (θ (e x)) = 0
      rw [hxzero, map_zero]
    | zero => exact map_zero τ
    | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
    | smul b x _ hx => simp only [hτscalar, hx, smul_zero]
  have hzero := hall (e.symm k) hmem
  apply e'.injective
  change e' (θ k) = e' 0
  change e' (θ (e (e.symm k))) = 0 at hzero
  simpa only [LinearEquiv.apply_symm_apply, map_zero] using hzero

end RingTheory
