/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite generators of an ideal multiplication kernel

Source: Stacks Project, Algebra, Tag 00R6, finite-generation paragraph.
(blueprint: lem-weil-pbc-finite-tensor-kernel-generators)
-/

@[expose] public section

universe u v w
open scoped TensorProduct
namespace RingTheory

/-- The ideal multiplication kernel has finitely many generators over the larger ring.
Source: Stacks Project, Algebra, Tag 00R6, choosing the generators xi.
(blueprint: lem-weil-pbc-finite-tensor-kernel-generators)

Proof: Choose finitely many R-generators of I and S-generators of M. Their pure
products generate M tensor I over S: expand both factors and move R-scalars to
M through phi. Multiplication is S-linear since S is commutative. Its kernel is
an S-submodule of this finite module, hence is finite since S is Noetherian.
Choose a finite generating set of that kernel. Its elements multiply to zero,
and its S-span is precisely the multiplication kernel. The zero ideal and zero
module give the empty generating set; no nontriviality assumption is needed. -/
theorem exists_finite_tensor_kernel_generators
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [AddCommGroup M]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Module S M] [Module.Finite S M]
    (φ : R →+* S) (I : Ideal R) :
    letI := Module.compHom M φ
    letI : SMulCommClass R S M := ⟨fun a b x ↦ smul_comm (φ a) b x⟩
    let μ := TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
    ∃ s : Finset (M ⊗[R] I),
      (∀ k ∈ s, μ (TensorProduct.comm R M I k) = 0) ∧
      (∀ k : M ⊗[R] I, μ (TensorProduct.comm R M I k) = 0 →
        k ∈ Submodule.span S (s : Set (M ⊗[R] I))) := by
  classical
  let := Module.compHom M φ
  let : SMulCommClass R S M := ⟨fun a b x ↦ smul_comm (φ a) b x⟩
  let μ := TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let e := TensorProduct.comm R M I
  obtain ⟨xs, hxs⟩ := (Module.Finite.fg_top (R := S) (M := M))
  obtain ⟨ys, hys⟩ := (Module.Finite.fg_top (R := R) (M := I))
  let t : Set (M ⊗[R] I) := Set.image2 (fun x y ↦ x ⊗ₜ[R] y) (xs : Set M) (ys : Set I)
  let P := Submodule.span S t
  have hygen (y : I) (hy : y ∈ ys) (x : M) : x ⊗ₜ[R] y ∈ P := by
    have hx : x ∈ Submodule.span S (xs : Set M) := by rw [hxs]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
    | zero => simp
    | add x z _ _ hx hz => simpa only [TensorProduct.add_tmul] using P.add_mem hx hz
    | smul b x _ hx =>
      simpa only [TensorProduct.smul_tmul'] using P.smul_mem b hx
  have htmul (y : I) (x : M) : x ⊗ₜ[R] y ∈ P := by
    have hy : y ∈ Submodule.span R (ys : Set I) := by rw [hys]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact hygen y hy x
    | zero => simp
    | add y z _ _ hy hz => simpa only [TensorProduct.tmul_add] using P.add_mem hy hz
    | smul a y _ hy =>
      have heq : x ⊗ₜ[R] (a • y) = (φ a) • (x ⊗ₜ[R] y) := by
        rw [← TensorProduct.smul_tmul]
        rfl
      rw [heq]
      exact P.smul_mem (φ a) hy
  have hP : P = ⊤ := by
    apply eq_top_iff.mpr
    intro k
    suffices k ∈ P from fun _ ↦ this
    induction k using TensorProduct.inductionOn with
    | tmul x y => exact htmul y x
    | add k l hk hl => exact P.add_mem hk hl
  have hfinite : Module.Finite S (M ⊗[R] I) :=
    ⟨by
      rw [← hP]
      exact Submodule.fg_def.mpr ⟨t, xs.finite_toSet.image2 _ ys.finite_toSet, rfl⟩⟩
  let π : M ⊗[R] I →ₗ[S] M :=
    { toFun := fun k ↦ μ (e k)
      map_add' := fun k l ↦ by rw [map_add, map_add]
      map_smul' := fun b k ↦ by
        induction k using TensorProduct.inductionOn with
        | tmul x a =>
          simp only [TensorProduct.smul_tmul', e, TensorProduct.comm_tmul,
            μ, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply,
            Submodule.subtype_apply]
          exact smul_comm (φ a) b x
        | add k l hk hl => simp only [smul_add, map_add, hk, hl] }
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian π.ker)
  refine ⟨s, ?_, ?_⟩
  · intro k hk
    have hmem : k ∈ π.ker := by rw [← hs]; exact Submodule.subset_span hk
    exact hmem
  · intro k hk
    rw [hs]
    exact hk


end RingTheory
