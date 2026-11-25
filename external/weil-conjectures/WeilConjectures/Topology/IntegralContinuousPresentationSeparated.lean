/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # Separation of continuous finite presentations

The compact space of solutions of a finite system of integral linear equations
has a continuous section over an extremally disconnected compact space.
This is the compact-solution substep of ordinary integral quotient separation.
-/

@[expose] public section
set_option autoImplicit false

namespace ContinuousMap

private theorem exists_matrix_solution
    {S : Type*} {R : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [ExtremallyDisconnected S] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) C(S, R)) (b : Fin n → C(S, R))
    (hb : ∀ s : S, ∃ v : Fin m → R, ∀ i, ∑ j, A i j s * v j = b i s) :
    ∃ a : Fin m → C(S, R), ∀ i, ∑ j, A i j * a j = b i := by
  classical
  let Z := {z : S × (Fin m → R) | ∀ i, ∑ j, A i j z.1 * z.2 j = b i z.1}
  have hZ : IsClosed Z := by
    change IsClosed {z : S × (Fin m → R) | ∀ i, _}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq
      (continuous_finsetSum _ fun j _ ↦
        ((A i j).continuous.comp continuous_fst).mul
          ((continuous_apply j).comp continuous_snd))
      ((b i).continuous.comp continuous_fst)
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  have hp : Function.Surjective (fun z : Z ↦ z.val.1) := by
    intro s
    obtain ⟨v, hv⟩ := hb s
    exact ⟨⟨(s, v), hv⟩, rfl⟩
  obtain ⟨t, ht, hsec⟩ := CompactT2.ExtremallyDisconnected.projective
    (A := S) continuous_id (continuous_fst.comp continuous_subtype_val) hp
  refine ⟨fun j ↦ ⟨fun s ↦ (t s).val.2 j,
    (continuous_apply j).comp (continuous_snd.comp (continuous_subtype_val.comp ht))⟩, ?_⟩
  intro i
  apply ContinuousMap.ext
  intro s
  have hs : (t s).val.1 = s := congrFun hsec s
  simpa [ContinuousMap.coe_sum, hs] using (t s).property i

/-- A continuous finite presentation on a Stonean test is separated for powers
of an element of the maximal ideal of a compact Noetherian local ring.

Source: the finite-presentation substep of ordinary integral quotient reconstruction,
motivated by Hemo--Richarz--Scholbach, Proposition 5.1. The argument here combines
Krull intersection with projectivity of extremally disconnected compact spaces.
(blueprint: lem-sp-integral-continuous-presentation-separated).

Proof. At a point of the test space, pass to the finite module which is the
cokernel of the matrix. The approximation hypothesis makes the class of b
infinitely divisible by r. Krull intersection makes this class zero. The
space of all pointwise solutions is a closed subspace of S times a finite
power of R, hence compact Hausdorff. Its projection to S is surjective.
Projectivity of the extremally disconnected compact space S gives a
continuous section, whose coordinates are the required solution. -/
theorem exists_matrix_solution_of_forall_pow
    {S : Type*} {R : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [ExtremallyDisconnected S] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [IsNoetherianRing R] [IsLocalRing R]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) C(S, R)) (b : Fin n → C(S, R))
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hb : ∀ k : ℕ, ∃ a : Fin m → C(S, R), ∃ c : Fin n → C(S, R),
      ∀ i, b i = (∑ j, A i j * a j) + r ^ k • c i) :
    ∃ a : Fin m → C(S, R), ∀ i, ∑ j, A i j * a j = b i := by
  classical
  apply exists_matrix_solution A b
  intro s
  let f : (Fin m → R) →ₗ[R] (Fin n → R) := (A.map (fun g ↦ g s)).mulVecLin
  let Q := (Fin n → R) ⧸ LinearMap.range f
  let q := (LinearMap.range f).mkQ
  have hzero : q (fun i ↦ b i s) = 0 := by
    have hI : Ideal.span {r} ≠ ⊤ :=
      Ideal.span_singleton_ne_top ((IsLocalRing.mem_maximalIdeal r).mp hr)
    have : IsHausdorff (Ideal.span {r}) Q := .of_isLocalRing _ _ hI
    apply IsHausdorff.haus this
    intro k
    obtain ⟨a, c, hc⟩ := hb k
    have he : (fun i ↦ b i s) = f (fun j ↦ a j s) + r ^ k • (fun i ↦ c i s) := by
      funext i
      simpa [f, Matrix.mulVec, dotProduct] using
        congrArg (fun g : C(S, R) ↦ g s) (hc i)
    have hqf : q (f (fun j ↦ a j s)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
    rw [he, map_add, map_smul, hqf, zero_add]
    rw [SModEq.zero, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzero
  exact ⟨a, fun i ↦ congrFun ha i⟩

end ContinuousMap
