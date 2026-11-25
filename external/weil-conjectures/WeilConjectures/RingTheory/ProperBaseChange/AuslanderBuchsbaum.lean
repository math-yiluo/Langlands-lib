/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.RingTheory.GlobalDimension
public import WeilConjectures.RingTheory.Depth
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.MinimalFiniteFreeResolutionLocal
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.ExactFreeComplexLastMinors
import WeilConjectures.RingTheory.DepthInSES
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Regular.Flat
import WeilConjectures.RingTheory.DepthExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# The Auslander–Buchsbaum depth formula

Source: Stacks Project, Algebra, Tag 090V, proposition-Auslander-Buchsbaum
(blueprint: lem-weil-pbc-auslander-buchsbaum).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u v

namespace IsLocalRing

open CategoryTheory CategoryTheory.Limits

private theorem depth_equiv_local {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    {B : Type*} [AddCommGroup B] [Module R B] [Module.Finite R B]
    (e : A ≃ₗ[R] B) : depth (R := R) A = depth (R := R) B := by
  have hmap : (maximalIdeal R • (⊤ : Submodule R A)).map e.toLinearMap =
      maximalIdeal R • (⊤ : Submodule R B) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  have htop : (maximalIdeal R • (⊤ : Submodule R A) = ⊤) ↔
      (maximalIdeal R • (⊤ : Submodule R B) = ⊤) := by
    constructor
    · intro h
      rw [← hmap, h]
      simp
    · intro h
      rw [← hmap] at h
      exact Submodule.map_eq_top_iff.mp h
  unfold depth Ideal.depth
  split_ifs with hA hB hB
  · rfl
  · exact (hB (htop.mp hA)).elim
  · exact (hA (htop.mpr hB)).elim
  · congr 1
    ext n
    constructor
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mp hreg, hmem, rfl⟩
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mpr hreg, hmem, rfl⟩

private theorem depth_subsingleton {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Subsingleton A] :
    depth (R := R) A = ⊤ := by
  unfold depth Ideal.depth
  have ht : maximalIdeal R • (⊤ : Submodule R A) = ⊤ := Subsingleton.elim _ _
  rw [ite_eq_left ht]

private theorem depth_free_ge {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Free R A] :
    depth (R := R) R ≤ depth (R := R) A := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl h =>
    let := h
    rw [depth_subsingleton A]
    exact le_top
  | inr h =>
    let := h
    let ι := Module.Free.ChooseBasisIndex R A
    let e : A ≃ₗ[R] (ι → R) := (Module.Free.chooseBasis R A).equivFun
    rw [depth_equiv_local e]
    have ht : maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ :=
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (maximalIdeal_le_jacobson (Module.annihilator R R))).symm
    unfold depth Ideal.depth
    rw [ite_eq_right ht]
    split_ifs with hP
    · exact le_top
    · apply sSup_le
      rintro n ⟨rs, hr, hm, rfl⟩
      apply le_sSup
      refine ⟨rs, ?_, hm, rfl⟩
      apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal (ι → R) hm
      exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
        (ι → R) (ι → R) rs).mp (hr.1.of_flat (S := ι → R))

end IsLocalRing
