/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import WeilConjectures.RingTheory.TorIdealCycleLift
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ConcreteCategory

/-! # Exactness of the ideal homology connecting map

Source: Stacks Project, Algebra, Tags 00M5 and 00M6.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

/-- Source: Stacks Project, Algebra, proof of Tag 00M5 and Remark 00M6.
(blueprint: lem-weil-pbc-tor-ideal-homology-exactness)

Proof in words: every quotient tensor is represented by y ⊗ 1, since a scalar
in R/I lifts to R; every differential of a quotient cycle belongs to I P₀,
so it has a finite expression Σ a_j p_j. The formula implies μ δH = 0
because ε d = 0. Conversely a tensor in ker μ lifts through I ⊗ P₀ by
right exactness. Its image in P₀ is killed by ε, hence is d y by resolution
exactness, giving a quotient cycle whose image is the original tensor.
For injectivity, if δH of a quotient cycle is zero, right exactness for
I ⊗ P identifies its ideal-tensor lift as an ideal-tensor boundary. Subtract
the corresponding element of I P₁ from y; the difference is an actual cycle
in P₁. Exactness of P in degree one makes it a boundary from P₂. Reducing
modulo I shows the original quotient cycle is a boundary. Thus δH is injective.
These arguments include the zero ideal, unit ideal and zero module.
-/
theorem tor_ideal_homology_exactness
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (hP : ∀ n : ℕ, Module.Free R (P.complex.X n))
    (μR : (I ⊗[R] M) →ₗ[R] M)
    (hμR : ∀ (a : I) (x : M), μR (a ⊗ₜ[R] x) = (a : R) • x)
    (δH : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology 1 →ₗ[R] (I ⊗[R] M))
    (hδH : ∀ (z : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
        I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).cycles 1)
        (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) →
        P.complex.d 1 0 y = ∑ j, (a j : R) • p j →
        δH
          (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homologyπ 1 z) =
          ∑ j, a j ⊗ₜ[R] P.π.f 0 (p j)) :
    Function.Injective δH ∧ LinearMap.range δH = LinearMap.ker μR := by
  classical
  -- The formula is assumed, so tensor right exactness suffices without using freeness.
  have _ := hP
  let C := (((tensoringRight (ModuleCat.{u} R)).obj
    (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let ε : P.complex.X 0 →ₗ[R] M := (P.π.f 0).hom
  let d := (P.complex.d 1 0).hom
  let m (n : ℕ) : (I ⊗[R] P.complex.X n) →ₗ[R] P.complex.X n :=
    (TensorProduct.lid R (P.complex.X n)).toLinearMap.comp
      (I.subtype.rTensor (P.complex.X n))
  have hm (n : ℕ) (a : I) (p : P.complex.X n) : m n (a ⊗ₜ[R] p) = (a : R) • p := by
    simp [m]
  have hεd (y : P.complex.X 1) : ε (d y) = 0 :=
    ConcreteCategory.congr_hom P.complex_d_comp_π_f_zero y
  have hexd : Function.Exact d ε :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀
  have hεsurj : Function.Surjective ε := (epi_iff_surjective (P.π.f 0)).mp inferInstance
  have hexI := lTensor_exact I hexd hεsurj
  have hmε (t : I ⊗[R] P.complex.X 0) : ε (m 0 t) = μR (ε.lTensor I t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a p => simp only [hm, LinearMap.lTensor_tmul, map_smul, hμR]
    | add x y hx hy => simp_all only [map_add]
  have hmd (t : I ⊗[R] P.complex.X 1) :
      d (m 1 t) = m 0 (d.lTensor I t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a p => simp only [hm, LinearMap.lTensor_tmul, map_smul]
    | add x y hx hy => simp_all only [map_add]
  have hmq (n : ℕ) (t : I ⊗[R] P.complex.X n) : m n t ⊗ₜ[R] (1 : R ⧸ I) = 0 := by
    induction t using TensorProduct.inductionOn with
    | tmul a p =>
      rw [hm, TensorProduct.smul_tmul]
      have ha : (a : R) • (1 : R ⧸ I) = 0 := by
        change Ideal.Quotient.mk I (a : R) * 1 = 0
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr a.property]
      rw [ha, TensorProduct.tmul_zero]
    | add x y hx hy => simp [map_add, TensorProduct.add_tmul, hx, hy]
  -- A vanishing ideal-tensor expression forces the quotient cycle to be a boundary.
  have hclass (z : C.cycles 1) (y : P.complex.X 1)
      (hy : C.iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I))
      (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0)
      (hd : d y = ∑ j, (a j : R) • p j)
      (ht : (∑ j, a j ⊗ₜ[R] ε (p j)) = 0) : C.homologyπ 1 z = 0 := by
    let t : I ⊗[R] P.complex.X 0 := ∑ j, a j ⊗ₜ[R] p j
    have het : ε.lTensor I t = 0 := by simpa only [t, map_sum, LinearMap.lTensor_tmul] using ht
    obtain ⟨s, hs⟩ := (hexI t).mp het
    have hms : d (m 1 s) = d y := by rw [hmd, hs]; simpa only [t, map_sum, hm] using hd.symm
    have hcycle : d (y - m 1 s) = 0 := by rw [map_sub, hms, sub_self]
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp (P.exact_succ 0)
      (y - m 1 s) hcycle
    have hboundary : C.d 2 1 (w ⊗ₜ[R] (1 : R ⧸ I)) = C.iCycles 1 z := by
      change (P.complex.d 2 1 w) ⊗ₜ[R] (1 : R ⧸ I) = _
      rw [hw, TensorProduct.sub_tmul, hmq 1, sub_zero, hy]
    have hz : C.toCycles 2 1 (w ⊗ₜ[R] (1 : R ⧸ I)) = z := by
      apply (mono_iff_injective (C.iCycles 1)).mp inferInstance
      simpa only [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i] using hboundary
    rw [← hz]
    exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 2 1)
      (w ⊗ₜ[R] (1 : R ⧸ I))
  have hzero (x : C.homology 1) (hx : δH x = 0) : x = 0 := by
    obtain ⟨z, rfl⟩ := (epi_iff_surjective (C.homologyπ 1)).mp inferInstance x
    obtain ⟨y, k, a, p, hy, hd⟩ := exists_quotient_cycle_lift I M P z
    apply hclass z y hy k a p hd
    change (∑ j, a j ⊗ₜ[R] P.π.f 0 (p j)) = 0
    rw [← hδH z y k a p hy hd]
    exact hx
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · apply le_antisymm
    · rintro t ⟨x, rfl⟩
      change μR (δH x) = 0
      obtain ⟨z, rfl⟩ := (epi_iff_surjective (C.homologyπ 1)).mp inferInstance x
      obtain ⟨y, k, a, p, hy, hd⟩ := exists_quotient_cycle_lift I M P z
      rw [hδH z y k a p hy hd, map_sum]
      calc
        ∑ j, μR (a j ⊗ₜ[R] ε (p j)) = ε (∑ j, (a j : R) • p j) := by
          simp only [hμR, map_sum, map_smul]
        _ = ε (d y) := congrArg ε hd.symm
        _ = 0 := hεd y
    · -- Lift a multiplication-kernel element through the tensor augmentation.
      intro t ht
      change μR t = 0 at ht
      obtain ⟨s, hs⟩ := LinearMap.lTensor_surjective I hεsurj t
      have hεs : ε (m 0 s) = 0 := by rw [hmε, hs, ht]
      obtain ⟨y, hy⟩ := (hexd (m 0 s)).mp hεs
      obtain ⟨k, a, p, hp⟩ := TensorProduct.exists_sum_tmul_eq s
      have hd : P.complex.d 1 0 y = ∑ j, (a j : R) • p j := by
        simpa only [hp, map_sum, hm] using hy
      have hq : C.d 1 0 (y ⊗ₜ[R] (1 : R ⧸ I)) = 0 := by
        change (d y) ⊗ₜ[R] (1 : R ⧸ I) = 0
        rw [hy]
        exact hmq 0 s
      let z := C.cyclesMk (y ⊗ₜ[R] (1 : R ⧸ I)) 0 (by simp) hq
      have hz : C.iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) := C.i_cyclesMk _ _ _ _
      refine ⟨C.homologyπ 1 z, ?_⟩
      rw [hδH z y k a p hz hd]
      change (∑ j, a j ⊗ₜ[R] ε (p j)) = t
      simpa only [hp, map_sum, LinearMap.lTensor_tmul] using hs

end ModuleCat
