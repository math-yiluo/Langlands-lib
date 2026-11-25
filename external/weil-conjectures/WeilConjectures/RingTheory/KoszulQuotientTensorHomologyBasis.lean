/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import all WeilConjectures.RingTheory.KoszulBaseChangeIso

/-! # Basis calculation for quotient-coefficient Koszul homology

Source: Stacks Project, Tags 0623 and 062I; the quotient-coefficient Koszul
calculation used in Tag 09PQ.
(blueprint: new-d3-koszul-quotient-tensor-homology-basis). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

open ExteriorAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The quotient-coefficient Koszul homology has the standard exterior basis.
Regularity is unnecessary: the generators only have to belong to the quotient ideal.
The input basis can be any basis of the conormal module; its normalization is used
later, when comparing this isomorphism to the canonical self-Tor map.

Source: Stacks Project, Tags 0623 (Koszul differential), 062I (conormal basis),
and 09PQ (computing Tor by tensoring a free resolution).
(blueprint: new-d3-koszul-quotient-tensor-homology-basis).

Proof: Write B=A/I and E=A^r. Tensor the exterior basis of wedge^n E with B,
using the tensor commutor to put the coefficient module on the left. Its vectors
are e_S tensor 1, indexed by n-element subsets S of Fin r. Contraction with f
has every matrix coefficient in I, so the tensor differential is zero in every
degree. The cycle inclusion is thus invertible, and the homology projection is
invertible since the incoming differential is also zero. Compose these two
isomorphisms with the basis equivalence from wedge^n_B I/I^2 to wedge^n_A E
tensor_A B, sending the exterior basis induced by b to e_S tensor 1. This
basis equivalence is B-linear, hence A-linear after restriction. The inverse
cycle inclusion gives the stated cycles and the homology projection gives
the stated formula. If n>r both bases are empty. For n=0 the empty wedge is
1, for r=0 the same construction applies, and for B=0 both sides are zero.
No nontrivial-ring assumption or properness of I is used. -/
theorem exists_koszul_quotient_tensor_homology_basis
    (A : Type u) [CommRing A] (I : Ideal A) (n r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I)
    (b : Module.Basis (Fin r) (A ⧸ I) I.Cotangent) :
    let K := ExteriorAlgebra.koszulComplex A r f
    let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    ∃ e : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^n I.Cotangent)) ≅ (T.obj K).homology n,
      ∀ s : Set.powersetCard (Fin r) n,
        ∃ z : (T.obj K).cycles n,
          (T.obj K).iCycles n z =
            (exteriorPower.ιMulti A n
              (fun j ↦ Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s j) 1))
                ⊗ₜ[A] (1 : A ⧸ I) ∧
          e.hom (b.exteriorPower n s) = (T.obj K).homologyπ n z := by
  classical
  let K := koszulComplex A r f
  let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
  let L := T.obj K
  let bA (k : ℕ) :=
    (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower k
  have hd (i j : ℕ) : L.d i j = 0 := by
    by_cases hij : i = j + 1
    · subst i
      change ((tensorRight (ModuleCat.of A (A ⧸ I))).map
        ((koszulComplex A r f).d (j + 1) j)) = 0
      simp only [koszulComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change koszulBoundary A r f j x ⊗ₜ[A] y = 0
      rw [← (bA (j + 1)).sum_repr x, map_sum, TensorProduct.sum_tmul]
      apply Finset.sum_eq_zero
      intro s hs
      rw [map_smul, ← TensorProduct.smul_tmul']
      suffices h : koszulBoundary A r f j (bA (j + 1) s) ⊗ₜ[A] y = 0 by
        rw [h, smul_zero]
      dsimp [bA]
      rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
      simp only [Finsupp.coe_basisSingleOne, Function.comp_def]
      rw [koszulBoundary_wedge, TensorProduct.sum_tmul]
      apply Finset.sum_eq_zero
      intro k hk
      rw [TensorProduct.smul_tmul]
      suffices h : (((-1 : A) ^ (k.val + 2) *
          f (Set.powersetCard.ofFinEmbEquiv.symm s k)) • y : A ⧸ I) = 0 by
        rw [h, TensorProduct.tmul_zero]
      change Ideal.Quotient.mk I _ * y = 0
      rw [map_mul]
      have hfI : f (Set.powersetCard.ofFinEmbEquiv.symm s k) ∈ I :=
        hf ▸ Ideal.subset_span (Set.mem_range_self _)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hfI, mul_zero, zero_mul]
    · have hK : K.d i j = 0 := K.shape i j (by simpa [eq_comm] using hij)
      change (tensorRight (ModuleCat.of A (A ⧸ I))).map (K.d i j) = 0
      rw [hK, Functor.map_zero]
  let eX : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^n I.Cotangent)) ≅ L.X n :=
    (((b.exteriorPower n).repr.restrictScalars A).trans
      (TensorProduct.equivFinsuppOfBasisLeft (bA n)).symm).toModuleIso
  have heX (s : Set.powersetCard (Fin r) n) :
      eX.hom (b.exteriorPower n s) =
        exteriorPower.ιMulti A n
          (fun j ↦ Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s j) 1)
            ⊗ₜ[A] (1 : A ⧸ I) := by
    have hstd : bA n s = exteriorPower.ιMulti A n
        (fun j ↦ Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s j) 1) := by
      simp only [bA, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
        Finsupp.coe_basisSingleOne, Function.comp_def]
    rw [← hstd]
    apply (TensorProduct.equivFinsuppOfBasisLeft (bA n)).injective
    change (TensorProduct.equivFinsuppOfBasisLeft (bA n))
        ((TensorProduct.equivFinsuppOfBasisLeft (bA n)).symm
          ((b.exteriorPower n).repr (b.exteriorPower n s))) = _
    rw [LinearEquiv.apply_symm_apply, Module.Basis.repr_self]
    change Finsupp.single s 1 =
      (TensorProduct.equivFinsuppOfBasisLeft (bA n)) (bA n s ⊗ₜ[A] (1 : A ⧸ I))
    simp
  let ec := L.iCyclesIso n ((ComplexShape.down ℕ).next n) rfl (hd _ _)
  let eh := L.isoHomologyπ ((ComplexShape.down ℕ).prev n) n rfl (hd _ _)
  refine ⟨eX ≪≫ ec.symm ≪≫ eh, ?_⟩
  intro s
  refine ⟨ec.inv (eX.hom (b.exteriorPower n s)), ?_, ?_⟩
  · rw [← heX]
    exact congrArg (fun q ↦ q (eX.hom (b.exteriorPower n s))) ec.inv_hom_id
  · rfl

end AlgebraicGeometry
