/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! Tensor Koszul augmentation for complementary regular quotients.
Source: Stacks Project, `intersection.tex`, Tag 0B1I.
(blueprint: new-d3-regular-local-complementary-tensor-augmentation)

The statement isolates construction of the normalized degree-zero augmentation after
base change; its proof uses the tensor homology calculation and the quotient identity.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace RingTheory

private noncomputable def tensorZeroEquiv {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (r : ℕ) :
    (⋀[R]^0 (Fin r →₀ R) ⊗[R] M) ≃ₗ[R] M :=
    (TensorProduct.congr (exteriorPower.zeroEquiv R (Fin r →₀ R))
    (LinearEquiv.refl R M)).trans (TensorProduct.lid R M)
private theorem koszulBoundary_zero_formula_local
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R)
    (x : ⋀[R]^1 (Fin r →₀ R)) :
    exteriorPower.zeroEquiv R (Fin r →₀ R)
        (ExteriorAlgebra.koszulBoundary R r f 0 x) =
      Finsupp.linearCombination R f (exteriorPower.oneEquiv R (Fin r →₀ R) x) := by
  have he : (exteriorPower.zeroEquiv R (Fin r →₀ R)).toLinearMap.comp
      (ExteriorAlgebra.koszulBoundary R r f 0) =
      (Finsupp.linearCombination R f).comp
        (exteriorPower.oneEquiv R (Fin r →₀ R)).toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext v
    have hg : ExteriorAlgebra.koszulBoundary R r f 0
          (exteriorPower.ιMulti R 1 v) =
        (exteriorPower.zeroEquiv R (Fin r →₀ R)).symm
          (Finsupp.linearCombination R f (v 0)) := by
      apply Subtype.ext
      simp [ExteriorAlgebra.koszulBoundary, exteriorPower.zeroEquiv_symm_apply,
        ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι,
        Algebra.algebraMap_eq_smul_one]
    simp [hg]
  exact LinearMap.congr_fun he x

private theorem tensorZeroEquiv_boundary_tmul {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R)
    (x : ⋀[R]^1 (Fin r →₀ R)) (m : M) :
    tensorZeroEquiv M r ((ExteriorAlgebra.koszulBoundary R r f 0).rTensor M
      (x ⊗ₜ[R] m)) =
      Finsupp.linearCombination R f (exteriorPower.oneEquiv R (Fin r →₀ R) x) • m := by
  change (exteriorPower.zeroEquiv R (Fin r →₀ R)
      (ExteriorAlgebra.koszulBoundary R r f 0 x)) • m = _
  rw [koszulBoundary_zero_formula_local]

private theorem tensorZeroEquiv_boundary_range {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R) :
    LinearMap.range ((tensorZeroEquiv M r).toLinearMap.comp
      ((ExteriorAlgebra.koszulBoundary R r f 0).rTensor M)) =
      Ideal.span (Set.range f) • (⊤ : Submodule R M) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul x m =>
      change tensorZeroEquiv M r ((ExteriorAlgebra.koszulBoundary R r f 0).rTensor M
        (x ⊗ₜ[R] m)) ∈ _
      rw [tensorZeroEquiv_boundary_tmul]
      apply Submodule.smul_mem_smul _ (Submodule.mem_top : m ∈ (⊤ : Submodule R M))
      rw [← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination]
      exact LinearMap.mem_range_self _ _
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro t ht m _
    rw [← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination] at ht
    obtain ⟨x, hx⟩ := ht
    refine ⟨(exteriorPower.oneEquiv R (Fin r →₀ R)).symm x ⊗ₜ[R] m, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [tensorZeroEquiv_boundary_tmul, LinearEquiv.apply_symm_apply, hx]

private theorem exists_tensor_quotient_augmentation
    (A : Type u) [CommRing A] (I J : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : ∀ n : ℕ, 0 < n →
      IsZero ((ExteriorAlgebra.koszulComplexTensor A r f (A ⧸ J)).homology n))
    (hf : Ideal.span (Set.range f) = I) :
    ∃ δ : ExteriorAlgebra.koszulComplexTensor A r f (A ⧸ J) ⟶
        (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ (I ⊔ J))),
      QuasiIso δ ∧ ∀ (x : ⋀[A]^0 (Fin r →₀ A)) (a : A),
        δ.f 0 (x ⊗ₜ[A] Ideal.Quotient.mk J a) =
          Ideal.Quotient.mk (I ⊔ J)
            (exteriorPower.zeroEquiv A (Fin r →₀ A) x * a) := by
  let K := ExteriorAlgebra.koszulComplexTensor A r f (A ⧸ J)
  let e : (⋀[A]^0 (Fin r →₀ A) ⊗[A] (A ⧸ J)) ≃ₗ[A] (A ⧸ J) :=
    tensorZeroEquiv (A ⧸ J) r
  let qM : (A ⧸ J) →ₗ[A] A ⧸ (I ⊔ J) :=
    J.liftQ (I ⊔ J).mkQ (by
      intro a ha
      exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_sup_right ha))
  have hqM (b : A) : qM (Ideal.Quotient.mk J b) =
      Ideal.Quotient.mk (I ⊔ J) b := by
    dsimp [qM]
    rfl
  let q : K.X 0 ⟶ ModuleCat.of A (A ⧸ (I ⊔ J)) :=
    ModuleCat.ofHom (qM.comp e.toLinearMap)
  have hq (x : K.X 0) : q x = qM (e x) := rfl
  have hmem (v : Fin r →₀ A) : Finsupp.linearCombination A f v ∈ I := by
    rw [← hf, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ _
  have hz : K.d 1 0 ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change qM (e (K.d 1 0 x)) = 0
    change qM (tensorZeroEquiv (A ⧸ J) r
      ((ExteriorAlgebra.koszulBoundary A r f 0).rTensor (A ⧸ J) x)) = 0
    induction x using TensorProduct.inductionOn with
    | tmul x m =>
      rw [tensorZeroEquiv_boundary_tmul]
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
      change qM ((Ideal.Quotient.mk J
        (Finsupp.linearCombination A f (exteriorPower.oneEquiv A (Fin r →₀ A) x))) *
        (Ideal.Quotient.mk J a)) = 0
      have hm : (Ideal.Quotient.mk J
          (Finsupp.linearCombination A f (exteriorPower.oneEquiv A (Fin r →₀ A) x))) *
          (Ideal.Quotient.mk J a) =
          Ideal.Quotient.mk J
            (Finsupp.linearCombination A f (exteriorPower.oneEquiv A (Fin r →₀ A) x) * a) := rfl
      rw [hm]
      rw [hqM]
      apply (Ideal.Quotient.eq_zero_iff_mem).2
      exact Ideal.mem_sup_left (I.mul_mem_right a (hmem _))
    | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy, add_zero]
  let δ := (ChainComplex.toSingle₀Equiv K
    (ModuleCat.of A (A ⧸ (I ⊔ J)))).symm ⟨q, hz⟩
  have hδ : δ.f 0 = q := ChainComplex.toSingle₀Equiv_symm_apply_f_zero q hz
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨(exteriorPower.zeroEquiv A (Fin r →₀ A)).symm 1 ⊗ₜ[A]
      Ideal.Quotient.mk J a, ?_⟩
    rw [hq]
    have he : e ((exteriorPower.zeroEquiv A (Fin r →₀ A)).symm 1 ⊗ₜ[A]
        Ideal.Quotient.mk J a) = Ideal.Quotient.mk J a := by
      simp [e, tensorZeroEquiv]
    rw [he, hqM]
    exact ha
  have hex : (ShortComplex.mk (K.d 1 0) q hz).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x : K.X 0) hx
    change qM (e x) = 0 at hx
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e x)
    have hzero : qM (Ideal.Quotient.mk J a) = 0 := by
      rw [← ha] at hx
      exact hx
    have haN : a ∈ I ⊔ J := by
      apply (Ideal.Quotient.eq_zero_iff_mem).1
      rw [hqM] at hzero
      exact hzero
    obtain ⟨i, hi, j, hj, hsum⟩ := Submodule.mem_sup.mp haN
    have hxi : e x = Ideal.Quotient.mk J i := by
      calc
        e x = Ideal.Quotient.mk J a := ha.symm
        _ = Ideal.Quotient.mk J (i + j) := by rw [hsum]
        _ = Ideal.Quotient.mk J i := by
          rw [map_add, show (Ideal.Quotient.mk J) j = 0 by
            exact (Ideal.Quotient.eq_zero_iff_mem).2 hj, add_zero]
    have hxi' : e x ∈ Ideal.span (Set.range f) •
        (⊤ : Submodule A (A ⧸ J)) := by
      rw [hxi]
      rw [← hf] at hi
      simpa [Algebra.smul_def] using
        (Submodule.smul_mem_smul hi
          (show (Ideal.Quotient.mk J 1) ∈ (⊤ : Submodule A (A ⧸ J)) by trivial))
    have hrange : e x ∈ LinearMap.range
        ((tensorZeroEquiv (A ⧸ J) r).toLinearMap.comp
          ((ExteriorAlgebra.koszulBoundary A r f 0).rTensor (A ⧸ J))) := by
      rw [tensorZeroEquiv_boundary_range]
      exact hxi'
    obtain ⟨z, hz⟩ := hrange
    refine ⟨z, ?_⟩
    apply (tensorZeroEquiv (A ⧸ J) r).injective
    exact hz
  have hqepi : Epi q := (ModuleCat.epi_iff_surjective q).mpr hsurj
  have hqi : QuasiIso δ := by
    constructor
    intro n
    by_cases hn : n = 0
    · subst n
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_isIso_descOpcycles _ (by simp) (by simp) (by simp)]
      let S := K.sc' 1 0 0
      let ei := S.isoOpcyclesOfIsColimit hex.gIsCokernel
      have heq : S.descOpcycles
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat A)
            (ComplexShape.down ℕ) 1 0 0).map δ).τ₂
          (by change K.d 1 0 ≫ δ.f 0 = 0; rw [hδ]; exact hz) = ei.inv := by
        apply (cancel_epi S.pOpcycles).mp
        simp only [ShortComplex.p_descOpcycles]
        simp only [ShortComplex.pOpcycles_π_isoOpcyclesOfIsColimit_inv, ei]
        exact hδ
      rw [heq]
      infer_instance
    · rw [quasiIsoAt_iff_exactAt]
      · exact HomologicalComplex.exactAt_single_obj _ _ _ _ hn
      · exact (HomologicalComplex.exactAt_iff_isZero_homology K n).mpr
          (hreg n (Nat.pos_iff_ne_zero.mpr hn))
  refine ⟨δ, hqi, ?_⟩
  intro x a
  rw [hδ]
  change qM (tensorZeroEquiv (A ⧸ J) r (x ⊗ₜ[A] Ideal.Quotient.mk J a)) = _
  change qM ((exteriorPower.zeroEquiv A (Fin r →₀ A) x) •
      (Ideal.Quotient.mk J a)) = _
  change qM (Ideal.Quotient.mk J
      (exteriorPower.zeroEquiv A (Fin r →₀ A) x * a)) = _
  exact hqM _

/-- Acyclic tensor Koszul homology and transversality give the normalized tensor
augmentation to the common quotient.
Source: Stacks Project, `intersection.tex`, Tag 0B1I.
(blueprint: new-d3-regular-local-complementary-tensor-augmentation)

Proof: use the degree-zero identification of the tensor Koszul complex with the quotient
by `I ⊔ J`, define the map by multiplication, and use exactness in positive degrees
from the tensor homology hypothesis to obtain a quasi-isomorphism. The displayed pure
tensor formula is the defining multiplication formula.
-/
theorem regularLocal_complementary_tensor_augmentation
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (r : ℕ) (I J : Ideal A) (g : Fin r → A)
    (hspan : I = Ideal.span (Set.range g))
    (hpositive : ∀ n : ℕ, 0 < n →
      IsZero ((ExteriorAlgebra.koszulComplexTensor A r g
        (A ⧸ J)).homology n))
    (htrans : I ⊔ J = IsLocalRing.maximalIdeal A) :
    ∃ δ : ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J) ⟶
        (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ (I ⊔ J))),
      QuasiIso δ ∧ ∀ (x : ⋀[A]^0 (Fin r →₀ A)) (a : A),
        δ.f 0 (x ⊗ₜ[A] Ideal.Quotient.mk J a) =
          Ideal.Quotient.mk (I ⊔ J)
            (exteriorPower.zeroEquiv A (Fin r →₀ A) x * a) := by
  have _ := htrans
  exact exists_tensor_quotient_augmentation A I J r g hpositive hspan.symm

end RingTheory
