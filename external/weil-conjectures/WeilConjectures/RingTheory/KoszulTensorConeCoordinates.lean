/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.RingTheory.KoszulLastGeneratorAssembly
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Coordinates for adjoining the final Koszul generator

Source: Stacks Project, Tags 0628 and 0629.
(blueprint: lem-weil-pbc-koszul-tensor-cone-coordinates).
-/

@[expose] public section

universe u v

namespace ExteriorAlgebra

open scoped TensorProduct

private theorem contract_prefix {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin (r + 1) → R) (x : ExteriorAlgebra R (Fin r →₀ R)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
      (Finsupp.linearCombination R f) (ExteriorAlgebra.map (koszulPrefixInclusion R r) x) =
    ExteriorAlgebra.map (koszulPrefixInclusion R r)
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin r →₀ R)))
        (Finsupp.linearCombination R (fun i ↦ f i.castSucc)) x) := by
  have hφ (v : Fin r →₀ R) :
      Finsupp.linearCombination R f (koszulPrefixInclusion R r v) =
        Finsupp.linearCombination R (fun i ↦ f i.castSucc) v :=
    LinearMap.congr_fun (Finsupp.linearCombination_comp_lmapDomain R (v' := f) Fin.castSucc) v
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul v x hx =>
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      hφ, map_sub, map_smul, hx]

private theorem prefix_map_coe {R : Type u} [CommRing R] (r n : ℕ)
    (x : ⋀[R]^n (Fin r →₀ R)) :
    (exteriorPower.map n (koszulPrefixInclusion R r) x :
      ExteriorAlgebra R (Fin (r + 1) →₀ R)) =
      ExteriorAlgebra.map (koszulPrefixInclusion R r) (x : ExteriorAlgebra R (Fin r →₀ R)) := by
  have h : (⋀[R]^n (Fin (r + 1) →₀ R)).subtype.comp
      (exteriorPower.map n (koszulPrefixInclusion R r)) =
      (ExteriorAlgebra.map (koszulPrefixInclusion R r)).toLinearMap.comp
        (⋀[R]^n (Fin r →₀ R)).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, AlgHom.toLinearMap_apply]
    exact (ExteriorAlgebra.map_apply_ιMulti (koszulPrefixInclusion R r) v).symm
  exact LinearMap.congr_fun h x

private theorem boundary_assembly {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin (r + 1) → R) (n : ℕ)
    (a : ⋀[R]^(n + 2) (Fin r →₀ R)) (b : ⋀[R]^(n + 1) (Fin r →₀ R)) :
    koszulBoundary R (r + 1) f (n + 1) (koszulLastAssembly R r (n + 1) (a, b)) =
      koszulLastAssembly R r n
        (koszulBoundary R r (fun i ↦ f i.castSucc) (n + 1) a + f (Fin.last r) • b,
          -koszulBoundary R r (fun i ↦ f i.castSucc) n b) := by
  apply Subtype.ext
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
    (Finsupp.linearCombination R f)
      ((exteriorPower.map (n + 2) (koszulPrefixInclusion R r) a :
          ExteriorAlgebra R (Fin (r + 1) →₀ R)) +
        ι R (Finsupp.single (Fin.last r) 1) *
          (exteriorPower.map (n + 1) (koszulPrefixInclusion R r) b :
            ExteriorAlgebra R (Fin (r + 1) →₀ R))) = _
  simp only [map_add, CliffordAlgebra.contractLeft_ι_mul,
    Finsupp.linearCombination_single, one_smul]
  change _ = (exteriorPower.map (n + 1) (koszulPrefixInclusion R r)
    (koszulBoundary R r (fun i ↦ f i.castSucc) (n + 1) a + f (Fin.last r) • b) :
      ExteriorAlgebra R (Fin (r + 1) →₀ R)) +
    ι R (Finsupp.single (Fin.last r) 1) *
      (exteriorPower.map n (koszulPrefixInclusion R r)
        (-koszulBoundary R r (fun i ↦ f i.castSucc) n b) :
          ExteriorAlgebra R (Fin (r + 1) →₀ R))
  simp only [map_add, map_smul, map_neg, Submodule.coe_add, Submodule.coe_smul,
    Submodule.coe_neg, mul_neg, sub_eq_add_neg]
  simp only [prefix_map_coe, contract_prefix]
  simp only [koszulBoundary, LinearMap.codRestrict_apply, LinearMap.comp_apply, add_assoc]
  rfl

private theorem boundary_assembly_zero {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin (r + 1) → R)
    (a : ⋀[R]^1 (Fin r →₀ R)) (b : ⋀[R]^0 (Fin r →₀ R)) :
    koszulBoundary R (r + 1) f 0 (koszulLastAssembly R r 0 (a, b)) =
      exteriorPower.map 0 (koszulPrefixInclusion R r)
        (koszulBoundary R r (fun i ↦ f i.castSucc) 0 a + f (Fin.last r) • b) := by
  have hb : (b : ExteriorAlgebra R (Fin r →₀ R)) ∈ (1 : Submodule R _) := by
    simpa only [exteriorPower, pow_zero] using b.property
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp hb
  apply Subtype.ext
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
    (Finsupp.linearCombination R f)
      ((exteriorPower.map 1 (koszulPrefixInclusion R r) a :
          ExteriorAlgebra R (Fin (r + 1) →₀ R)) +
        ι R (Finsupp.single (Fin.last r) 1) *
          (exteriorPower.map 0 (koszulPrefixInclusion R r) b :
            ExteriorAlgebra R (Fin (r + 1) →₀ R))) = _
  simp only [map_add, CliffordAlgebra.contractLeft_ι_mul,
    Finsupp.linearCombination_single, one_smul]
  simp only [map_smul, Submodule.coe_add, Submodule.coe_smul]
  rw [prefix_map_coe r 0 b, ← hc, AlgHom.commutes,
    CliffordAlgebra.contractLeft_algebraMap, mul_zero, sub_zero]
  simp only [prefix_map_coe, contract_prefix]
  rfl

/-- Source: Stacks Project, Tags 0628 and 0629
(blueprint: lem-weil-pbc-koszul-tensor-cone-coordinates).

Proof: split the exterior-power basis of `R^(r+1)` according to whether its
last generator occurs. Send `(a,b)` to `a + e_last ∧ b`, with the last generator
placed first in the second summand. The resulting basis bijections give linear
isomorphisms in each positive degree; degree zero is the identity on scalars.
Tensor these isomorphisms with `M`. Contraction with the sequence's linear form
restricts to the prefix contraction on the first summand. On the second summand,
the graded Leibniz rule gives `d(e_last ∧ b) = f_last b - e_last ∧ d b`.
This proves both displayed differential formulas, including the separate formula
from degree one to degree zero. When `r=0`, the positive prefix exterior powers
are zero and the same basis argument and formulas still hold. -/
theorem exists_koszulTensorConeCoordinates {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin (r + 1) → R) :
    let A := koszulComplexTensor R r (fun i ↦ f i.castSucc) M
    let B := koszulComplexTensor R (r + 1) f M
    ∃ (e₀ : B.X 0 ≃ₗ[R] A.X 0)
      (e : ∀ n : ℕ, B.X (n + 1) ≃ₗ[R] A.X (n + 1) × A.X n),
      (∀ x : B.X 1, e₀ (B.d 1 0 x) =
        A.d 1 0 (e 0 x).1 + f (Fin.last r) • (e 0 x).2) ∧
      (∀ (n : ℕ) (x : B.X (n + 2)), e n (B.d (n + 2) (n + 1) x) =
        (A.d (n + 2) (n + 1) (e (n + 1) x).1 +
          f (Fin.last r) • (e (n + 1) x).2,
        -A.d (n + 1) n (e (n + 1) x).2)) := by
  let i₀ : ⋀[R]^0 (Fin r →₀ R) ≃ₗ[R] ⋀[R]^0 (Fin (r + 1) →₀ R) :=
    (exteriorPower.zeroEquiv R (Fin r →₀ R)).trans
      (exteriorPower.zeroEquiv R (Fin (r + 1) →₀ R)).symm
  have hi₀ (x : ⋀[R]^0 (Fin r →₀ R)) :
      i₀ x = exteriorPower.map 0 (koszulPrefixInclusion R r) x := by
    apply (exteriorPower.zeroEquiv R (Fin (r + 1) →₀ R)).injective
    simp only [i₀, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact (LinearMap.congr_fun
      (exteriorPower.zeroEquiv_naturality (koszulPrefixInclusion R r)) x).symm
  let i (n : ℕ) :
      (⋀[R]^(n + 1) (Fin r →₀ R) × ⋀[R]^n (Fin r →₀ R)) ≃ₗ[R]
        ⋀[R]^(n + 1) (Fin (r + 1) →₀ R) :=
    LinearEquiv.ofBijective (koszulLastAssembly R r n) (koszulLastAssembly_bijective R r n)
  let e₀ := i₀.symm.rTensor M
  let e (n : ℕ) := ((i n).symm.rTensor M).trans
    (TensorProduct.prodLeft R R (⋀[R]^(n + 1) (Fin r →₀ R))
      (⋀[R]^n (Fin r →₀ R)) M)
  have he (n : ℕ) (a : ⋀[R]^(n + 1) (Fin r →₀ R))
      (b : ⋀[R]^n (Fin r →₀ R)) (m : M) :
      e n (koszulLastAssembly R r n (a, b) ⊗ₜ[R] m) = (a ⊗ₜ[R] m, b ⊗ₜ[R] m) := by
    change e n (i n (a, b) ⊗ₜ[R] m) = _
    simp [e]
  have he₀ (a : ⋀[R]^0 (Fin r →₀ R)) (m : M) :
      e₀ (exteriorPower.map 0 (koszulPrefixInclusion R r) a ⊗ₜ[R] m) = a ⊗ₜ[R] m := by
    rw [← hi₀]
    simp [e₀]
  refine ⟨e₀, e, ?_, ?_⟩
  · intro x
    change e₀ ((koszulBoundary R (r + 1) f 0).rTensor M x) =
      (koszulBoundary R r (fun i ↦ f i.castSucc) 0).rTensor M (e 0 x).1 +
        f (Fin.last r) • (e 0 x).2
    let F := e₀.toLinearMap.comp ((koszulBoundary R (r + 1) f 0).rTensor M)
    let G := ((koszulBoundary R r (fun i ↦ f i.castSucc) 0).rTensor M).comp
      ((LinearMap.fst R _ _).comp (e 0).toLinearMap) +
      f (Fin.last r) • (LinearMap.snd R _ _).comp (e 0).toLinearMap
    change F x = G x
    apply LinearMap.congr_fun
    apply TensorProduct.ext'
    intro x m
    obtain ⟨⟨a, b⟩, rfl⟩ := (i 0).surjective x
    change e₀ ((koszulBoundary R (r + 1) f 0).rTensor M
      (koszulLastAssembly R r 0 (a, b) ⊗ₜ[R] m)) =
        (koszulBoundary R r (fun i ↦ f i.castSucc) 0).rTensor M
          (e 0 (koszulLastAssembly R r 0 (a, b) ⊗ₜ[R] m)).1 +
        f (Fin.last r) • (e 0 (koszulLastAssembly R r 0 (a, b) ⊗ₜ[R] m)).2
    rw [LinearMap.rTensor_tmul, boundary_assembly_zero, he₀, he]
    simp only [TensorProduct.add_tmul, TensorProduct.smul_tmul', LinearMap.rTensor_tmul]
  · intro n x
    dsimp only [koszulComplexTensor, ChainComplex.of] at x ⊢
    erw [ChainComplex.of_d _ _ (n + 1), ChainComplex.of_d _ _ (n + 1),
      ChainComplex.of_d _ _ n]
    change e n ((koszulBoundary R (r + 1) f (n + 1)).rTensor M x) =
      ((koszulBoundary R r (fun i ↦ f i.castSucc) (n + 1)).rTensor M (e (n + 1) x).1 +
          f (Fin.last r) • (e (n + 1) x).2,
        -(koszulBoundary R r (fun i ↦ f i.castSucc) n).rTensor M (e (n + 1) x).2)
    let p := (LinearMap.fst R _ _).comp (e (n + 1)).toLinearMap
    let q := (LinearMap.snd R _ _).comp (e (n + 1)).toLinearMap
    let F := (e n).toLinearMap.comp ((koszulBoundary R (r + 1) f (n + 1)).rTensor M)
    let G := (((koszulBoundary R r (fun i ↦ f i.castSucc) (n + 1)).rTensor M).comp p +
      f (Fin.last r) • q).prod (-((koszulBoundary R r (fun i ↦ f i.castSucc) n).rTensor M).comp q)
    change F x = G x
    apply LinearMap.congr_fun
    apply TensorProduct.ext'
    intro x m
    obtain ⟨⟨a, b⟩, rfl⟩ := (i (n + 1)).surjective x
    change e n ((koszulBoundary R (r + 1) f (n + 1)).rTensor M
      (koszulLastAssembly R r (n + 1) (a, b) ⊗ₜ[R] m)) =
        ((koszulBoundary R r (fun i ↦ f i.castSucc) (n + 1)).rTensor M
            (e (n + 1) (koszulLastAssembly R r (n + 1) (a, b) ⊗ₜ[R] m)).1 +
          f (Fin.last r) • (e (n + 1) (koszulLastAssembly R r (n + 1) (a, b) ⊗ₜ[R] m)).2,
        -(koszulBoundary R r (fun i ↦ f i.castSucc) n).rTensor M
          (e (n + 1) (koszulLastAssembly R r (n + 1) (a, b) ⊗ₜ[R] m)).2)
    rw [LinearMap.rTensor_tmul, boundary_assembly, he, he]
    simp only [TensorProduct.add_tmul, TensorProduct.smul_tmul',
      TensorProduct.neg_tmul, LinearMap.rTensor_tmul]


end ExteriorAlgebra
