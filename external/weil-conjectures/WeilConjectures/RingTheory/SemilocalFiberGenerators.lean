/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Etale.FiberDegree
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Generators from fibre dimensions over a semilocal ring

Source: Stacks Project, Morphisms, proof of Tag 03J6, and Algebra, Tag 00DV.
(blueprint: lem-weil-pbc-semilocal-fibre-generators).
-/

@[expose] public section

universe u v

open TensorProduct
open scoped Function

namespace RingTheory

private theorem exists_spanning_fin (k : Type*) [Field k] (V : Type*)
    [AddCommGroup V] [Module k V] [Module.Finite k V] (n : ℕ)
    (h : Module.finrank k V ≤ n) :
    ∃ b : Fin n → V, Submodule.span k (Set.range b) = ⊤ := by
  classical
  let d := Module.finrank k V
  let e := Module.finBasis k V
  let b : Fin n → V := fun i ↦ if hi : i.val < d then e ⟨i.val, hi⟩ else 0
  refine ⟨b, top_unique ?_⟩
  rw [← e.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨⟨i.val, lt_of_lt_of_le i.isLt h⟩, ?_⟩
  simp [b, d]

private noncomputable def quotientResidueEquiv {R : Type*} [CommRing R]
    (p : MaximalSpectrum R) : (R ⧸ p.asIdeal) ≃ₐ[R] p.asIdeal.ResidueField :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ p.asIdeal) p.asIdeal.ResidueField)
    p.asIdeal.bijective_algebraMap_quotient_residueField

private theorem residue_crt_surjective (R : Type*) [CommRing R]
    [Finite (MaximalSpectrum R)] (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Surjective (LinearMap.pi fun p : MaximalSpectrum R ↦
      TensorProduct.mk R p.asIdeal.ResidueField M 1) := by
  classical
  intro x
  let e (p : MaximalSpectrum R) := TensorProduct.congr
    (quotientResidueEquiv p).toLinearEquiv (LinearEquiv.refl R M)
  obtain ⟨m, hm⟩ := Ideal.pi_tensorProductMk_quotient_surjective M
    (fun p : MaximalSpectrum R ↦ p.asIdeal)
    (fun _ _ ne ↦ Ideal.isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp ne))
    (fun p ↦ (e p).symm (x p))
  refine ⟨m, funext fun p ↦ ?_⟩
  have hp := congr_fun hm p
  apply_fun e p at hp
  rw [LinearEquiv.apply_symm_apply] at hp
  simpa [e] using hp


/-- A finite algebra over a semilocal ring has at most `n` module generators when
all residue-field fibre dimensions are at most `n`.

Source: Stacks Project, Morphisms, proof of Tag 03J6; Algebra, Tag 00DV.
(blueprint: lem-weil-pbc-semilocal-fibre-generators)

Proof: pad a basis of every residue-field fibre with zeroes to length `n` and
lift these tuples simultaneously by the module Chinese remainder theorem. The
resulting linear combination map is surjective after tensoring with every
residue field. The kernel of the map to the product of fibres is the intersection
of the maximal ideals times the module. This intersection lies in the Jacobson
radical, so Nakayama's lemma makes the lifted elements generate the module. -/
theorem exists_surjective_fin_of_fiberDegree_le
    (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)]
    (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
    (n : ℕ) (h : ∀ p : MaximalSpectrum R, p.asIdeal.fiberDegree A ≤ n) :
    ∃ q : (Fin n → R) →ₗ[R] A, Function.Surjective q  := by
  classical
  have hpair : Pairwise (IsCoprime on fun p : MaximalSpectrum R ↦ p.asIdeal) :=
    fun _ _ ne ↦ Ideal.isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp ne)
  choose b hb using fun p : MaximalSpectrum R ↦
    exists_spanning_fin p.asIdeal.ResidueField (p.asIdeal.Fiber A) n (h p)
  choose v hv using fun i : Fin n ↦ residue_crt_surjective R A (fun p ↦ b p i)
  let q := Fintype.linearCombination R v
  refine ⟨q, ?_⟩
  let T := LinearMap.pi fun p : MaximalSpectrum R ↦
    TensorProduct.mk R p.asIdeal.ResidueField A 1
  have hs : Function.Surjective (T.comp q) := by
    intro x
    have hx (p : MaximalSpectrum R) :
        ∃ c : Fin n → p.asIdeal.ResidueField, ∑ i, c i • b p i = x p := by
      have surj := (span_range_eq_top_iff_surjective_fintypeLinearCombination
        p.asIdeal.ResidueField (b p)).mp (hb p)
      exact surj (x p)
    choose c hc using hx
    have hscalar : Function.Surjective (LinearMap.pi fun p : MaximalSpectrum R ↦
        Algebra.linearMap R p.asIdeal.ResidueField) := by
      intro z
      obtain ⟨r, hr⟩ := Ideal.pi_mkQ_surjective hpair
        (fun p ↦ (quotientResidueEquiv p).symm (z p))
      refine ⟨r, funext fun p ↦ ?_⟩
      have hp := congr_fun hr p
      apply_fun quotientResidueEquiv p at hp
      change (quotientResidueEquiv p) (algebraMap R (R ⧸ p.asIdeal) r) =
        (quotientResidueEquiv p) ((quotientResidueEquiv p).symm (z p)) at hp
      change (algebraMap R p.asIdeal.ResidueField) r = z p
      simpa only [AlgEquiv.commutes, AlgEquiv.apply_symm_apply] using hp
    choose r hr using fun i : Fin n ↦ hscalar (fun p ↦ c p i)
    refine ⟨r, funext fun p ↦ ?_⟩
    change (TensorProduct.mk R p.asIdeal.ResidueField A 1) (∑ i, r i • v i) = x p
    rw [map_sum]
    simp only [map_smul]
    have hv' i := congr_fun (hv i) p
    change ∀ i, (1 : p.asIdeal.ResidueField) ⊗ₜ[R] v i = b p i at hv'
    calc
      _ = ∑ i, c p i • b p i := by
        apply Finset.sum_congr rfl
        intro i _
        change r i • ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] v i) = c p i • b p i
        rw [hv' i]
        have hr' := congr_fun (hr i) p
        change algebraMap R p.asIdeal.ResidueField (r i) = c p i at hr'
        rw [← hr', ← IsScalarTower.algebraMap_smul p.asIdeal.ResidueField (r i) (b p i)]
      _ = x p := hc p
  have hker : T.ker = (⨅ p : MaximalSpectrum R, p.asIdeal) •
      (⊤ : Submodule R A) := by
    rw [← Ideal.ker_tensorProductMk_quotient A _ hpair]
    ext a
    simp only [LinearMap.mem_ker, LinearMap.pi_apply, funext_iff, Pi.zero_apply]
    constructor
    · intro ha p
      let e := TensorProduct.congr (quotientResidueEquiv p).toLinearEquiv
        (LinearEquiv.refl R A)
      apply e.injective
      simpa [e, T] using ha p
    · intro ha p
      have hp := congrArg
        (TensorProduct.congr (quotientResidueEquiv p).toLinearEquiv
          (LinearEquiv.refl R A)) (ha p)
      simpa [T] using hp
  apply LinearMap.range_eq_top.mp
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (I := ⨅ p : MaximalSpectrum R, p.asIdeal)
  · intro r hr
    apply Ideal.mem_sInf.mpr
    rintro J ⟨_, hJ⟩
    exact (iInf_le (fun p : MaximalSpectrum R ↦ p.asIdeal) ⟨J, hJ⟩) hr
  · rw [← hker]
    intro a _
    obtain ⟨c, hc⟩ := hs (T a)
    have hk : a - q c ∈ T.ker := by
      simp only [LinearMap.mem_ker, map_sub, LinearMap.comp_apply] at hc ⊢
      rw [hc, sub_self]
    have hr : q c ∈ q.range := ⟨c, rfl⟩
    have := Submodule.add_mem_sup hr hk
    simpa using this


end RingTheory
