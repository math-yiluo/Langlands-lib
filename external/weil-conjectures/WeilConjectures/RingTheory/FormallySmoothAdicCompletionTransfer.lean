/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicCompletion
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

universe u v

namespace Algebra

/-- Transfer of adic formal smoothness across the completion map of a local homomorphism.
Source: Stacks Project, More on Algebra, Lemma 15.38.4 (Tag 07ED), (1) implies (3).
The proof restricts a lifting problem over the source completion to the source, applies
formal smoothness after completion of the target, and uses the quotient approximation
of a finitely generated adic completion to recover linearity over the source completion.
(blueprint: lem-weil-pbc-fs-adic-completion-transfer) -/
theorem formallySmoothAdic_completion_transfer
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (ψ : AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
      AdicCompletion (IsLocalRing.maximalIdeal B) B)
    (hψ : ∀ (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) (a : A),
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x =
          Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a →
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) n (ψ x) =
          Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B) ^ n) (φ a)) :
    (letI := φ.toAlgebra
     FormallySmoothAdic A B (IsLocalRing.maximalIdeal B) →
       letI := ψ.toAlgebra
       FormallySmoothAdic (AdicCompletion (IsLocalRing.maximalIdeal A) A)
         (AdicCompletion (IsLocalRing.maximalIdeal B) B)
         ((IsLocalRing.maximalIdeal B).map
           (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)))) := by
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  let CA := AdicCompletion mA A
  let CB := AdicCompletion mB B
  let NA : Ideal CA := mA.map (algebraMap A CA)
  let NB : Ideal CB := mB.map (algebraMap B CB)
  let : Algebra A B := φ.toAlgebra
  intro h
  let : Algebra CA CB := ψ.toAlgebra
  have hcan (a : A) : ψ (algebraMap A CA a) = algebraMap B CB (φ a) := by
    apply AdicCompletion.ext_evalₐ
    intro n
    exact (hψ n _ a (AdicCompletion.evalₐ_of mA n a)).trans
      (AdicCompletion.evalₐ_of mB n (φ a)).symm
  have : IsScalarTower A B CB :=
    IsScalarTower.of_algebraMap_eq (AdicCompletion.algebraMap_apply mB)
  have : IsScalarTower A CA CB := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [AdicCompletion.algebraMap_apply]
    exact (hcan a).symm
  have hCB : FormallySmoothAdic A CB NB :=
    FormallySmoothAdic.adicCompletion A B mB (IsNoetherian.noetherian mB) h
  have hmap : NA.map ψ ≤ NB := by
    rw [Ideal.map_map]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change ψ (algebraMap A CA a) ∈ NB
    rw [hcan]
    exact Ideal.mem_map_of_mem _ (map_nonunit φ a ha)
  have hp (n : ℕ) : (NA ^ n).map ψ ≤ NB ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmap n
  change FormallySmoothAdic CA CB NB
  intro D _ _ J hJ g hg
  let : Algebra A D := ((algebraMap CA D).comp (algebraMap A CA)).toAlgebra
  have : IsScalarTower A CA D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨k, hk, hgk⟩ := hg
  obtain ⟨f, hf⟩ := hCB J hJ (g.restrictScalars A) ⟨k, hk, hgk⟩
  have hfJ : NB ^ k ≤ J.comap f.toRingHom := by
    intro x hx
    change f x ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := DFunLike.congr_fun hf x
    exact he.trans (hgk x hx)
  have hfkill : ∀ x ∈ NB ^ (k + k), f x = 0 := by
    have hp' : NB ^ (k + k) ≤ (J ^ 2).comap f.toRingHom := by
      rw [pow_add, pow_two]
      exact (Ideal.mul_mono hfJ hfJ).trans (Ideal.le_comap_mul _)
    rw [hJ] at hp'
    exact fun x hx ↦ hp' hx
  have hDJ : NA ^ k ≤ J.comap (algebraMap CA D) := by
    intro x hx
    change algebraMap CA D x ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz := hgk (ψ x) (hp k (Ideal.mem_map_of_mem ψ hx))
    exact (g.commutes x).symm.trans hz
  have hDkill : ∀ x ∈ NA ^ (k + k), algebraMap CA D x = 0 := by
    have hp' : NA ^ (k + k) ≤ (J ^ 2).comap (algebraMap CA D) := by
      rw [pow_add, pow_two]
      exact (Ideal.mul_mono hDJ hDJ).trans (Ideal.le_comap_mul _)
    rw [hJ] at hp'
    exact fun x hx ↦ hp' hx
  have hker (n : ℕ) : RingHom.ker (AdicCompletion.evalₐ mA n).toRingHom = NA ^ n := by
    ext x
    rw [RingHom.mem_ker, ← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian mA)]
    change AdicCompletion.evalₐ mA n x = 0 ↔ AdicCompletion.eval mA A n x = 0
    let e := Ideal.quotientEquivAlgOfEq A
      (show (mA ^ n • ⊤ : Ideal A) = mA ^ n by simp)
    change e (AdicCompletion.eval mA A n x) = 0 ↔ AdicCompletion.eval mA A n x = 0
    exact map_eq_zero_iff e e.injective
  have hcomm (x : CA) : f (ψ x) = algebraMap CA D x := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ mA (k + k) x)
    have hea : AdicCompletion.evalₐ mA (k + k) (algebraMap A CA a) =
        Ideal.Quotient.mk (mA ^ (k + k)) a := AdicCompletion.evalₐ_of mA (k + k) a
    have hd : x - algebraMap A CA a ∈ NA ^ (k + k) := by
      rw [← hker, RingHom.mem_ker]
      change AdicCompletion.evalₐ mA (k + k) (x - algebraMap A CA a) = 0
      rw [map_sub, hea, ha, sub_self]
    have hfd : f (ψ (x - algebraMap A CA a)) = 0 :=
      hfkill _ (hp (k + k) (Ideal.mem_map_of_mem ψ hd))
    have hfa : f (ψ x) = f (ψ (algebraMap A CA a)) := by
      simpa only [map_sub, sub_eq_zero] using hfd
    have hda : algebraMap CA D x = algebraMap CA D (algebraMap A CA a) := by
      simpa only [map_sub, sub_eq_zero] using hDkill _ hd
    rw [hfa, hda]
    rw [hcan]
    exact (f.commutes a).trans (IsScalarTower.algebraMap_apply A CA D a)
  let F : CB →ₐ[CA] D := { f.toRingHom with commutes' := hcomm }
  refine ⟨F, ?_⟩
  ext x
  exact DFunLike.congr_fun hf x

end Algebra
