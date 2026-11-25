/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

/-!
# Residue-field criteria for finite-projective maps

Source: Stacks Project, Algebra, Tag 00O0, Lemma `cokernel-flat`, parts (1) and (3)
(blueprint: lem-pc-finite-projective-cokernel-localization).
-/

universe u v w

namespace Module

/-- The residue criterion gives a split injection over the local ring at the prime. -/
private theorem split_atPrime
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (φ : M →ₗ[R] N) (p : Ideal R) [p.IsPrime]
    (hφ : Function.Injective (φ.baseChange p.ResidueField)) :
    ∃ v : (TensorProduct R (Localization.AtPrime p) N) →ₗ[Localization.AtPrime p]
      (TensorProduct R (Localization.AtPrime p) M),
      v.comp (φ.baseChange (Localization.AtPrime p)) = LinearMap.id := by
  let L := Localization.AtPrime p
  let K := p.ResidueField
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R L K K M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R L K K N
  have hcomm : eN.toLinearMap.comp ((φ.baseChange L).baseChange K) =
      (φ.baseChange K).comp eM.toLinearMap := by
    ext
    simp [eM, eN]
  have hK : Function.Injective ((φ.baseChange L).baseChange K) := by
    intro x y h
    apply eM.injective
    apply hφ
    have he := congrArg eN h
    change eN.toLinearMap _ = eN.toLinearMap _ at he
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hcomm] at he
    exact he
  have : Module.Free L (TensorProduct R L N) := Module.free_of_flat_of_isLocalRing
  exact (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (φ.baseChange L)).mpr hK

/-- Spread a local retraction: finite presentation clears its denominators, and
finiteness clears the error in its left-inverse identity. -/
private theorem spread_split
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
    (φ : M →ₗ[R] N) (p : Ideal R) [p.IsPrime]
    (v : (TensorProduct R (Localization.AtPrime p) N) →ₗ[Localization.AtPrime p]
      (TensorProduct R (Localization.AtPrime p) M))
    (hv : v.comp (φ.baseChange (Localization.AtPrime p)) = LinearMap.id) :
    ∃ f : R, f ∉ p ∧ ∃ w : (TensorProduct R (Localization.Away f) N) →ₗ[Localization.Away f]
      (TensorProduct R (Localization.Away f) M),
      w.comp (φ.baseChange (Localization.Away f)) = LinearMap.id := by
  let L := Localization.AtPrime p
  let lM := TensorProduct.mk R L M 1
  let lN := TensorProduct.mk R L N 1
  obtain ⟨ψ, s, hψ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    p.primeCompl lM ((v.restrictScalars R).comp lN)
  have h : lM.comp (ψ.comp φ) = lM.comp (s.1 • LinearMap.id) := by
    ext x
    have hh := LinearMap.congr_fun hψ (φ x)
    have hh' := LinearMap.congr_fun hv (TensorProduct.tmul R (1 : L) x)
    change TensorProduct.tmul R (1 : L) (ψ (φ x)) =
      s.1 • v (TensorProduct.tmul R (1 : L) (φ x)) at hh
    have hval : v (TensorProduct.tmul R (1 : L) (φ x)) = TensorProduct.tmul R (1 : L) x := hh'
    simpa [lM, hval] using hh
  obtain ⟨t, ht⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    p.primeCompl lM (ψ.comp φ) (s.1 • LinearMap.id) h
  let f : R := s.1 * t.1
  let A := Localization.Away f
  have hu : IsUnit (algebraMap R A f) := IsLocalization.Away.algebraMap_isUnit f
  have hs : IsUnit (algebraMap R A s.1) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R A) (Dvd.intro t.1 rfl)) hu
  have ht' : IsUnit (algebraMap R A t.1) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R A) (Dvd.intro s.1 (mul_comm _ _))) hu
  have heq : (ψ.baseChange A).comp (φ.baseChange A) =
      (algebraMap R A s.1) • LinearMap.id := by
    apply ht'.smul_left_cancel.mp
    change t.1 • (ψ.comp φ) = t.1 • (s.1 • LinearMap.id) at ht
    have hh := congrArg (LinearMap.baseChange A) ht
    simpa only [LinearMap.baseChange_smul, LinearMap.baseChange_comp,
      LinearMap.baseChange_id, algebraMap_smul] using hh
  refine ⟨f, (p.primeCompl.mul_mem s.2 t.2), (↑(hs.unit⁻¹) : A) • ψ.baseChange A, ?_⟩
  rw [LinearMap.smul_comp, heq, smul_smul, IsUnit.val_inv_mul, one_smul]

/-- Source: Stacks Project, Algebra, Tag 00O0, Lemma `cokernel-flat`, parts (1) and (3)
(blueprint: lem-pc-finite-projective-cokernel-localization).

Proof: At the prime, the projective target is finite free. The residue-field
injectivity criterion gives a left inverse over the local ring. Finite presentation
of the target clears the denominators of this inverse; finiteness of the source clears
the error in its identity. Inverting the product gives a split injection. Its cokernel
is a direct summand of the finite projective target, hence finite projective.
For the bijective clause, right exactness makes the residue of the local cokernel zero.
Nakayama makes the local cokernel zero, so the map at the prime is bijective. Finite
presentation spreads this isomorphism to a principal neighborhood. -/
theorem finiteProjectiveCokernel_residue_localization
    {R : Type u} [CommRing R]
    {P₁ : Type v} [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁]
    [Module.Projective R P₁]
    {P₂ : Type w} [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂]
    [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (p : Ideal R) [p.IsPrime] :
    (Function.Injective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        Function.Injective (φ.baseChange (Localization.Away f)) ∧
        Module.Finite (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f))) ∧
        Module.Projective (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f)))) ∧
    (Function.Bijective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧ Function.Bijective (φ.baseChange (Localization.Away f))) := by
  constructor
  · intro hφ
    have : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
    obtain ⟨v, hv⟩ := split_atPrime φ p hφ
    obtain ⟨f, hf, w, hw⟩ := spread_split φ p v hv
    have hinj : Function.Injective (φ.baseChange (Localization.Away f)) :=
      Function.HasLeftInverse.injective ⟨w, LinearMap.congr_fun hw⟩
    let q := LinearMap.range (φ.baseChange (Localization.Away f))
    have hsplit := (Function.Exact.split_tfae
      (φ.baseChange (Localization.Away f)).exact_map_mkQ_range hinj
      (Submodule.mkQ_surjective q)).out 1 2
    obtain ⟨i, hi⟩ := hsplit.mpr ⟨w, hw⟩
    exact ⟨f, hf, hinj, inferInstance, Module.Projective.of_split i q.mkQ hi⟩
  · intro hφ
    let L := Localization.AtPrime p
    let K := p.ResidueField
    let l := φ.baseChange L
    obtain ⟨v, hv⟩ := split_atPrime φ p hφ.1
    have hinj : Function.Injective l :=
      Function.HasLeftInverse.injective ⟨v, LinearMap.congr_fun hv⟩
    let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R L K K P₁
    let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R L K K P₂
    have hcomm : eN.toLinearMap.comp (l.baseChange K) =
        (φ.baseChange K).comp eM.toLinearMap := by
      ext
      simp [eM, eN, l]
    have hsurjK : Function.Surjective (l.baseChange K) := by
      intro y
      obtain ⟨x, hx⟩ := hφ.2 (eN y)
      refine ⟨eM.symm x, eN.injective ?_⟩
      change eN.toLinearMap _ = _
      rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]
      simpa only [LinearEquiv.coe_coe, eM.apply_symm_apply] using hx
    let q := LinearMap.range l
    have hzero : (q.mkQ.baseChange K).comp (l.baseChange K) = 0 := by
      rw [← LinearMap.baseChange_comp, l.exact_map_mkQ_range.linearMap_comp_eq_zero,
        LinearMap.baseChange_zero]
    have : Subsingleton (TensorProduct L K ((TensorProduct R L P₂) ⧸ q)) := by
      apply (subsingleton_iff_forall_eq 0).mpr
      intro z
      obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective K (Submodule.mkQ_surjective q) z
      obtain ⟨x, rfl⟩ := hsurjK y
      exact LinearMap.congr_fun hzero x
    have : Subsingleton ((TensorProduct R L P₂) ⧸ q) :=
      (IsLocalRing.subsingleton_tensorProduct (R := L)).mp inferInstance
    have hsurj : Function.Surjective l := by
      rw [← LinearMap.range_eq_top]
      exact Submodule.Quotient.subsingleton_iff.mp inferInstance
    let lM := TensorProduct.mk R L P₁ 1
    let lN := TensorProduct.mk R L P₂ 1
    have heq : IsLocalizedModule.map p.primeCompl lM lN φ = l.restrictScalars R := by
      apply IsLocalizedModule.ext p.primeCompl lM (IsLocalizedModule.map_units lN)
      ext x
      change IsLocalizedModule.map p.primeCompl lM lN φ (lM x) = lN (φ x)
      exact IsLocalizedModule.map_apply p.primeCompl lM lN φ x
    have : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
    have hloc : Function.Bijective (IsLocalizedModule.map p.primeCompl lM lN φ) := by
      rw [heq]
      exact ⟨hinj, hsurj⟩
    obtain ⟨f, hf, hbij⟩ := Module.FinitePresentation.exists_notMem_bijective
      φ p lM lN hloc
    let lMf := TensorProduct.mk R (Localization.Away f) P₁ 1
    let lNf := TensorProduct.mk R (Localization.Away f) P₂ 1
    rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective lMf lNf] at hbij
    have heqf : IsLocalizedModule.map (Submonoid.powers f) lMf lNf φ =
        (φ.baseChange (Localization.Away f)).restrictScalars R := by
      apply IsLocalizedModule.ext (Submonoid.powers f) lMf (IsLocalizedModule.map_units lNf)
      ext x
      change IsLocalizedModule.map (Submonoid.powers f) lMf lNf φ (lMf x) = lNf (φ x)
      exact IsLocalizedModule.map_apply (Submonoid.powers f) lMf lNf φ x
    rw [heqf] at hbij
    exact ⟨f, hf, hbij⟩

end Module
