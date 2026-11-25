/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.KrullDimension.Field
import WeilConjectures.RingTheory.LengthQuotSMulTopFractionFieldSubmodule

/-!
# Residue fields above a one-dimensional local domain

Source: Stacks Project, Algebra, Tag 031F, Lemma 10.119.10
(blueprint: lem-weil-pbc-dim-one-residue-field-extensions-finite).
-/

@[expose] public section

set_option autoImplicit false

universe uR uS uK uL

namespace Ideal

/-- Stacks Project, Tag 031F
(blueprint: lem-weil-pbc-dim-one-residue-field-extensions-finite).
For an injection of domains inducing a finite extension of fraction fields, with the base
Noetherian local of dimension one, primes above its maximal ideal are maximal, there are
finitely many, and their residue fields are finite extensions via the induced field map.

Proof: choose a nonzero element `x` of the maximal ideal. View `S` as an `R`-submodule of
`L`, and identify `L` with a finite direct sum of `K` using a basis. Apply
lem-weil-pbc-dim-one-submodule-quotient-finite-length to get finite length of `S/xS`.
The surjection onto `S/mS` preserves finite length: strict chains lift to strict chains.
Since the action factors through `R/m`, submodules are its vector subspaces, so this
closed fibre is finite dimensional. Apply lem-weil-pbc-finite-dim-algebra-artinian and
lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum to the fibre, then
lem-weil-pbc-spec-quotient-homeomorphism-zero-locus to identify its primes with the primes
above `m`. They are finitely many and maximal, including the case of the zero fibre.
Each quotient by such a prime is a quotient of the finite-dimensional fibre. Maximality
identifies it with the localization residue field, by sending a fraction to the quotient
of its numerator and denominator. This gives the finite residue extension. -/
theorem dim_one_residue_fields_finite
    (R : Type uR) (S : Type uS) (K : Type uK) (L : Type uL)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [FiniteDimensional K L]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (hcompat : ∀ r : R, algebraMap K L (algebraMap R K r) = algebraMap S L (φ r))
    (hdim : ringKrullDim R = 1) :
    (∀ n : PrimeSpectrum S,
      n.asIdeal.comap φ = IsLocalRing.maximalIdeal R → n.asIdeal.IsMaximal) ∧
    Set.Finite {n : PrimeSpectrum S | n.asIdeal.comap φ = IsLocalRing.maximalIdeal R} ∧
    (∀ (n : PrimeSpectrum S) (hn : n.asIdeal.comap φ = IsLocalRing.maximalIdeal R),
      letI := (Ideal.ResidueField.map (IsLocalRing.maximalIdeal R) n.asIdeal φ
        hn.symm).toAlgebra
      FiniteDimensional (IsLocalRing.maximalIdeal R).ResidueField n.asIdeal.ResidueField) := by
  classical
  let := φ.toAlgebra
  let p := IsLocalRing.maximalIdeal R
  have : Module.Finite p.ResidueField (p.Fiber S) := by
    have hp : p ≠ ⊥ := by
      intro h
      have hfield : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr h
      have hz := ringKrullDim_eq_zero_of_isField hfield
      rw [hdim] at hz
      exact one_ne_zero hz
    obtain ⟨x, hxp, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    have hxφ : φ x ≠ 0 := fun h ↦ hx (hφ (h.trans φ.map_zero.symm))
    let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
    let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun r ↦ hcompat r
    let e := (Module.finBasis K L).equivFun
    let f : S →ₗ[R] (Fin (Module.finrank K L) → K) :=
      (e.restrictScalars R).toLinearMap.comp (IsScalarTower.toAlgHom R S L).toLinearMap
    have hf : Function.Injective f := e.injective.comp (IsFractionRing.injective S L)
    let E := LinearEquiv.ofInjective f hf
    have hlen :=
      (Submodule.length_quotSMulTop_le_of_ringKrullDim_eq_one_of_isLocalRing
        (Module.finrank K L) f.range hdim x
        (fun h ↦ hxφ (by rw [h, map_zero]))).2.1
    have hfin : IsFiniteLength R (QuotSMulTop x S) :=
      (QuotSMulTop.congr x E.symm).isFiniteLength
        (Module.length_ne_top_iff.mp hlen.ne)
    let g : S →ₗ[R] p.Fiber S := Algebra.TensorProduct.includeRight.toLinearMap
    have hg : Function.Surjective g :=
      Algebra.TensorProduct.includeRight_surjective S p.algebraMap_residueField_surjective
    let : DistribMulAction R (Submodule R S) := Submodule.pointwiseDistribMulAction
    have hkill : x • (⊤ : Submodule R S) ≤ LinearMap.ker g := by
      intro y hy
      obtain ⟨z, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y x ⊤).mp hy
      change g (x • z) = 0
      rw [map_smul, ← IsScalarTower.algebraMap_smul p.ResidueField x]
      rw [Ideal.algebraMap_residueField_eq_zero.mpr hxp, zero_smul]
    let q := (x • (⊤ : Submodule R S)).liftQ g hkill
    have hq : Function.Surjective q := by
      intro y
      obtain ⟨z, rfl⟩ := hg y
      exact ⟨Submodule.Quotient.mk z, rfl⟩
    have hfin' : IsFiniteLength R (p.Fiber S) := hfin.of_surjective hq
    have : IsNoetherian R (p.Fiber S) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin').1
    have : Module.Finite R (p.Fiber S) := inferInstance
    exact Module.Finite.of_restrictScalars_finite R p.ResidueField (p.Fiber S)
  let : IsArtinianRing (p.Fiber S) := .of_finite p.ResidueField _
  let e := PrimeSpectrum.preimageEquivFiber R S ⟨p, inferInstance⟩
  have hsurj : Function.Surjective
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) :=
    Algebra.TensorProduct.includeRight_surjective S p.algebraMap_residueField_surjective
  have hmax : ∀ n : PrimeSpectrum S, n.asIdeal.comap φ = p → n.asIdeal.IsMaximal := by
    intro n hn
    let q := e ⟨n, PrimeSpectrum.ext hn⟩
    have : q.asIdeal.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal q.asIdeal).mp q.isPrime
    have hq := (e.symm_apply_apply ⟨n, PrimeSpectrum.ext hn⟩)
    have heq : q.asIdeal.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom = n.asIdeal :=
      congrArg (fun a ↦ a.val.asIdeal) hq
    rw [← heq]
    exact Ideal.comap_isMaximal_of_surjective _ hsurj
  refine ⟨hmax, ?_, ?_⟩
  · have hf : (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        {⟨p, inferInstance⟩}).Finite := by
      have : Finite (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
          {⟨p, inferInstance⟩}) := e.finite_iff.mpr inferInstance
      exact Set.toFinite _
    convert hf using 1
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hn ↦ PrimeSpectrum.ext hn, fun hn ↦ congrArg PrimeSpectrum.asIdeal hn⟩
  · intro n hn
    let : n.asIdeal.IsMaximal := hmax n hn
    let := (Ideal.ResidueField.map p n.asIdeal φ hn.symm).toAlgebra
    let : IsScalarTower R p.ResidueField n.asIdeal.ResidueField :=
      IsScalarTower.of_algebraMap_eq fun r ↦
        (Ideal.ResidueField.map_algebraMap p n.asIdeal φ hn.symm r).symm
    let f : p.Fiber S →ₐ[p.ResidueField] n.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift (Algebra.ofId p.ResidueField n.asIdeal.ResidueField)
        (IsScalarTower.toAlgHom R S n.asIdeal.ResidueField) (fun _ _ ↦ .all _ _)
    exact Module.Finite.of_surjective f.toLinearMap (by
      intro y
      obtain ⟨s, rfl⟩ := n.asIdeal.algebraMap_residueField_surjective y
      exact ⟨TensorProduct.tmul R 1 s, by simp [f]⟩)

end Ideal
