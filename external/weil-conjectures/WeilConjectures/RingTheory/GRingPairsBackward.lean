/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.FormalFibreQuotientIso
import WeilConjectures.RingTheory.GeometricRegularityFieldIso
import WeilConjectures.RingTheory.RegularThroughLocalization

/-!
# Backward implication of the G-ring criterion

Source: Stacks Project, More on Algebra, proof of Lemma 07PN.
(blueprint: theorem-finite-etale-covers-proper-henselian--2)
-/

@[expose] public section

universe u

private theorem geometricallyRegular_of_subsingleton
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Subsingleton A] :
    Algebra.IsGeometricallyRegular k A := by
  refine ⟨inferInstance, ?_⟩
  intro K _ _ _ _
  refine ⟨?_⟩
  intro q hq
  exact False.elim (hq.ne_top (Subsingleton.elim _ _))

private theorem completion_fiber_subsingleton
    (R : Type u) [CommRing R] (q p : Ideal R) [q.IsPrime] [p.IsPrime]
    (hqp : ¬ q ≤ p) :
    Subsingleton (q.Fiber (AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))) := by
  classical
  let L := Localization.AtPrime p
  let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
  obtain ⟨x, hxq, hxp⟩ := IsConcreteLE.not_le_iff_exists.mp hqp
  have hu : IsUnit (algebraMap R C x) := by
    rw [IsScalarTower.algebraMap_apply R L C]
    exact (IsLocalization.map_units L (⟨x, hxp⟩ : p.primeCompl)).map (algebraMap L C)
  have hz : algebraMap R (q.Fiber C) x = 0 := by
    change (algebraMap R q.ResidueField x) ⊗ₜ[R] (1 : C) = 0
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hxq, TensorProduct.zero_tmul]
  have hzunit : IsUnit (0 : q.Fiber C) := by
    rw [← hz]
    have hu' := hu.map
      (Algebra.TensorProduct.includeRight : C →ₐ[R] q.Fiber C).toRingHom
    change IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] q.Fiber C)
      (algebraMap R C x)) at hu'
    rw [AlgHom.commutes] at hu'
    exact hu'
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hzunit)

/-- Backward implication in the G-ring criterion by pairs of primes. This is the backward
half of Stacks Project, More on Algebra, Lemma 07PN, using the formal-fibre description of
regular completion maps and the quotient formal-fibre identification.
(blueprint: theorem-finite-etale-covers-proper-henselian--2) -/
theorem isGRing_pairsOfPrimes_backward (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (q p : Ideal R) [q.IsPrime] [p.IsPrime] (hqp : q ≤ p),
      let pbar := p.map (Ideal.Quotient.mk q)
      letI : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
      let L := Localization.AtPrime pbar
      let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
      let F := TensorProduct (R ⧸ q) q.ResidueField C
      IsNoetherianRing F ∧ Algebra.IsGeometricallyRegular q.ResidueField F) :
    IsGRing R := by
  refine ⟨inferInstance, ?_⟩
  intro p hp
  let L := Localization.AtPrime p
  let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
  apply RingHom.isRegular_of_comp_algebraMap_localization (A := R)
    (A' := L) (C := C) p.primeCompl
  rw [RingHom.IsRegular, toAlgebra_algebraMap]
  refine ⟨?_, ?_⟩
  · rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.trans R L C
  · intro q hq
    by_cases hqp : q ≤ p
    · obtain ⟨e⟩ := nonempty_formalFibre_quotient_algEquiv R q p hqp
      exact Algebra.isGeometricallyRegular_of_fieldIso (RingEquiv.refl q.ResidueField)
        e.toRingEquiv (fun x a ↦ e.toLinearEquiv.map_smul x a) (h q p hqp).2
    · have := completion_fiber_subsingleton R q p hqp
      exact geometricallyRegular_of_subsingleton q.ResidueField (q.Fiber C)
