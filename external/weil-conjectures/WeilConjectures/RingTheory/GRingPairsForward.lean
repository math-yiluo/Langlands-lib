/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.QuotientGRing
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.GeometricRegularityFieldIso

@[expose] public section

universe u

/-- Forward implication in the G-ring criterion by pairs of primes. This is the forward
half of Stacks Project, More on Algebra, Lemma 07PN, obtained by identifying each quotient
formal fibre with the corresponding formal fibre of the localization completion.
(blueprint: theorem-finite-etale-covers-proper-henselian--2) -/
theorem isGRing_pairsOfPrimes_forward (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsGRing R) :
    ∀ (q p : Ideal R) [q.IsPrime] [p.IsPrime] (hqp : q ≤ p),
      let pbar := p.map (Ideal.Quotient.mk q)
      letI : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
      let L := Localization.AtPrime pbar
      let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
      let F := TensorProduct (R ⧸ q) q.ResidueField C
      IsNoetherianRing F ∧ Algebra.IsGeometricallyRegular q.ResidueField F := by
  intro q p hq hp hqp
  let B := R ⧸ q
  let pbar := p.map (Ideal.Quotient.mk q)
  let : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
  let L := Localization.AtPrime pbar
  let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
  have : IsNoetherianRing L := inferInstance
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing _
  have hlocal : (algebraMap L C).IsRegular := (isGRing_quotient hR q).2 pbar
  have hbase : (algebraMap B C).IsRegular :=
    RingHom.IsRegular.comp_of_fiber_noetherian
      (IsLocalization.isRegular_and_fiber pbar.primeCompl).1 hlocal
      (fun r _ ↦ Ideal.isNoetherianRing_fiber r)
  rw [RingHom.IsRegular, toAlgebra_algebraMap] at hbase
  let r : Ideal B := ⊥
  have : r.IsPrime := inferInstance
  let σ : r.ResidueField ≃ₐ[B] q.ResidueField :=
    IsLocalization.algEquiv (nonZeroDivisors B) r.ResidueField q.ResidueField
  let e := Algebra.TensorProduct.congr σ (AlgEquiv.refl : C ≃ₐ[B] C)
  have hgeom := Algebra.isGeometricallyRegular_of_fieldIso σ.toRingEquiv e.toRingEquiv
    (by
      intro x y
      induction y using TensorProduct.inductionOn with
      | tmul a c =>
        change σ (x * a) ⊗ₜ[B] c = σ x • (σ a ⊗ₜ[B] c)
        simp [Algebra.smul_def]
      | add a b ha hb => simp_all) (hbase.2 r)
  exact ⟨hgeom.1, hgeom⟩
