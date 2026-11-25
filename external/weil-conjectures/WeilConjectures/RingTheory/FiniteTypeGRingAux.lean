/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.PolynomialGRingComparison
import WeilConjectures.RingTheory.GRingEquiv
import WeilConjectures.RingTheory.GRingMaximalIdealCriterion
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Algebra.MvPolynomial.Equiv
import WeilConjectures.RingTheory.QuotientGRing
import WeilConjectures.RingTheory.RegularPermanence

/-! Auxiliary formal-fibre step for finite type algebras over G-rings.

Source: Stacks Project, More on Algebra, Proposition 07PV (blueprint:
lem-weil-pbc-finite-type-over-g-ring), the maximal-ideal and completion steps.
-/

@[expose] public section

universe u v

/-- If `R` is a G-ring and `S` is finite type over `R`, then every prime-local
completion map of `S` is regular.  This is the formal-fibre part of the proof of
Proposition 07PV: write `S` as a quotient of a polynomial algebra, reduce to a
maximal ideal, localize the base at its contraction, and use regular base change,
the complete-local polynomial case, composition, and faithfully-flat descent.
(blueprint: lem-weil-pbc-finite-type-over-g-ring-formal-fibres)
-/
theorem finiteType_completion_regular
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (hR : IsGRing R) [Algebra.FiniteType R S] :
    ∀ (p : Ideal S) [p.IsPrime],
      RingHom.IsRegular
        (algebraMap (Localization.AtPrime p)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p))) := by
  have hpoly : ∀ (A : Type u) [CommRing A], IsGRing A → IsGRing (Polynomial A) := by
    intro A _ hA
    have : IsNoetherianRing A := hA.1
    apply (isGRing_iff_maximalIdeal (Polynomial A)).2
    intro Q hQ
    obtain ⟨B, hB, hBlocal, hBnoeth, φ, hflat, hlocal, hregular⟩ :=
      exists_polynomial_flat_local_regular_completion_comparison A hA Q
    let L := Localization.AtPrime Q
    let Lhat := AdicCompletion (IsLocalRing.maximalIdeal L) L
    let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
    obtain ⟨φhat, _, hcomm, hflatHat⟩ :=
      flat_adicCompletion_of_flat_local L B φ hflat hlocal
    have hlocalHat : IsLocalHom φhat := by
      apply ((IsLocalRing.local_hom_TFAE φhat).out 1 3).mpr
      rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hcomm]
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      exact map_nonunit (algebraMap B Bhat) (φ x) (hlocal x hx)
    let : Algebra Lhat Bhat := φhat.toAlgebra
    let : Algebra L Bhat := (φhat.comp (algebraMap L Lhat)).toAlgebra
    let : IsScalarTower L Lhat Bhat := IsScalarTower.of_algebraMap_eq' rfl
    have : IsLocalHom (algebraMap Lhat Bhat) := hlocalHat
    have : Module.Flat Lhat Bhat := hflatHat
    have : Module.FaithfullyFlat Lhat Bhat :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    apply RingHom.isRegular_of_isRegular_comp (C := Bhat)
    · change (φhat.comp (algebraMap L Lhat)).IsRegular
      rw [hcomm]
      exact hregular
    · exact hflatHat
    · exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  have hmv : ∀ n : ℕ, IsGRing (MvPolynomial (Fin n) R) := by
    intro n
    induction n with
    | zero =>
      exact isGRing_of_ringEquiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm hR
    | succ n ih =>
      exact isGRing_of_ringEquiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv
        (hpoly _ ih)
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := S)).mp inferInstance
  have hquot := isGRing_quotient (hmv n) (RingHom.ker f.toRingHom)
  have hS := isGRing_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf) hquot
  exact hS.2
