/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import WeilConjectures.RingTheory.PowerSeriesNormalDomain
import WeilConjectures.RingTheory.TateN2CompletePrincipal
import WeilConjectures.RingTheory.IsN2OfFiniteExtension
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! Auxiliary N-2 assertion for power series.

Source: Stacks Project, Algebra, Lemma Tag 032Q.
(blueprint: lem-weil-pbc-power-series-n2-aux).
-/

@[expose] public section

universe u

namespace PowerSeries

private theorem finite_power_series_extension (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] : Module.Finite (PowerSeries R) (PowerSeries A) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := A)
  apply Module.finite_def.mpr
  apply Submodule.fg_iff_exists_fin_generating_family.mpr
  refine ⟨n, fun i ↦ C (s i), ?_⟩
  apply top_unique
  intro f _
  have hc (k : ℕ) : ∃ c : Fin n → R, ∑ i, c i • s i = coeff k f := by
    apply (Submodule.mem_span_range_iff_exists_fun R).mp
    rw [hs]
    exact Submodule.mem_top
  choose c hc using hc
  apply (Submodule.mem_span_range_iff_exists_fun (PowerSeries R)).mpr
  refine ⟨fun i ↦ mk (fun k ↦ c k i), ?_⟩
  ext k
  simpa only [map_sum, Algebra.smul_def, algebraMap_apply'', coeff_mul_C,
    coeff_map, coeff_mk] using hc k

private theorem isN2_quotient_X (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A]
    [IsDomain (PowerSeries A ⧸ Ideal.span ({X} : Set (PowerSeries A)))]
    (hA : IsN2 A (FractionRing A)) :
    IsN2 (PowerSeries A ⧸ Ideal.span ({X} : Set (PowerSeries A)))
      (FractionRing (PowerSeries A ⧸ Ideal.span ({X} : Set (PowerSeries A)))) := by
  let I : Ideal (PowerSeries A) := Ideal.span ({X} : Set (PowerSeries A))
  have hI : I = RingHom.ker (constantCoeff : PowerSeries A →+* A) := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]
  let e : (PowerSeries A ⧸ I) ≃+* A := (Ideal.quotEquivOfEq hI).trans
    ((constantCoeff : PowerSeries A →+* A).quotientKerEquivOfSurjective
      (fun a ↦ ⟨C a, constantCoeff_C a⟩))
  let : Algebra A (PowerSeries A ⧸ I) := e.symm.toRingHom.toAlgebra
  let : Module A (PowerSeries A ⧸ I) := e.symm.toRingHom.toAlgebra.toModule
  have : Module.Finite A (PowerSeries A ⧸ I) :=
    RingHom.Finite.of_surjective e.symm.toRingHom e.symm.surjective
  exact isN2_of_finite_domain_extension A (PowerSeries A ⧸ I)
    (FractionRing A) (FractionRing (PowerSeries A ⧸ I)) e.symm.injective hA

/-- The N-2 part of the power-series lemma.  This is the normalization and Tate
argument of Tag 032Q, isolated so that the Noetherian and domain conclusions can
be discharged directly from Mathlib instances.
(blueprint: lem-weil-pbc-power-series-n2-aux). -/
theorem isN2_power_series (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (hR : IsN2 R (FractionRing R)) :
    IsN2 (PowerSeries R) (FractionRing (PowerSeries R)) := by
  let A := integralClosure R (FractionRing R)
  let : Module.Finite R A := hR (FractionRing R)
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  let : IsIntegrallyClosed A :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have hinj : Function.Injective (algebraMap R A) := by
    intro r s hrs
    apply IsFractionRing.injective R (FractionRing R)
    exact congrArg (fun a : A ↦ (a : FractionRing R)) hrs
  have hA : IsN2 A (FractionRing A) :=
    isN2_of_finite_domain_extension R A (FractionRing R) (FractionRing A) hinj hR
  have : Module.Finite (PowerSeries R) (PowerSeries A) := finite_power_series_extension R A
  apply isN2_of_finite_extension (PowerSeries R) (PowerSeries A)
    (FractionRing (PowerSeries R)) (FractionRing (PowerSeries A))
  · exact map_injective (algebraMap R A) hinj
  · have : (Ideal.span ({X} : Set (PowerSeries A))).IsPrime := span_X_isPrime
    exact tate_n2_complete_principal (PowerSeries A) (FractionRing (PowerSeries A)) X
      (noetherian_normal_domain A).2.2 (isN2_quotient_X A hA)

end PowerSeries
