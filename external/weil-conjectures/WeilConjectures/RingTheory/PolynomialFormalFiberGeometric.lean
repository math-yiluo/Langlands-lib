/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Polynomial.Basic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.FormallySmoothCompleteLocalRegular
import WeilConjectures.RingTheory.HypersurfaceDerivationRegular
import WeilConjectures.RingTheory.PolynomialLocalCompletionFormallySmooth
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import WeilConjectures.RingTheory.PolynomialLinearFormalFiberPresentation
import WeilConjectures.RingTheory.PolynomialFormalFiberFiniteReduction
@[expose] public section
universe u
namespace Polynomial
/-- A finite product is regular: every prime comes from one factor, and projection
identifies its localization with the factor's localization. This also handles the
empty product. Source: Stacks Tag 07PU, first proof paragraph. -/
private theorem regular_finite_product (ι : Type*) [Finite ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsRegularRing (R i)] : IsRegularRing (∀ i, R i) := by
  classical
  apply isRegularRing_iff.mpr
  intro p hp
  obtain ⟨i, q, heq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq (⟨p, hp⟩ : PrimeSpectrum _)
  have heq' : q.asIdeal.comap (Pi.evalRingHom R i) = p := congrArg PrimeSpectrum.asIdeal heq
  subst p
  let e := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
    (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- The formally smooth coefficient map to the completed polynomial local ring is
regular by Tag 07PM; its zero fibre is regular by testing the trivial field extension.
Source: Stacks Tag 07PU, second proof paragraph. -/
private theorem coefficient_generic_fiber_regular
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsRegularRing ((⊥ : Ideal A).Fiber C) := by
  let T := Localization.AtPrime q
  let C := AdicCompletion (IsLocalRing.maximalIdeal T) T
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing _
  have hlocal : IsLocalHom (algebraMap A T) := by
    apply ((IsLocalRing.local_hom_TFAE _).out 1 5).mpr
    rw [IsScalarTower.algebraMap_eq A (Polynomial A) T, ← Ideal.comap_comap]
    rw [show (IsLocalRing.maximalIdeal T).comap
      (algebraMap (Polynomial A) T) = q from
        IsLocalization.AtPrime.under_maximalIdeal T q]
    exact hq
  let := hlocal
  have : IsLocalHom (algebraMap A C) := by
    rw [IsScalarTower.algebraMap_eq A T C]
    infer_instance
  have hfs : Algebra.FormallySmoothAdic A C (IsLocalRing.maximalIdeal C) := by
    have h := Algebra.polynomial_local_completion_formallySmoothAdic A q
    rw [Localization.AtPrime.map_eq_maximalIdeal] at h
    have heq : IsLocalRing.maximalIdeal C = q.map (algebraMap (Polynomial A) C) := by
      rw [AdicCompletion.maximalIdeal_eq_map]
      change (IsLocalRing.maximalIdeal T).map (algebraMap T C) = _
      calc
        _ = (q.map (algebraMap (Polynomial A) T)).map (algebraMap T C) :=
          congrArg (Ideal.map (algebraMap T C))
            (Localization.AtPrime.map_eq_maximalIdeal (I := q)).symm
        _ = _ := by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    rw [heq]
    exact h
  have hreg := RingHom.isRegular_of_formallySmoothAdic (algebraMap A C) (by
    rw [toAlgebra_algebraMap]
    exact hfs)
  rw [RingHom.IsRegular, toAlgebra_algebraMap] at hreg
  have hgeom : Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).Fiber C) := hreg.2 (⊥ : Ideal A)
  have := hgeom.2 (⊥ : Ideal A).ResidueField
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.lid (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber C)).toRingEquiv

/-- Geometric-regularity component of the formal-fibre theorem.
Source: Stacks Project, More on Algebra, Lemma 07PU.
(blueprint: lem-weil-pbc-another-helper-g-ring-geometric-component)
Proof: after a finite purely inseparable residue-field extension, use the
completion finite-extension decomposition to write the base-changed fibre as a
finite product. Each factor is regular by the formally smooth completion and
derivation quotient lemmas, and a finite product of regular rings is regular;
this is precisely geometric regularity. -/
theorem formalFiber_isGeometricallyRegular_component (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) (hp : p.Prime) [CharP (Localization.AtPrime (⊥ : Ideal A)) p]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    Algebra.IsGeometricallyRegular r.ResidueField (r.Fiber C) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing _
  refine ⟨Ideal.isNoetherianRing_fiber r, ?_⟩
  intro L _ _ _ _
  obtain ⟨n, B, rings, domains, noeth, locals, complete, q', qmax, s, sprime,
    fraction, hq', _, hs, hsB, ⟨e⟩⟩ :=
    formalFiber_finiteExtension_reduction A p hp q hq r hrq hr hrA L
  let := rings
  let := domains
  let := noeth
  let := locals
  let := complete
  let := qmax
  let := sprime
  let := fraction
  let C' (i : Fin n) :=
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime (q' i)))
      (Localization.AtPrime (q' i))
  have hregular (i : Fin n) : IsRegularRing ((s i).Fiber (C' i)) := by
    let R := (⊥ : Ideal (B i)).Fiber (C' i)
    have : IsRegularRing R := coefficient_generic_fiber_regular (B i) (q' i) (hq' i)
    obtain ⟨f, D, hD, ⟨ef⟩⟩ :=
      linear_formalFiber_hypersurface (B i) (q' i) (s i) (hs i) (hsB i)
    have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (D f)) := by
      rw [hD, map_one]
      exact isUnit_one
    have := IsRegularRing.quotient_span_singleton_of_isUnit_derivation R f D hunit
    exact IsRegularRing.of_ringEquiv ef
  let := hregular
  have := regular_finite_product (Fin n) (fun i ↦ (s i).Fiber (C' i))
  exact IsRegularRing.of_ringEquiv e.symm
end Polynomial
