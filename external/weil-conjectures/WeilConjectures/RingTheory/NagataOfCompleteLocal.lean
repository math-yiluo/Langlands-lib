/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension
import WeilConjectures.RingTheory.PowerSeriesN2
import WeilConjectures.RingTheory.TateN2CompletePrincipal
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Complete Noetherian local rings are Nagata

Source: Stacks Project, Algebra, Lemma 10.162.8 (Tag 032W)
(blueprint: lem-weil-pbc-complete-local-nagata).
-/

@[expose] public section

universe u

private instance mvPowerSeries_isDomain (σ : Type) (A : Type u)
    [CommRing A] [IsDomain A] : IsDomain (MvPowerSeries σ A) :=
  NoZeroDivisors.to_isDomain _

-- Step 4: allow any fraction field, including one in a different universe.
private theorem isN2_field (F : Type u) (K : Type*) [Field F] [Field K]
    [Algebra F K] [IsFractionRing F K] : IsN2 F K := by
  intro L _ _ _ _ _
  have : Module.Finite F K :=
    Module.Finite.equiv
      ((FractionRing.algEquiv F F).symm.trans (FractionRing.algEquiv F K)).toLinearEquiv
  have : Module.Finite F L := Module.Finite.trans K L
  exact Module.IsNoetherian.finite F (integralClosure F L)

-- Step 2: an isomorphism is an injective finite extension, so N-2 ascends.
private theorem isN2_equiv (A B : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [IsDomain B] (e : A ≃+* B)
    (hA : IsN2 A (FractionRing A)) : IsN2 B (FractionRing B) := by
  let : Algebra A B := e.toRingHom.toAlgebra
  have : Module.Finite A B := RingHom.Finite.of_surjective e.toRingHom e.surjective
  exact isN2_of_finite_domain_extension A B (FractionRing A) (FractionRing B)
    e.injective hA

-- Step 3: use the zero-variable and successor equivalences to iterate Tag 032Q.
private theorem isN2_mvPowerSeries (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hA : IsN2 A (FractionRing A)) (d : ℕ) :
    IsN2 (MvPowerSeries (Fin d) A) (FractionRing (MvPowerSeries (Fin d) A)) := by
  induction d with
  | zero =>
    exact isN2_equiv A _ (MvPowerSeries.isEmptyEquiv (Fin 0) A).toRingEquiv.symm hA
  | succ d ih =>
    have h := PowerSeries.noetherian_domain_isN2 (MvPowerSeries (Fin d) A) ih
    have : IsNoetherianRing (PowerSeries (MvPowerSeries (Fin d) A)) := h.1
    exact isN2_equiv _ _ (MvPowerSeries.finSuccEquiv A d).toRingEquiv.symm h.2.2

-- Step 5: the quotient by p is a field, and Tate applies to the complete DVR.
private theorem isN2_cohen (A : Type u) [CommRing A] [IsDomain A] (p : ℕ)
    (hA : IsCohenRing p A) : IsN2 A (FractionRing A) := by
  obtain ⟨_, _, hdvr, hmax, hcomplete⟩ := hA
  have : IsDiscreteValuationRing A := hdvr
  have : IsAdicComplete (Ideal.span {(p : A)}) A := hcomplete
  have : (Ideal.span {(p : A)}).IsMaximal := by
    rw [← hmax]
    infer_instance
  let := Ideal.Quotient.field (Ideal.span {(p : A)})
  exact tate_n2_complete_principal A (FractionRing A) (p : A) inferInstance
    (isN2_field _ _)

-- Step 2: Cohen structure supplies the finite power series subring.
private theorem isN2_complete_local_domain (D : Type u) [CommRing D]
    [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D] : IsN2 D (FractionRing D) := by
  obtain ⟨A, hreg, _, hfinite, _, _, _, hcoeff⟩ :=
    IsLocalRing.complete_local_domain_finite_over_regular D
  have : IsRegularLocalRing A := hreg
  have : Module.Finite A D := hfinite
  have hA : IsN2 A (FractionRing A) := by
    rcases hcoeff with ⟨k, hk, d, ⟨e⟩⟩ | ⟨Λ, hΛ, d, p, hp, ⟨e⟩⟩
    · let := hk
      exact isN2_equiv _ _ e.symm (isN2_mvPowerSeries k (isN2_field k _) d)
    · let := hΛ
      obtain ⟨hpprime, hdomain, hdvr, hmax, hcomp⟩ := hp
      have : IsDomain Λ := hdomain
      have : IsDiscreteValuationRing Λ := hdvr
      exact isN2_equiv _ _ e.symm
        (isN2_mvPowerSeries Λ (isN2_cohen Λ p ⟨hpprime, hdomain, hdvr, hmax, hcomp⟩) d)
  exact isN2_of_finite_domain_extension A D (FractionRing A) (FractionRing D)
    (fun x y h ↦ Subtype.ext h) hA

/-- A Noetherian ring complete at its unique maximal ideal is Nagata.
Source: Stacks Project, Algebra, Tag 032W
(blueprint: lem-weil-pbc-complete-local-nagata).

Proof (the six steps of the blueprint node):
1. For each prime ideal `p`, the quotient `R / p` is a complete Noetherian local domain
   by `lem-weil-pbc-complete-local-quotient`. It suffices to prove such domains are N-2.
2. By `lem-weil-pbc-complete-local-domain-finite-over-regular`, such a domain is finite
   over a subring isomorphic to a multivariate power series ring over a field or Cohen
   ring. Noetherianity and N-2 are invariant under ring isomorphism: monic equations,
   fraction fields, and module generators transport along the isomorphism. By
   `lem-weil-pbc-n2-ascends-finite-domain-extension`, it suffices that this subring is N-2.
3. Induct on the number of variables using `lem-weil-pbc-power-series-n2`. The zero-variable
   ring is the coefficient ring. Regrouping coefficients by the last coordinate identifies
   the next multivariate ring with a one-variable power series ring over the preceding one;
   the coefficient convolution formula respects this regrouping.
4. A field is Noetherian and N-2: in a finite field extension every element satisfies a
   monic equation, obtained from linear dependence of its powers and division by the
   leading coefficient. Its integral closure is the extension itself, finite by a basis.
5. A Cohen ring is a Noetherian normal domain by `lem-weil-pbc-pid-noetherian-normal`.
   Its residue ring modulo the prime `p` is a field, hence N-2 by step 4; it is complete
   for this principal ideal. Apply `lem-weil-pbc-tate-n2-complete-principal` with `x = p`.
6. Steps 4 and 5 supply the coefficient cases, step 3 supplies their power series rings,
   step 2 supplies the complete local domains, and step 1 shows every prime quotient
   of `R` is N-2. Together with Noetherianity this is `IsNagataRing R`. -/
theorem isNagataRing_of_complete_local (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : IsNagataRing R := by
  refine ⟨inferInstance, ?_⟩
  intro p hp
  have hquot := quotient_complete_local R p hp.ne_top
  have : IsNoetherianRing (R ⧸ p) := hquot.1
  have : IsLocalRing (R ⧸ p) := hquot.2.1
  have : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ p)) (R ⧸ p) := hquot.2.2.2
  exact isN2_complete_local_domain (R ⧸ p)
