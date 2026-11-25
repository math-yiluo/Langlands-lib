/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.PolynomialQuotientCompletionFibreIso
import WeilConjectures.RingTheory.GeometricRegularityFieldIso

/-!
# Reduction of polynomial completion fibres to complete local domains

Source: Stacks Project, More on Algebra, proof of Proposition 07PV, paragraph 2;
Algebra 00E3, 00C9, 00MA, 0325 and 07BH.
(blueprint: lem-weil-pbc-polynomial-complete-local-fibre-reduction)
-/

@[expose] public section

universe u

namespace Polynomial

/-- Each fibre of the localized polynomial completion transports to a polynomial
formal fibre above zero over a complete local domain.
Source: Stacks Project, proof of Proposition 07PV, paragraph 2, with the quotient
completion identity in the proof of 07PN.
(blueprint: lem-weil-pbc-polynomial-complete-local-fibre-reduction)

Proof:
1. Contract the given prime s of T = S[X]_Q to r in S[X]. Prime correspondence
   for localization gives r ≤ Q and canonically identifies the residue fields.
   As all denominators of T act invertibly on both factors, tensoring over S[X]
   or T gives the same fibre over this identified residue field (00E3, 00C9, 07BH).
2. Put p = r intersect S and A = S/p. Primality makes A a domain; 0325 makes it
   a Noetherian complete local ring. The coefficient quotient map S[X] → A[X]
   is surjective with kernel pS[X]. Its images q and r' of Q and r are maximal
   and prime respectively; q lies over the maximal ideal of A, r' ≤ q and
   r' intersects A in zero. Take this actual quotient ring as the witness A.
3. Localizing the coefficient quotient identifies A[X]_q with T/pT, preserving
   maximal ideals. Completion of a quotient (00MA) identifies its completion
   with C/pC, where C is the completion of T. At r the quotient-localization
   identity identifies the residue field with that of r' as an S[X]-algebra.
4. Since p annihilates the residue field, tensoring C with it is unchanged by
   replacing C with C/pC and the base S[X] with A[X]. Tensor associativity and
   step 1 give an isomorphism of fibres compatible with the residue-field
   isomorphism. Noetherianity and regularity after every finite purely inseparable
   field extension transport across these isomorphisms. This is precisely the
   implication below; no arbitrary object is used in a definition. -/
theorem exists_completeLocalDomain_fibre_reduction
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (Q : Ideal (Polynomial S)) [Q.IsMaximal]
    (hQ : Q.comap (Polynomial.C : S →+* Polynomial S) = IsLocalRing.maximalIdeal S)
    (s : Ideal (Localization.AtPrime Q)) [s.IsPrime] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A)
      (_ : IsLocalRing A) (_ : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
      (q r : Ideal (Polynomial A)) (_ : q.IsMaximal) (_ : r.IsPrime),
      q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A ∧
      r ≤ q ∧ r.comap (Polynomial.C : A →+* Polynomial A) = ⊥ ∧
      (Algebra.IsGeometricallyRegular r.ResidueField
        (r.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q))) →
        Algebra.IsGeometricallyRegular s.ResidueField
          (s.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
            (Localization.AtPrime Q)))) := by
  let T := Localization.AtPrime Q
  let r₀ : Ideal (Polynomial S) := s.comap (algebraMap (Polynomial S) T)
  have : r₀.IsPrime := inferInstance
  have hr₀Q : r₀ ≤ Q := by
    have h := Ideal.comap_mono
      (f := algebraMap (Polynomial S) T) (IsLocalRing.le_maximalIdeal_of_isPrime s)
    exact h.trans_eq (IsLocalization.AtPrime.under_maximalIdeal T Q)
  let p : Ideal S := r₀.comap (Polynomial.C : S →+* Polynomial S)
  have : p.IsPrime := inferInstance
  let A := S ⧸ p
  have : IsDomain A := inferInstance
  have : IsLocalRing A :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  obtain ⟨hnoeth, _, hmax, hcomplete⟩ := quotient_complete_local S p
    (Ideal.IsPrime.ne_top inferInstance)
  have : IsNoetherianRing A := hnoeth
  have : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hcomplete
  let f : Polynomial S →+* Polynomial A := Polynomial.mapRingHom (Ideal.Quotient.mk p)
  have hf : Function.Surjective f :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ r₀ := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
    exact Ideal.map_comap_le
  let q : Ideal (Polynomial A) := Q.map f
  let r : Ideal (Polynomial A) := r₀.map f
  have : q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hf
    (hker.trans hr₀Q)
  have : r.IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hqQ : q.comap f = Q := by
    rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr (hker.trans hr₀Q)]
  have hrr₀ : r.comap f = r₀ := by
    rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  have hq : q.comap (Polynomial.C : A →+* Polynomial A) =
      IsLocalRing.maximalIdeal A := by
    have hmk : Function.Surjective (Ideal.Quotient.mk p) :=
      Ideal.Quotient.mk_surjective
    have hinj := Ideal.comap_injective_of_surjective (Ideal.Quotient.mk p) hmk
    apply hinj
    rw [hmax, Ideal.comap_map_of_surjective (Ideal.Quotient.mk p) hmk,
      ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    have hpmax : p ≤ IsLocalRing.maximalIdeal S :=
      IsLocalRing.le_maximalIdeal_of_isPrime p
    rw [sup_eq_left.mpr hpmax]
    change (q.comap Polynomial.C).comap (Ideal.Quotient.mk p) = _
    rw [Ideal.comap_comap]
    have hcomm : (Polynomial.C : A →+* Polynomial A).comp (Ideal.Quotient.mk p) =
        f.comp (Polynomial.C : S →+* Polynomial S) := by
      ext x
      simp [f]
    rw [hcomm, ← Ideal.comap_comap, hqQ, hQ]
  have hr : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥ := by
    have hmk : Function.Surjective (Ideal.Quotient.mk p) :=
      Ideal.Quotient.mk_surjective
    have hinj := Ideal.comap_injective_of_surjective (Ideal.Quotient.mk p) hmk
    apply hinj
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [Ideal.comap_comap]
    have hcomm : (Polynomial.C : A →+* Polynomial A).comp (Ideal.Quotient.mk p) =
        f.comp (Polynomial.C : S →+* Polynomial S) := by
      ext x
      simp [f]
    rw [hcomm, ← Ideal.comap_comap, hrr₀]
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, q, r, inferInstance, inferInstance, hq,
    Ideal.map_mono hr₀Q, hr, ?_⟩
  intro hregular
  obtain ⟨σ, e, hcompat⟩ := exists_quotient_completion_fibre_iso S Q s p rfl q r rfl rfl
  exact Algebra.isGeometricallyRegular_of_fieldIso σ e hcompat hregular

end Polynomial
