/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.SerreConditions
import WeilConjectures.RingTheory.SerreCriterionNormal

/-!
# A regular ring is normal

Source: Stacks Project, Algebra, Lemma Tag 0567
(blueprint: lem-weil-pbc-regular-ring-normal).
-/

@[expose] public section

universe u

namespace IsRegularRing

/-- Every localization of a regular ring at a prime ideal is a normal domain.
Source: Stacks Project, Algebra, Lemma Tag 0567
(blueprint: lem-weil-pbc-regular-ring-normal).

Proof:
1. Regularity (`def-weil-regular-scheme`) makes every prime localization regular local,
   hence in particular those at primes of height at most one. This is Serre's condition
   (R_1) (`def-weil-pbc-serre-conditions-rk-sk`).
2. For each prime localization A of dimension d, choose d generators of its maximal ideal.
   They form a regular sequence by `lem-weil-pbc-regular-local-generators-regular-sequence`
   (Tag 00NQ). They lie in the proper maximal ideal, so the definition of depth
   (`def-weil-pbc-depth`, `def-weil-pbc-regular-sequence`) gives depth A at least d,
   hence at least min(2,d). For d = 0 use the empty sequence. This is (S_2).
3. The ring is Noetherian by regularity (`def-weil-pbc-noetherian-ring`). Apply
   `lem-weil-pbc-serre-criterion-normal` (Tag 031S) to (R_1) and (S_2): each prime
   localization is a domain integrally closed in its fraction field, which is normality
   (`def-weil-pbc-normal-ring`). -/
theorem isNormalRing (R : Type u) [CommRing R] [IsRegularRing R] :
    ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  apply (Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS R).mpr
  constructor
  · intro p hp
    exact inferInstance
  · classical
    intro p hp
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    obtain ⟨s, hcard, hs⟩ := (IsNoetherian.noetherian m).exists_span_finset_card_eq_spanFinrank
    let rs := s.toList
    have hspan : Ideal.span {x | x ∈ rs} = m := by
      simpa [rs] using hs
    have hdim : ringKrullDim A = (rs.length : WithBot ℕ∞) := by
      simpa [rs, hcard, m] using
        (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
    have hparams : IsLocalRing.IsRegularSystemOfParameters rs := ⟨hspan, hdim.symm⟩
    have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators
      A rs.length hdim rs hparams).1
    have hmem : ∀ x ∈ rs, x ∈ m := by
      intro x hx
      rw [← hspan]
      exact Ideal.subset_span hx
    have hdepth : (rs.length : ℕ∞) ≤ IsLocalRing.depth (R := A) A := by
      unfold IsLocalRing.depth Ideal.depth
      split_ifs
      · exact le_top
      · exact le_sSup ⟨rs, hreg, hmem, rfl⟩
    have hheight : p.height = (rs.length : ℕ∞) := by
      have h := (IsLocalization.AtPrime.ringKrullDim_eq_height p A).symm.trans hdim
      exact WithBot.coe_inj.mp h
    exact (min_le_right _ _).trans (hheight ▸ hdepth)

end IsRegularRing
