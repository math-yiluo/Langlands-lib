/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SerreConditions
import Mathlib.RingTheory.LocalProperties.Reduced
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# Serre's criterion for reducedness

Source: Stacks Project, Algebra, Lemma 10.157.3 (Tag 031R)
(blueprint: lem-weil-pbc-serre-criterion-reduced).
-/

@[expose] public section

universe u

namespace Ring

private theorem depth_ge_one_of_regular_element (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (t : A)
    (ht : t ∈ IsLocalRing.maximalIdeal A) (hreg : IsSMulRegular A t) :
    1 ≤ IsLocalRing.depth (R := A) A := by
  unfold IsLocalRing.depth Ideal.depth
  split
  · exact le_top
  · apply le_sSup
    refine ⟨[t], ?_, ?_, by simp⟩
    · apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
      · simpa using ht
      · exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff A t).mpr hreg
    · simpa using ht

private theorem depth_ge_one_of_reduced (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdim : ringKrullDim A ≠ 0) : 1 ≤ IsLocalRing.depth (R := A) A := by
  apply Exists.elim (exists_mem_maximalIdeal_smul_injective A A ?_)
    (fun t ht ↦ depth_ge_one_of_regular_element A t ht.1 ht.2)
  intro hassoc
  obtain ⟨_, z, hz⟩ := (isAssociatedPrime_iff.mp hassoc)
  have hz0 : z ≠ 0 := by
    intro h
    have : IsLocalRing.maximalIdeal A = ⊤ := by
      rw [hz]
      ext x
      simp [h]
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top this
  have hzu : ¬ IsUnit z := by
    intro hu
    have hm : IsLocalRing.maximalIdeal A = ⊥ := by
      rw [hz]
      ext x
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
      exact hu.mul_left_eq_zero
    have hf := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hm
    exact hdim (ringKrullDim_eq_zero_of_isField hf)
  have hzmem : z ∈ IsLocalRing.maximalIdeal A := hzu
  rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hzmem
  exact hz0 (IsNilpotent.eq_zero ⟨2, by simpa [pow_two] using hzmem⟩)

private theorem exists_regular_element_of_depth (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (hd : 1 ≤ IsLocalRing.depth (R := A) A) :
    ∃ t : A, t ∈ IsLocalRing.maximalIdeal A ∧ IsSMulRegular A t := by
  have hm : (IsLocalRing.maximalIdeal A • (⊤ : Submodule A A)) ≠ ⊤ := by
    exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A A))).symm
  unfold IsLocalRing.depth Ideal.depth at hd
  rw [ite_eq_right hm] at hd
  obtain ⟨n, ⟨rs, hreg, hmem, rfl⟩, hn⟩ := lt_sSup_iff.mp (lt_of_lt_of_le
    (show (0 : ℕ∞) < 1 by decide) hd)
  cases rs with
  | nil => simp at hn
  | cons t ts =>
    exact ⟨t, hmem t (by simp), (RingTheory.Sequence.isRegular_cons_iff A t ts).mp hreg |>.1⟩

private theorem reduced_of_localizations (A : Type u) [CommRing A]
    (h : ∀ (p : Ideal A) [p.IsPrime], IsReduced (Localization.AtPrime p)) :
    IsReduced A := by
  constructor
  intro x hx
  apply PrimeSpectrum.toPiLocalization_injective A
  ext p
  have := h p.asIdeal
  simpa using (hx.map ((Pi.evalRingHom _ p).comp
    (PrimeSpectrum.toPiLocalization A).toRingHom)).eq_zero

private theorem reduced_localization_height_zero (R : Type u) [CommRing R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (hp : p.height = 0)
    (hreg : IsRegularLocalRing (Localization.AtPrime p)) :
    IsReduced (Localization.AtPrime p) := by
  have := hreg
  have hdim : ringKrullDim (Localization.AtPrime p) = 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]
    rfl
  have hfin : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).spanFinrank = 0 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime p)
    rw [hdim] at h
    exact_mod_cast h
  have hm := (Submodule.spanFinrank_eq_zero_iff_eq_bot
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal (Localization.AtPrime p)))).mp hfin
  let := ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hm).toField
  infer_instance

/-- A Noetherian ring is reduced exactly when it satisfies `(R₀)` and `(S₁)`.
Source: Stacks Project, Algebra, Lemma 10.157.3 (Tag 031R)
(blueprint: lem-weil-pbc-serre-criterion-reduced).

Proof, following the five steps of the blueprint node:

1. If `R` is reduced, its minimal-prime localizations are fields
   (`lem-weil-pbc-minimal-prime-reduced-localization-field`). Fields are regular local of
   dimension zero (`def-weil-regular-scheme`), giving `(R₀)` as defined in
   `def-weil-pbc-serre-conditions-rk-sk`.
2. For each prime put `A = R_p` (`def-weil-pbc-localization-at-prime`). At dimension zero the
   `(S₁)` inequality is automatic (`def-weil-pbc-depth`). Otherwise `A` is reduced and
   Noetherian (`lem-weil-pbc-localization-preserves-reduced`,
   `lem-weil-pbc-localization-noetherian`). Its maximal ideal cannot annihilate a nonzero
   element: such an element is a nonunit, lies in its annihilator, and has square zero.
   Thus `lem-weil-pbc-nonzerodivisor-if-maximal-not-associated` supplies a nonzerodivisor
   in the maximal ideal. Its one-term sequence is regular (`def-weil-pbc-regular-sequence`)
   and gives depth at least one (`def-weil-pbc-depth`), hence `(S₁)`.
3. Conversely assume both conditions. Prime localizations are Noetherian and have finite
   dimension (`lem-weil-pbc-localization-noetherian`,
   `lem-weil-pbc-noetherian-local-finite-krull-dimension`). Induct simultaneously on their
   heights (`def-weil-pbc-serre-conditions-rk-sk`). At height zero `(R₀)` implies that the
   maximal ideal is generated by zero elements (`def-weil-regular-scheme`), so the
   localization is a field and is reduced.
4. At positive height, `(S₁)` supplies a regular element `t` in the maximal ideal
   (`def-weil-pbc-depth`, `def-weil-pbc-regular-sequence`). The map from `A = R_p` to
   `B = A[1/t]` is injective (`def-weil-ring-localization-away`): an element of its kernel
   is killed by a power of `t`, and multiplication by that power is injective.
   Prime correspondence (`lem-weil-pbc-primes-of-localization`) and iterated localization
   (`lem-weil-pbc-localize-localization-at-prime`) identify every prime localization of
   `B` with `R_q` for a prime `q` strictly below `p`, because it avoids `t`.
   Such a prime has smaller height (`lem-weil-pbc-localization-dimension-chains-below-prime`),
   so these localizations are reduced by induction.
5. Prime localizations jointly detect zero
   (`lem-weil-pbc-prime-localizations-jointly-injective`), so `B` is reduced. The injection
   `A → B` makes `A` reduced. This finishes the induction. Applying joint detection of zero
   once more to `R` makes `R` reduced, completing the equivalence. -/
theorem isReduced_iff_serreR_zero_and_serreS_one (R : Type u) [CommRing R]
    [IsNoetherianRing R] : IsReduced R ↔ IsSerreR R 0 ∧ IsSerreS R 1 := by
  constructor
  · intro hred
    let := hred
    constructor
    · intro p hp hheight
      have hz : p.height = 0 := le_zero_iff.mp hheight
      have : KrullDimLE 0 (Localization.AtPrime p) :=
        KrullDimLE.of_isLocalization p (Ideal.height_eq_zero_iff.mp hz) _
      let := (KrullDimLE.isField_of_isReduced (R := Localization.AtPrime p)).toField
      infer_instance
    · intro p hp
      by_cases hz : p.height = 0
      · simp [hz]
      · have hd : ringKrullDim (Localization.AtPrime p) ≠ 0 := by
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
          simpa using hz
        exact (min_le_left _ _).trans (depth_ge_one_of_reduced _ hd)
  · rintro ⟨hR, hS⟩
    apply reduced_of_localizations
    intro p hp
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := p))
    have hind : ∀ n : ℕ, ∀ (p : Ideal R) [p.IsPrime], p.height = n →
        IsReduced (Localization.AtPrime p) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro p hp hn
        by_cases hz : n = 0
        · subst n
          exact reduced_localization_height_zero R p hn (hR p (by simp [hn]))
        · have hd : 1 ≤ IsLocalRing.depth (R := Localization.AtPrime p)
              (Localization.AtPrime p) := by
            have hmin : min (1 : ℕ∞) p.height = 1 := by
              rw [hn]
              exact min_eq_left (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz)
            simpa only [Nat.cast_one, hmin] using hS p
          obtain ⟨t, ht, hreg⟩ := exists_regular_element_of_depth _ hd
          let A := Localization.AtPrime p
          let B := Localization.Away t
          have hB : IsReduced B := by
            apply reduced_of_localizations
            intro Q hQ
            let Q' : Ideal A := Q.comap (algebraMap A B)
            have : Q'.IsPrime := Ideal.comap_isPrime _ Q
            let q : Ideal R := Q'.comap (algebraMap R A)
            have : q.IsPrime := Ideal.comap_isPrime _ Q'
            have hqle : q ≤ p :=
              ((IsLocalization.AtPrime.orderIsoOfPrime A p) ⟨Q', inferInstance⟩).2.2
            have htQ : t ∉ Q' := by
              intro htQ
              exact hQ.ne_top (Q.eq_top_of_isUnit_mem htQ
                (IsLocalization.Away.algebraMap_isUnit t))
            have hqne : q ≠ p := by
              intro heq
              have hm : Q' = IsLocalRing.maximalIdeal A :=
                (Localization.AtPrime.eq_maximalIdeal_iff_under_eq).mp heq
              exact htQ (hm.symm ▸ ht)
            have hqlt : q < p := lt_of_le_of_ne hqle hqne
            have hheight : q.height < p.height :=
              Ideal.height_strict_mono_of_isPrime hqlt
            obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
              (Ideal.height_ne_top_of_isPrime (I := q))
            have hmn : m < n := by
              rw [hn, ← hm] at hheight
              exact_mod_cast hheight
            have := ih m hmn q hm.symm
            let e₁ := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
              (M := p.primeCompl) Q'
            let e₂ := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
              (M := Submonoid.powers t) Q
            have := isReduced_of_injective e₁.symm.toRingHom e₁.symm.injective
            exact isReduced_of_injective e₂.symm.toRingHom e₂.symm.injective
          have hinj : Function.Injective (algebraMap A B) := by
            intro x y hxy
            obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (x := t) hxy
            exact hreg.pow k hk
          exact isReduced_of_injective (algebraMap A B) hinj
    exact hind n p hn.symm

end Ring
