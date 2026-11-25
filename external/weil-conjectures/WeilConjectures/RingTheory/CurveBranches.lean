/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.RingTheory.HenselianDVRExtension
public import WeilConjectures.RingTheory.NagataRingIntegralClosure
public import WeilConjectures.RingTheory.Excellent
import WeilConjectures.RingTheory.GRingNagata

/-!
# Branches of a one-dimensional local ring

For a reduced one-dimensional Noetherian local ring `R` with minimal primes `p₁, …, pₜ`, put
`Q(R) = ∏ₐ Frac(R/pₐ)` and `B(R) = ∏ₐ B(R)ₐ`, where `B(R)ₐ` is the integral closure of `R/pₐ` in
`Frac(R/pₐ)` (blueprint `def-exc-local-curve-branches`).

If `R` is moreover henselian with algebraically closed residue field and its normalization is
finite (e.g. `R` is excellent or Nagata), then every branch `B(R)ₐ` is a henselian discrete
valuation ring with fraction field `Frac(R/pₐ)` and the same residue field as `R`, and the
punctured spectrum of `R` is the spectrum of `Q(R)`: there is `f` in the maximal ideal, outside
every minimal prime, such that `D(f) = Spec R ∖ {𝔪}` and `R_f = Q(R)` (blueprint
`lem-exc-punctured-curve-branches`; the scheme-level form is
`AlgebraicGeometry.puncturedSpectrum_branches`). If `R` is excellent, so are its branches.

## Main definitions and statements

- `IsLocalRing.branchFractionRing`, `IsLocalRing.branch`, `IsLocalRing.branchAlgebra`: `Q(R)`,
  the branches and `B(R)`.
- `IsLocalRing.isDiscreteValuationRing_branch`, `IsLocalRing.henselianLocalRing_branch`,
  `IsLocalRing.isAlgClosed_residueField_branch`: the branches are henselian DVRs with
  algebraically closed residue field.
- `IsLocalRing.isLocalization_away_branchFractionRing`: the punctured spectrum is `Spec Q(R)`.
- `IsLocalRing.finite_branch`, `IsLocalRing.finite_branch_of_isExcellentRing`: the branches of a
  Nagata, resp. excellent, local ring are finite; `IsLocalRing.isExcellentRing_branch`: the
  branches of an excellent local ring are excellent.
- `IsLocalRing.branches_and_punctured_spectrum`: the algebraic form of the blueprint lemma
  for a reduced one-dimensional strictly henselian excellent local ring (variants:
  `branches_and_punctured_spectrum_of_finite`, `branches_and_punctured_spectrum_of_isNagataRing`).
-/

@[expose] public section

universe u

open IsLocalRing

namespace IsLocalRing

variable (R : Type u) [CommRing R]

/-- The total ring of fractions of the branches of `R`: `Q(R) = ∏ₐ Frac(R/pₐ)`, the product
over the minimal primes `pₐ` of `R`. (blueprint: `def-exc-local-curve-branches`) -/
abbrev branchFractionRing : Type u :=
  ∀ p : minimalPrimes R, FractionRing (R ⧸ p.1)

/-- The branch of `R` at a minimal prime `p`: the integral closure of `R/p` in its fraction
field. (blueprint: `def-exc-local-curve-branches`) -/
abbrev branch (p : minimalPrimes R) : Type u :=
  integralClosure (R ⧸ p.1) (FractionRing (R ⧸ p.1))

/-- Blueprint `def-exc-local-curve-branches`: The normalization algebra of local curve
branches.

For a ring `R` with minimal primes `pₐ`, the branch algebra
`B(R) = ∏ₐ \overline{(R/pₐ)}^{Frac(R/pₐ)}`: the product of the integral closures of the `R/pₐ`
in their fraction fields (`IsLocalRing.branch`). The map `R → B(R)` (`algebraMap`) is the
product of the quotient maps followed by the inclusions in these integral closures, and
`B(R) ⊆ Q(R)` (`IsLocalRing.branchFractionRing`). The blueprint considers a reduced
one-dimensional Noetherian local ring `R`; the definition makes sense in general. -/
abbrev branchAlgebra : Type u :=
  ∀ p : minimalPrimes R, branch R p

instance isPrime_minimalPrimes (p : minimalPrimes R) : (p : Ideal R).IsPrime := p.2.1.1

example (p : minimalPrimes R) : IsDomain (branch R p) := inferInstance
example : Algebra R (branchAlgebra R) := inferInstance
example : Algebra R (branchFractionRing R) := inferInstance
example : Algebra (branchAlgebra R) (branchFractionRing R) := inferInstance

section dimOne

variable {R} [IsLocalRing R]

/-- In a local ring of dimension one, the maximal ideal has height one. -/
lemma height_maximalIdeal_of_ringKrullDim_eq_one (hdim : ringKrullDim R = 1) :
    (maximalIdeal R).height = 1 := by
  have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
  rw [hdim] at this
  exact_mod_cast this

/-- In a local ring of dimension one, every prime other than the maximal ideal is minimal. -/
lemma mem_minimalPrimes_of_ne_maximalIdeal (hdim : ringKrullDim R = 1) (q : Ideal R)
    [q.IsPrime] (hq : q ≠ maximalIdeal R) : q ∈ minimalPrimes R := by
  have hm := height_maximalIdeal_of_ringKrullDim_eq_one hdim
  have : (maximalIdeal R).FiniteHeight := ⟨Or.inr (by rw [hm]; exact ENat.one_ne_top)⟩
  have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime
    (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hq)
  rw [hm, Order.lt_one_iff] at hlt
  exact Ideal.height_eq_zero_iff.1 hlt

/-- In a local ring of dimension one, a minimal prime is not the maximal ideal. -/
lemma ne_maximalIdeal_of_mem_minimalPrimes (hdim : ringKrullDim R = 1) {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p ≠ maximalIdeal R := by
  rintro rfl
  have : (maximalIdeal R).IsPrime := inferInstance
  have h0 := Ideal.height_eq_zero_iff.2 hp
  rw [height_maximalIdeal_of_ringKrullDim_eq_one hdim] at h0
  exact one_ne_zero h0

end dimOne

section branch

variable {R} [HenselianLocalRing R] (p : minimalPrimes R)

omit [HenselianLocalRing R] in
lemma isPrime_of_mem_minimalPrimes' : p.1.IsPrime := p.2.1.1

lemma isLocalRing_quotient_minimalPrimes : IsLocalRing (R ⧸ p.1) :=
  have := isPrime_of_mem_minimalPrimes' p
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p.1) Ideal.Quotient.mk_surjective

/-- In a one-dimensional local ring, the nonzero primes of `R / p` (`p` minimal) are maximal. -/
lemma eq_maximalIdeal_quotient_of_ne_bot (hdim : ringKrullDim R = 1)
    (q : Ideal (R ⧸ p.1)) [q.IsPrime] (hq : q ≠ ⊥) :
    letI := isLocalRing_quotient_minimalPrimes p
    q = maximalIdeal (R ⧸ p.1) := by
  let := isLocalRing_quotient_minimalPrimes p
  have := isPrime_of_mem_minimalPrimes' p
  set Q := q.comap (Ideal.Quotient.mk p.1)
  have hpQ : p.1 ≤ Q := fun x hx ↦ by
    simp [Q, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  have hQm : Q = maximalIdeal R := by
    by_contra hne
    have hQmin := mem_minimalPrimes_of_ne_maximalIdeal hdim Q hne
    have hQp : p.1 = Q := (show Minimal (fun q : Ideal R ↦ q.IsPrime ∧ ⊥ ≤ q) Q from hQmin).eq_of_le
      ⟨inferInstance, bot_le⟩ hpQ
    apply hq
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q]
    change Ideal.map _ Q = ⊥
    rw [← hQp]
    exact Ideal.map_quotient_self p.1
  refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) fun x hx ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hr : r ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun h ↦ hx (h.map _)
  rw [← hQm] at hr
  exact hr

lemma henselianLocalRing_quotient_minimalPrimes : HenselianLocalRing (R ⧸ p.1) :=
  have := isLocalRing_quotient_minimalPrimes p
  HenselianLocalRing.finite_local_henselian R (R ⧸ p.1)

omit [HenselianLocalRing R] in
lemma isDomain_quotient_minimalPrimes : IsDomain (R ⧸ p.1) :=
  have := isPrime_of_mem_minimalPrimes' p
  inferInstance

lemma isLocalRing_branch : IsLocalRing (branch R p) :=
  have := henselianLocalRing_quotient_minimalPrimes p
  have := isDomain_quotient_minimalPrimes p
  IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain (R := R ⧸ p.1)

lemma isLocalHom_algebraMap_branch :
    letI := isLocalRing_quotient_minimalPrimes p
    letI := isLocalRing_branch p
    IsLocalHom (algebraMap (R ⧸ p.1) (branch R p)) := by
  let := isLocalRing_quotient_minimalPrimes p
  let := isLocalRing_branch p
  have := isDomain_quotient_minimalPrimes p
  have : FaithfulSMul (R ⧸ p.1) (branch R p) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply IsFractionRing.injective (R ⧸ p.1) (FractionRing (R ⧸ p.1))
    have := congrArg (algebraMap (branch R p) (FractionRing (R ⧸ p.1))) h
    simpa only [← IsScalarTower.algebraMap_apply] using this
  infer_instance

variable (hdim : ringKrullDim R = 1)
include hdim

lemma maximalIdeal_quotient_ne_bot :
    letI := isLocalRing_quotient_minimalPrimes p
    maximalIdeal (R ⧸ p.1) ≠ ⊥ := by
  let := isLocalRing_quotient_minimalPrimes p
  have := isPrime_of_mem_minimalPrimes' p
  obtain ⟨r, hrm, hrp⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne
    (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) (ne_maximalIdeal_of_mem_minimalPrimes hdim p.2))
  intro h
  apply hrp
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h, mem_maximalIdeal,
    mem_nonunits_iff]
  exact fun hu ↦ (mem_maximalIdeal _).1 hrm (by
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective v
    by_contra hr
    have hrs : r * s ∈ maximalIdeal R := Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 hr)
    have : r * s - 1 ∈ p.1 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
    have hp := le_maximalIdeal (Ideal.IsPrime.ne_top (isPrime_of_mem_minimalPrimes' p)) this
    exact (mem_maximalIdeal (1 : R)).1 (by simpa using (maximalIdeal R).sub_mem hrs hp) isUnit_one)

/-- A branch is not a field. -/
lemma not_isField_branch : ¬ IsField (branch R p) := by
  let := isLocalRing_quotient_minimalPrimes p
  let := isLocalRing_branch p
  have := isLocalHom_algebraMap_branch p
  intro hF
  apply maximalIdeal_quotient_ne_bot p hdim
  rw [eq_bot_iff]
  intro x hx
  have h1 : algebraMap _ (branch R p) x ∈ maximalIdeal (branch R p) :=
    map_nonunit (algebraMap _ _) x hx
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.1 hF, Ideal.mem_bot] at h1
  rw [Ideal.mem_bot]
  have := isDomain_quotient_minimalPrimes p
  exact (FaithfulSMul.algebraMap_injective _ (branch R p)) (by rw [h1, map_zero])

/-- The nonzero primes of a branch are maximal: they lie over the maximal ideal of `R / p`. -/
lemma eq_maximalIdeal_branch_of_ne_bot (Q : Ideal (branch R p)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    letI := isLocalRing_branch p
    Q = maximalIdeal (branch R p) := by
  let := isLocalRing_quotient_minimalPrimes p
  let := isLocalRing_branch p
  have := isDomain_quotient_minimalPrimes p
  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
  have hc : Q.comap (algebraMap (R ⧸ p.1) (branch R p)) ≠ ⊥ :=
    Ideal.under_ne_bot_of_integral_mem hx0 hxQ (Algebra.IsIntegral.isIntegral x)
  have hcm := eq_maximalIdeal_quotient_of_ne_bot p hdim _ hc
  have : (Q.comap (algebraMap (R ⧸ p.1) (branch R p))).IsMaximal := by
    rw [hcm]
    exact maximalIdeal.isMaximal _
  have := Ideal.isMaximal_of_isIntegral_of_isMaximal_under Q this
  exact IsLocalRing.eq_maximalIdeal this

variable (hfin : Module.Finite (R ⧸ p.1) (branch R p))
include hfin

omit hdim in
lemma henselianLocalRing_branch : HenselianLocalRing (branch R p) :=
  have := henselianLocalRing_quotient_minimalPrimes p
  have := isLocalRing_branch p
  HenselianLocalRing.finite_local_henselian (R ⧸ p.1) (branch R p)

omit hdim [HenselianLocalRing R] in
lemma isNoetherianRing_branch [IsNoetherianRing R] : IsNoetherianRing (branch R p) :=
  IsNoetherianRing.of_finite (R ⧸ p.1) (branch R p)

/-- Blueprint `lem-exc-punctured-curve-branches` (branches): every branch of a reduced
one-dimensional Noetherian henselian local ring with finite normalization is a discrete
valuation ring. -/
theorem isDiscreteValuationRing_branch [IsNoetherianRing R] :
    IsDiscreteValuationRing (branch R p) := by
  let := isLocalRing_branch p
  have := isDomain_quotient_minimalPrimes p
  have := isNoetherianRing_branch p hfin
  have hint : IsIntegrallyClosed (branch R p) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (R ⧸ p.1))
  have h := (IsDiscreteValuationRing.TFAE (branch R p) (not_isField_branch p hdim)).out 1 4
  refine h.2 ⟨hint, ⟨maximalIdeal _, ⟨?_, inferInstance⟩, fun Q ⟨hQ, hQp⟩ ↦
    eq_maximalIdeal_branch_of_ne_bot p hdim Q hQ⟩⟩
  intro h0
  exact not_isField_branch p hdim (IsLocalRing.isField_iff_maximalIdeal_eq.2 h0)

omit hdim hfin in
lemma mk_mem_maximalIdeal_quotient_iff (r : R) :
    letI := isLocalRing_quotient_minimalPrimes p
    Ideal.Quotient.mk p.1 r ∈ maximalIdeal (R ⧸ p.1) ↔ r ∈ maximalIdeal R := by
  let := isLocalRing_quotient_minimalPrimes p
  constructor
  · intro hx
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun h ↦ hx (h.map _)
  · intro hr
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hrs : r * s ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hr
    have : r * s - 1 ∈ p.1 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
    have hp := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) this
    exact (mem_maximalIdeal (1 : R)).1 (by simpa using (maximalIdeal R).sub_mem hrs hp)
      isUnit_one

omit hdim hfin in
lemma isAlgClosed_residueField_quotient [IsAlgClosed (ResidueField R)] :
    letI := isLocalRing_quotient_minimalPrimes p
    IsAlgClosed (ResidueField (R ⧸ p.1)) := by
  let := isLocalRing_quotient_minimalPrimes p
  let φ : R →+* ResidueField (R ⧸ p.1) := (residue _).comp (Ideal.Quotient.mk p.1)
  have hφ : Function.Surjective φ :=
    residue_surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = maximalIdeal R := by
    ext r
    simp only [RingHom.mem_ker, φ, RingHom.comp_apply, residue_eq_zero_iff]
    exact mk_mem_maximalIdeal_quotient_iff p r
  let e : ResidueField R ≃+* ResidueField (R ⧸ p.1) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  exact IsAlgClosed.of_ringEquiv _ _ e

omit hfin hdim in
/-- Blueprint `lem-exc-punctured-curve-branches` (residue fields): the residue field of a
branch is the (algebraically closed) residue field of `R`: every element of a branch is
congruent to an element of `R` modulo its maximal ideal. -/
theorem isAlgClosed_residueField_branch [IsAlgClosed (ResidueField R)] :
    letI := isLocalRing_branch p
    IsAlgClosed (ResidueField (branch R p)) ∧
      ∀ b : branch R p, ∃ r : R, b - algebraMap R (branch R p) r ∈ maximalIdeal _ := by
  let := isLocalRing_quotient_minimalPrimes p
  let := isLocalRing_branch p
  have := isLocalHom_algebraMap_branch p
  have := isAlgClosed_residueField_quotient p
  have := Algebra.IsAlgebraic.residueField_of_isIntegral (R := R ⧸ p.1) (S := branch R p)
  have hbij : Function.Bijective
      (algebraMap (ResidueField (R ⧸ p.1)) (ResidueField (branch R p))) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨IsAlgClosed.of_ringEquiv _ _ (RingEquiv.ofBijective _ hbij), fun b ↦ ?_⟩
  obtain ⟨a, ha⟩ := hbij.2 (residue _ b)
  obtain ⟨a, rfl⟩ := residue_surjective a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨r, ?_⟩
  rw [← residue_eq_zero_iff, RingHom.map_sub, ← ha, ResidueField.algebraMap_residue,
    IsScalarTower.algebraMap_apply R (R ⧸ p.1) (branch R p)]
  exact sub_eq_zero.2 rfl

end branch

section punctured

variable {R} [IsNoetherianRing R] [HenselianLocalRing R] (hdim : ringKrullDim R = 1)
include hdim

/-- By prime avoidance, some `f` in the maximal ideal lies outside every minimal prime. -/
lemma exists_mem_maximalIdeal_forall_notMem :
    ∃ f ∈ maximalIdeal R, ∀ p ∈ minimalPrimes R, f ∉ p := by
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  by_contra! h
  have hsub : ((maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ i ∈ (hfin.toFinset : Set (Ideal R)), ((id i : Ideal R) : Set R) := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := h x hx
    exact Set.mem_biUnion (by simpa using hp) hxp
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
    (fun i hi _ _ ↦ (hfin.mem_toFinset.1 hi).1.1)).1 hsub
  have hp' := hfin.mem_toFinset.1 hp
  have : p.IsPrime := hp'.1.1
  exact ne_maximalIdeal_of_mem_minimalPrimes hdim hp'
    (le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top this)) hle)

omit [IsNoetherianRing R] in
/-- In a one-dimensional local ring, an element of the maximal ideal outside the minimal primes
cuts out the punctured spectrum. -/
lemma notMem_iff_ne_maximalIdeal {f : R} (hfm : f ∈ maximalIdeal R)
    (hf : ∀ p ∈ minimalPrimes R, f ∉ p) (q : Ideal R) [q.IsPrime] :
    f ∉ q ↔ q ≠ maximalIdeal R := by
  constructor
  · rintro hfq rfl
    exact hfq hfm
  · intro hq
    exact hf q (mem_minimalPrimes_of_ne_maximalIdeal hdim q hq)

omit [IsNoetherianRing R] in
/-- For `s ∉ p` (`p` minimal), some power of `f` is a multiple of `s` modulo `p`. -/
lemma exists_mul_sub_pow_mem {f : R} (hfm : f ∈ maximalIdeal R) (p : minimalPrimes R) {s : R}
    (hs : s ∉ p.1) : ∃ (t : R) (n : ℕ), s * t - f ^ n ∈ p.1 := by
  let := isLocalRing_quotient_minimalPrimes p
  have hrad : Ideal.Quotient.mk p.1 f ∈ (Ideal.span {Ideal.Quotient.mk p.1 s}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hsJ, hJ⟩
    have hJ0 : J ≠ ⊥ := by
      intro h0
      apply hs
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h0]
      exact hsJ (Ideal.mem_span_singleton_self _)
    rw [eq_maximalIdeal_quotient_of_ne_bot p hdim J hJ0]
    exact (mk_mem_maximalIdeal_quotient_iff p f).2 hfm
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, n, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, mul_comm, hc, sub_self]

omit hdim in
/-- An element outside a minimal prime `p` lying in all the other minimal primes. -/
lemma exists_notMem_forall_mem (p : minimalPrimes R) :
    ∃ e : R, e ∉ p.1 ∧ ∀ p' : minimalPrimes R, p' ≠ p → e ∈ p'.1 := by
  classical
  have : Finite (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  have := Fintype.ofFinite (minimalPrimes R)
  have hsep (p' : minimalPrimes R) (h : p' ≠ p) : ∃ x, x ∈ p'.1 ∧ x ∉ p.1 := by
    by_contra! H
    apply h
    have hle : p'.1 ≤ p.1 := H
    exact Subtype.ext ((show Minimal (fun q : Ideal R ↦ q.IsPrime ∧ ⊥ ≤ q) p.1 from p.2).eq_of_le
      ⟨inferInstance, bot_le⟩ hle)
  choose! x hx using hsep
  refine ⟨∏ p' ∈ Finset.univ.erase p, x p', ?_, fun p' hp' ↦ ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p', hp', hmem⟩
    exact (hx p' (Finset.ne_of_mem_erase hp')).2 hmem
  · exact Ideal.mem_of_dvd _
      (Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hp', Finset.mem_univ _⟩))
      (hx p' hp').1

omit hdim [IsNoetherianRing R] [HenselianLocalRing R] in
lemma algebraMap_branchFractionRing_apply (r : R) (p : minimalPrimes R) :
    algebraMap R (branchFractionRing R) r p =
      algebraMap (R ⧸ p.1) (FractionRing (R ⧸ p.1)) (Ideal.Quotient.mk p.1 r) :=
  IsScalarTower.algebraMap_apply R (R ⧸ p.1) (FractionRing (R ⧸ p.1)) r

/-- The punctured spectrum: `R_f = Q(R)`, for `f` in the maximal ideal outside the minimal
primes of the reduced one-dimensional local ring `R`. -/
theorem isLocalization_away_branchFractionRing [IsReduced R] {f : R}
    (hfm : f ∈ maximalIdeal R) (hf : ∀ p ∈ minimalPrimes R, f ∉ p) :
    IsLocalization.Away f (branchFractionRing R) where
  map_units := by
    rintro ⟨_, n, rfl⟩
    refine Pi.isUnit_iff.2 fun p ↦ ?_
    simp only [map_pow, algebraMap_branchFractionRing_apply]
    refine IsUnit.pow _ (isUnit_iff_ne_zero.2 ?_)
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hf p.1 p.2
  exists_of_eq := by
    intro x y hxy
    refine ⟨1, ?_⟩
    have hmem : x - y ∈ sInf (minimalPrimes R) := by
      refine Submodule.mem_sInf.2 fun p hp ↦ ?_
      have := congr_fun hxy ⟨p, hp⟩
      simp only [algebraMap_branchFractionRing_apply] at this
      rw [← Ideal.Quotient.eq]
      exact IsFractionRing.injective _ _ this
    rw [Ideal.sInf_minimalPrimes] at hmem
    change x - y ∈ nilradical R at hmem
    rw [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at hmem
    rw [hmem]
  surj := by
    classical
    intro z
    have : Finite (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
    have := Fintype.ofFinite (minimalPrimes R)
    -- each component is `a / f ^ k`
    have hcomp (p : minimalPrimes R) : ∃ (a : R) (k : ℕ),
        z p * algebraMap R (FractionRing (R ⧸ p.1)) (f ^ k) =
          algebraMap R (FractionRing (R ⧸ p.1)) a := by
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R ⧸ p.1) (z p)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hbp : b ∉ p.1 := fun h ↦ nonZeroDivisors.ne_zero hb
        (Ideal.Quotient.eq_zero_iff_mem.2 h)
      obtain ⟨t, k, htk⟩ := exists_mul_sub_pow_mem hdim hfm p hbp
      refine ⟨a * t, k, ?_⟩
      have hb0 : algebraMap (R ⧸ p.1) (FractionRing (R ⧸ p.1)) (Ideal.Quotient.mk p.1 b) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have hk : Ideal.Quotient.mk p.1 (f ^ k) = Ideal.Quotient.mk p.1 (b * t) :=
        (Ideal.Quotient.eq.2 (by rw [← neg_mem_iff, neg_sub]; exact htk))
      simp only [IsScalarTower.algebraMap_apply R (R ⧸ p.1) (FractionRing (R ⧸ p.1)),
        Ideal.Quotient.algebraMap_eq]
      rw [hk, ← hab, map_mul, map_mul, map_mul]
      field_simp
      rw [map_mul]
    -- separating elements
    have hsep (p : minimalPrimes R) : ∃ (E : R) (n : ℕ),
        (∀ p' : minimalPrimes R, p' ≠ p → E ∈ p'.1) ∧ E - f ^ n ∈ p.1 := by
      obtain ⟨e, hep, he⟩ := exists_notMem_forall_mem p
      obtain ⟨t, n, hn⟩ := exists_mul_sub_pow_mem hdim hfm p hep
      exact ⟨e * t, n, fun p' hp' ↦ Ideal.mul_mem_right _ _ (he p' hp'), hn⟩
    choose a k hak using hcomp
    choose E n hE hEn using hsep
    let N := ∑ p, (k p + n p)
    have hN (p : minimalPrimes R) : k p + n p ≤ N :=
      Finset.single_le_sum (f := fun p ↦ k p + n p) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ p)
    refine ⟨⟨∑ p, E p * a p * f ^ (N - k p - n p), ⟨f ^ N, N, rfl⟩⟩, funext fun p ↦ ?_⟩
    simp only [Pi.mul_apply]
    rw [algebraMap_branchFractionRing_apply, algebraMap_branchFractionRing_apply]
    have hx : Ideal.Quotient.mk p.1 (∑ p', E p' * a p' * f ^ (N - k p' - n p')) =
        Ideal.Quotient.mk p.1 (a p * f ^ (N - k p)) := by
      rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ p),
        Finset.sum_eq_zero (s := Finset.univ.erase p) ?h0, add_zero]
      · rw [Ideal.Quotient.eq]
        have := hN p
        obtain ⟨d, h1⟩ : ∃ d, N - k p = n p + d := ⟨N - k p - n p, by omega⟩
        have hd : N - k p - n p = d := by omega
        have : E p * a p * f ^ (N - k p - n p) - a p * f ^ (N - k p) =
            (E p - f ^ n p) * (a p * f ^ (N - k p - n p)) := by
          rw [hd, h1, pow_add]; ring
        rw [this]
        exact Ideal.mul_mem_right _ _ (hEn p)
      · intro p' hp'
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
          (hE p' p (Finset.ne_of_mem_erase hp').symm))
    have hak' := hak p
    rw [IsScalarTower.algebraMap_apply R (R ⧸ p.1),
      IsScalarTower.algebraMap_apply R (R ⧸ p.1) (FractionRing _) (a p),
      Ideal.Quotient.algebraMap_eq] at hak'
    obtain ⟨d, hd⟩ : ∃ d, N = k p + d := ⟨N - k p, by have := hN p; omega⟩
    rw [hx, hd, Nat.add_sub_cancel_left, pow_add, map_mul, map_mul, ← mul_assoc, hak',
      map_mul, map_mul]

end punctured
section finite

variable {R} [IsNoetherianRing R] [HenselianLocalRing R] (hdim : ringKrullDim R = 1)
  (hfin : ∀ p : minimalPrimes R, Module.Finite (R ⧸ p.1) (branch R p))
include hdim hfin

/-- The algebraic content of `lem-exc-punctured-curve-branches` for a reduced one-dimensional
Noetherian henselian local ring with algebraically closed residue field whose normalization is
finite (each branch `B(R)ₐ` is a finite `R / pₐ`-module):
* each branch `B(R)ₐ` is a henselian discrete valuation ring with fraction field `Frac(R/pₐ)` and
  with the same (algebraically closed) residue field as `R`;
* there is `f` in the maximal ideal such that `D(f)` is the punctured spectrum
  `Spec R ∖ {𝔪}` and `R_f = Q(R) = ∏ₐ Frac(R/pₐ)` (`IsLocalization.Away`). -/
theorem branches_and_punctured_spectrum_of_finite [IsReduced R]
    [IsAlgClosed (ResidueField R)] :
    (∀ p : minimalPrimes R, Module.Finite (R ⧸ p.1) (branch R p) ∧
      IsDiscreteValuationRing (branch R p) ∧ HenselianLocalRing (branch R p) ∧
      IsFractionRing (branch R p) (FractionRing (R ⧸ p.1)) ∧
      (letI := isLocalRing_branch p;
        IsAlgClosed (ResidueField (branch R p)) ∧
          ∀ b : branch R p, ∃ r : R, b - algebraMap R (branch R p) r ∈ maximalIdeal _)) ∧
    ∃ f ∈ maximalIdeal R, (∀ q : Ideal R, q.IsPrime → (f ∉ q ↔ q ≠ maximalIdeal R)) ∧
      IsLocalization.Away f (branchFractionRing R) := by
  refine ⟨fun p ↦ ⟨hfin p, isDiscreteValuationRing_branch p hdim (hfin p),
    henselianLocalRing_branch p (hfin p), inferInstance, isAlgClosed_residueField_branch p⟩, ?_⟩
  obtain ⟨f, hfm, hf⟩ := exists_mem_maximalIdeal_forall_notMem hdim
  exact ⟨f, hfm, fun q _ ↦ notMem_iff_ne_maximalIdeal hdim hfm hf q,
    isLocalization_away_branchFractionRing hdim hfm hf⟩

end finite

section nagata

variable {R} (hR : IsNagataRing R)
include hR

/-- The normalization of a Nagata ring is finite: each branch `B(R)ₐ` is a finite
`R / pₐ`-module. -/
theorem finite_branch (p : minimalPrimes R) : Module.Finite (R ⧸ p.1) (branch R p) :=
  hR.finite_integralClosure_quotient p.1

variable [HenselianLocalRing R] (hdim : ringKrullDim R = 1)
include hdim

/-- Variant of `lem-exc-punctured-curve-branches` (`IsLocalRing.branches_and_punctured_spectrum`)
for a reduced one-dimensional strictly henselian Nagata local ring: the Nagata property
`IsNagataRing` gives the finiteness of the normalization
(`branches_and_punctured_spectrum_of_finite`). -/
theorem branches_and_punctured_spectrum_of_isNagataRing [IsReduced R]
    [IsAlgClosed (ResidueField R)] :
    (∀ p : minimalPrimes R, Module.Finite (R ⧸ p.1) (branch R p) ∧
      IsDiscreteValuationRing (branch R p) ∧ HenselianLocalRing (branch R p) ∧
      IsFractionRing (branch R p) (FractionRing (R ⧸ p.1)) ∧
      (letI := isLocalRing_branch p;
        IsAlgClosed (ResidueField (branch R p)) ∧
          ∀ b : branch R p, ∃ r : R, b - algebraMap R (branch R p) r ∈ maximalIdeal _)) ∧
    ∃ f ∈ maximalIdeal R, (∀ q : Ideal R, q.IsPrime → (f ∉ q ↔ q ≠ maximalIdeal R)) ∧
      IsLocalization.Away f (branchFractionRing R) :=
  have := hR.isNoetherianRing
  branches_and_punctured_spectrum_of_finite hdim (finite_branch hR)

end nagata

section excellent

variable {R} (hR : IsExcellentRing R) [HenselianLocalRing R]
include hR

/-- The normalization of an excellent local ring is finite: excellent local rings are Nagata
(`IsExcellentRing.isNagataRing`, Stacks, Tag 07QV), so each branch is finite. -/
theorem finite_branch_of_isExcellentRing (p : minimalPrimes R) :
    Module.Finite (R ⧸ p.1) (branch R p) :=
  finite_branch hR.isNagataRing p

/-- The branches of an excellent local ring are finite `R`-algebras. -/
theorem finite_branch_of_isExcellentRing' (p : minimalPrimes R) : Module.Finite R (branch R p) :=
  have := finite_branch_of_isExcellentRing hR p
  Module.Finite.trans (R ⧸ p.1) (branch R p)

/-- The branches of an excellent local ring are excellent: they are finite `R`-algebras
(Stacks, Tag 07QU). -/
theorem isExcellentRing_branch (p : minimalPrimes R) : IsExcellentRing (branch R p) :=
  have := finite_branch_of_isExcellentRing' hR p
  hR.of_finiteType

variable (hdim : ringKrullDim R = 1)
include hdim

/-- Blueprint `lem-exc-punctured-curve-branches`: The punctured strictly local curve has DVR
branches (algebraic form; the scheme-level statement is
`AlgebraicGeometry.puncturedSpectrum_branches`).

Let `R` be a reduced excellent one-dimensional henselian local ring with algebraically closed
residue field (i.e. strictly henselian; the residue characteristic plays no role). Then:
* each branch `B(R)ₐ = \overline{R/pₐ}` (`IsLocalRing.branch`, the factors of the branch algebra
  `B(R)`) is a finite `R / pₐ`-module, is excellent, and is a henselian discrete valuation ring
  with fraction field `Frac(R/pₐ)` and with the same (algebraically closed) residue field as `R`;
* there is `f` in the maximal ideal such that `D(f)` is the punctured spectrum
  `Spec R ∖ {𝔪}` and `R_f = Q(R) = ∏ₐ Frac(R/pₐ)` (`IsLocalization.Away`).

Excellence gives the finiteness of the normalization (`finite_branch_of_isExcellentRing`) and
passes to the finite `R`-algebras `B(R)ₐ` (`isExcellentRing_branch`). -/
theorem branches_and_punctured_spectrum [IsReduced R] [IsAlgClosed (ResidueField R)] :
    (∀ p : minimalPrimes R, Module.Finite (R ⧸ p.1) (branch R p) ∧ IsExcellentRing (branch R p) ∧
      IsDiscreteValuationRing (branch R p) ∧ HenselianLocalRing (branch R p) ∧
      IsFractionRing (branch R p) (FractionRing (R ⧸ p.1)) ∧
      (letI := isLocalRing_branch p;
        IsAlgClosed (ResidueField (branch R p)) ∧
          ∀ b : branch R p, ∃ r : R, b - algebraMap R (branch R p) r ∈ maximalIdeal _)) ∧
    ∃ f ∈ maximalIdeal R, (∀ q : Ideal R, q.IsPrime → (f ∉ q ↔ q ≠ maximalIdeal R)) ∧
      IsLocalization.Away f (branchFractionRing R) := by
  have := hR.isNoetherianRing
  obtain ⟨h, rest⟩ := branches_and_punctured_spectrum_of_finite hdim
    (finite_branch_of_isExcellentRing hR)
  exact ⟨fun p ↦ ⟨(h p).1, isExcellentRing_branch hR p, (h p).2⟩, rest⟩

end excellent

end IsLocalRing
