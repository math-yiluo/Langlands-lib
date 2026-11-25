/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Regular.Flat

/-!
# Spreading out regular sequences from a localization

Let `R` be a Noetherian ring, `M` a finitely generated `R`-module and `p` a prime of `R`. A
sequence `r₁, …, rₙ` of `R` which is weakly regular on the localization `M_p` is weakly regular
on `M_g` for some `g ∉ p` (`RingTheory.Sequence.exists_isWeaklyRegular_of_isLocalizedModule`):
more precisely, on every localization `T⁻¹M` in which `g` becomes invertible. Similarly two
finitely generated ideals with the same extension to `R_p` have the same extension to every such
localization (`Ideal.exists_map_eq_map_of_map_eq_map`).

The regularity of one element is read off the associated primes: `a/1` is regular on `T⁻¹M` if
and only if `a` lies in no associated prime of `M` disjoint from `T`
(`RingTheory.Sequence.isSMulRegular_algebraMap_iff`). Take `g` in every associated prime of `M`
containing `a` (there are finitely many, none of them inside `p`).
-/

@[expose] public section

open Module

namespace RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

section Element

variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
  (T : Submonoid R) {S : Type*} [CommRing S] [Algebra R S] [IsLocalization T S]
  {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  (f : M →ₗ[R] N) [IsLocalizedModule T f]

include T f in
/-- The image of `a ∈ R` is regular on the localization `T⁻¹M` if and only if `a` lies in no
associated prime of `M` disjoint from `T`. -/
theorem isSMulRegular_algebraMap_iff (a : R) :
    IsSMulRegular N (algebraMap R S a) ↔
      ∀ q ∈ associatedPrimes R M, Disjoint (T : Set R) q → a ∉ q := by
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing T S ‹_›
  have : Module.Finite S N := Module.Finite.of_isLocalizedModule T f
  have key := biUnion_associatedPrimes_eq_compl_regular S N
  have hass :=
    Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    T S f
  constructor
  · intro hreg q hq hd haq
    have hqP : q.IsPrime := hq.isPrime
    have hP : q.map (algebraMap R S) ∈ associatedPrimes S N := by
      rw [← hass]
      change (q.map (algebraMap R S)).under R ∈ associatedPrimes R M
      rw [IsLocalization.under_map_of_isPrime_disjoint T S hqP hd]
      exact hq
    have : algebraMap R S a ∈ ⋃ P ∈ associatedPrimes S N, (P : Set S) :=
      Set.mem_biUnion hP (Ideal.mem_map_of_mem _ haq)
    rw [key] at this
    exact this hreg
  · intro h
    by_contra hreg
    have : algebraMap R S a ∈ ⋃ P ∈ associatedPrimes S N, (P : Set S) := by
      rw [key]
      exact hreg
    obtain ⟨P, hP, haP⟩ := Set.mem_iUnion₂.1 this
    have hPc : P.comap (algebraMap R S) ∈ associatedPrimes R M := by
      rw [← hass] at hP
      exact hP
    have hd : Disjoint (T : Set R) (P.comap (algebraMap R S)) :=
      ((IsLocalization.isPrime_iff_isPrime_disjoint T S P).1 hP.isPrime).2
    exact h _ hPc hd haP

omit [IsNoetherianRing R] in
include T in
/-- If the image of `g` in `T⁻¹R` is a unit, then `g` lies in no prime disjoint from `T`. -/
lemma notMem_of_isUnit_algebraMap {g : R} (hg : IsUnit (algebraMap R S g)) {q : Ideal R}
    (hq : q.IsPrime) (hd : Disjoint (T : Set R) q) : g ∉ q := fun hgq ↦
  (IsLocalization.isPrime_of_isPrime_disjoint T S q hq hd).ne_top
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hgq) hg)

end Element

section Spread

variable (p : Ideal R) [p.IsPrime] {Sp : Type*} [CommRing Sp] [Algebra R Sp]
  [IsLocalization.AtPrime Sp p]

/-- If `a` is regular on the localization `M_p`, then it is regular on every localization of `M`
in which some fixed `g ∉ p` becomes invertible. -/
theorem exists_isSMulRegular_of_isLocalizedModule {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {Np : Type*} [AddCommGroup Np] [Module R Np] [Module Sp Np]
    [IsScalarTower R Sp Np] (fp : M →ₗ[R] Np) [IsLocalizedModule p.primeCompl fp] (a : R)
    (h : IsSMulRegular Np (algebraMap R Sp a)) :
    ∃ g ∉ p, ∀ (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S]
      (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
      (f : M →ₗ[R] N) [IsLocalizedModule T f], IsUnit (algebraMap R S g) →
        IsSMulRegular N (algebraMap R S a) := by
  classical
  have hp' := (isSMulRegular_algebraMap_iff p.primeCompl fp a).1 h
  let B := (associatedPrimes.finite R M).toFinset.filter (fun q ↦ a ∈ q)
  have hB : ∀ q ∈ B, ∃ g ∈ q, g ∉ p := by
    intro q hq
    simp only [B, Finset.mem_filter, Set.Finite.mem_toFinset] at hq
    by_contra hcon
    push Not at hcon
    exact hp' q hq.1 (Set.disjoint_left.2 fun x hx hxq ↦ hx (hcon x hxq)) hq.2
  choose g hgq hgp using hB
  refine ⟨∏ q ∈ B.attach, g q.1 q.2, fun hG ↦ ?_, ?_⟩
  · obtain ⟨q, -, hq⟩ := Ideal.IsPrime.prod_mem_iff.1 hG
    exact hgp _ _ hq
  · intro T S _ _ _ N _ _ _ _ f _ hu
    rw [isSMulRegular_algebraMap_iff T f]
    intro q hq hd haq
    have hqB : q ∈ B := by simp [B, hq, haq]
    have hGq : ∏ q ∈ B.attach, g q.1 q.2 ∈ q :=
      Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ ⟨q, hqB⟩)) (hgq q hqB)
    exact notMem_of_isUnit_algebraMap T hu hq.isPrime hd hGq

omit [IsNoetherianRing R] in
/-- The quotient `M/aM` of a module has a localization at `T` given by `N/aN`, for any
localization `N` of `M` at `T`. -/
lemma exists_isLocalizedModule_quotSMulTop (T : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization T S] {M : Type*} [AddCommGroup M] [Module R M] {N : Type*}
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[R] N)
    [IsLocalizedModule T f] (a : R) :
    ∃ g : QuotSMulTop a M →ₗ[R] QuotSMulTop (algebraMap R S a) N, IsLocalizedModule T g := by
  have hf : IsBaseChange S f := IsLocalizedModule.isBaseChange T S f
  let e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop a M S).symm ≪≫ₗ
    QuotSMulTop.congr ((algebraMap R S) a) hf.equiv
  have hg : IsBaseChange S <|
      e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop a M) 1 :=
    IsBaseChange.of_equiv e (fun _ ↦ by simp)
  exact ⟨_, (isLocalizedModule_iff_isBaseChange T S _).2 hg⟩

/-- **Spreading out a weakly regular sequence.** Let `R` be Noetherian, `M` a finitely generated
`R`-module and `p` a prime of `R`. If `r₁, …, rₙ` is weakly regular on `M_p`, then there is
`g ∉ p` such that `r₁, …, rₙ` is weakly regular on every localization of `M` in which `g` is
invertible, e.g. on `M_g`. -/
theorem exists_isWeaklyRegular_of_isLocalizedModule (rs : List R) :
    ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] {Np : Type*}
      [AddCommGroup Np] [Module R Np] [Module Sp Np] [IsScalarTower R Sp Np]
      (fp : M →ₗ[R] Np) [IsLocalizedModule p.primeCompl fp],
      IsWeaklyRegular Np (rs.map (algebraMap R Sp)) →
      ∃ g ∉ p, ∀ (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S]
        (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
        (f : M →ₗ[R] N) [IsLocalizedModule T f], IsUnit (algebraMap R S g) →
          IsWeaklyRegular N (rs.map (algebraMap R S)) := by
  induction rs with
  | nil =>
    intro M _ _ _ Np _ _ _ _ fp _ _
    exact ⟨1, fun h ↦ ‹p.IsPrime›.ne_top ((Ideal.eq_top_iff_one p).2 h), fun _ _ _ _ _ _ _ _ _ _ _
      _ _ ↦ by simp⟩
  | cons a rs ih =>
    intro M _ _ _ Np _ _ _ _ fp _ h
    rw [List.map_cons, isWeaklyRegular_cons_iff] at h
    obtain ⟨g₁, hg₁p, hg₁⟩ := exists_isSMulRegular_of_isLocalizedModule p fp a h.1
    obtain ⟨gq, hgq⟩ := exists_isLocalizedModule_quotSMulTop p.primeCompl Sp fp a
    obtain ⟨g₂, hg₂p, hg₂⟩ := ih gq h.2
    refine ⟨g₁ * g₂, fun h ↦ (‹p.IsPrime›.mem_or_mem h).elim hg₁p hg₂p, ?_⟩
    intro T S _ _ _ N _ _ _ _ f _ hu
    rw [map_mul] at hu
    rw [List.map_cons, isWeaklyRegular_cons_iff]
    obtain ⟨gq', hgq'⟩ := exists_isLocalizedModule_quotSMulTop T S f a
    exact ⟨hg₁ T S N f (isUnit_of_mul_isUnit_left hu),
      hg₂ T S _ gq' (isUnit_of_mul_isUnit_right hu)⟩

end Spread

section Associated

open Pointwise

variable {A : Type*} [CommRing A]

lemma smul_top_mul_unit {M : Type*} [AddCommGroup M] [Module A M] (x : A) (u : Aˣ) :
    (x * u : A) • (⊤ : Submodule A M) = x • ⊤ := by
  ext m
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(u : A) • n, by rw [smul_smul]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(↑u⁻¹ : A) • n, by rw [smul_smul, mul_assoc, Units.mul_inv, mul_one]⟩

/-- Weak regularity only depends on the members of a sequence up to units. -/
theorem isWeaklyRegular_of_forall₂_associated (rs : List A) :
    ∀ {M : Type*} [AddCommGroup M] [Module A M] {rs' : List A},
      List.Forall₂ Associated rs rs' → IsWeaklyRegular M rs → IsWeaklyRegular M rs' := by
  induction rs with
  | nil =>
    intro M _ _ rs' h _
    obtain rfl := List.forall₂_nil_left_iff.1 h
    exact IsWeaklyRegular.nil A M
  | cons x rs ih =>
    intro M _ _ rs' h hreg
    obtain ⟨y, rs₂, hxy, h₂, rfl⟩ := List.forall₂_cons_left_iff.1 h
    obtain ⟨u, rfl⟩ := hxy
    rw [isWeaklyRegular_cons_iff] at hreg ⊢
    refine ⟨hreg.1.mul (u.isUnit.isSMulRegular M), ?_⟩
    exact ((Submodule.quotEquivOfEq _ _ (smul_top_mul_unit x u)).isWeaklyRegular_congr rs₂).2
      (ih h₂ hreg.2)

/-- Associated generators generate the same ideal. -/
theorem ofList_eq_of_forall₂_associated {rs rs' : List A} (h : List.Forall₂ Associated rs rs') :
    Ideal.ofList rs = Ideal.ofList rs' := by
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
    obtain ⟨u, rfl⟩ := hxy
    rw [Ideal.ofList_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_mul_right_unit u.isUnit]

end Associated

end RingTheory.Sequence

namespace Ideal

variable {R : Type*} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
  {Sp : Type*} [CommRing Sp] [Algebra R Sp] [IsLocalization.AtPrime Sp p]

/-- If the extension of `I` to `R_p` is contained in that of `J`, then the same holds in every
localization in which some fixed `g ∉ p` becomes invertible. -/
theorem exists_map_le_map_of_map_le_map (I J : Ideal R)
    (h : I.map (algebraMap R Sp) ≤ J.map (algebraMap R Sp)) :
    ∃ g ∉ p, ∀ (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S],
      IsUnit (algebraMap R S g) → I.map (algebraMap R S) ≤ J.map (algebraMap R S) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  have hx : ∀ x ∈ s, ∃ t ∉ p, x * t ∈ J := by
    intro x hx
    have hxI : algebraMap R Sp x ∈ J.map (algebraMap R Sp) :=
      h (Ideal.mem_map_of_mem _ (hs ▸ Ideal.subset_span hx))
    obtain ⟨⟨a, c⟩, hac⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl Sp).1 hxI
    simp only at hac
    rw [← map_mul, IsLocalization.eq_iff_exists p.primeCompl Sp] at hac
    obtain ⟨d, hd⟩ := hac
    refine ⟨d * c, fun hdc ↦ (‹p.IsPrime›.mem_or_mem hdc).elim d.2 c.2, ?_⟩
    have : x * (d * c) = d * a := by rw [← hd]; ring
    rw [this]
    exact J.mul_mem_left _ a.2
  choose t htp htJ using hx
  refine ⟨∏ x ∈ s.attach, t x.1 x.2, fun hG ↦ ?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := Ideal.IsPrime.prod_mem_iff.1 hG
    exact htp _ _ hx
  · intro T S _ _ _ hu
    rw [← hs, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hux : IsUnit (algebraMap R S (t x hx)) := by
      rw [map_prod] at hu
      exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun y : s ↦ algebraMap R S (t y.1 y.2))
        (Finset.mem_attach _ ⟨x, hx⟩)) hu
    have : algebraMap R S x = algebraMap R S (x * t x hx) * ↑hux.unit⁻¹ := by
      rw [map_mul, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [SetLike.mem_coe, this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (htJ x hx))

/-- **Spreading out an equality of ideals.** If two ideals of a Noetherian ring `R` have the same
extension to `R_p`, they have the same extension to every localization in which some fixed
`g ∉ p` becomes invertible. -/
theorem exists_map_eq_map_of_map_eq_map (I J : Ideal R)
    (h : I.map (algebraMap R Sp) = J.map (algebraMap R Sp)) :
    ∃ g ∉ p, ∀ (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S],
      IsUnit (algebraMap R S g) → I.map (algebraMap R S) = J.map (algebraMap R S) := by
  obtain ⟨g₁, hg₁p, hg₁⟩ := exists_map_le_map_of_map_le_map p I J h.le
  obtain ⟨g₂, hg₂p, hg₂⟩ := exists_map_le_map_of_map_le_map p J I h.ge
  refine ⟨g₁ * g₂, fun h ↦ (‹p.IsPrime›.mem_or_mem h).elim hg₁p hg₂p, ?_⟩
  intro T S _ _ _ hu
  rw [map_mul] at hu
  exact le_antisymm (hg₁ T S (isUnit_of_mul_isUnit_left hu))
    (hg₂ T S (isUnit_of_mul_isUnit_right hu))

end Ideal
