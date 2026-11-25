/-
Copyright (c) 2026 Christian Merten, Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.Separation.Regular
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.Localization

/-!
# Rings of locally constant functions

Let `R` be a commutative ring and `T` a topological space. In this file we study the
`R`-algebra `LocallyConstant T R` of locally constant functions `T → R`.

## Main declarations

* `LocallyConstant.toPrimeSpectrum`: the map `T × Spec R → Spec (LocallyConstant T R)`
  sending `(t, p)` to the prime of functions whose value at `t` lies in `p`.
* `LocallyConstant.homeomorphPrimeSpectrum`: for `T` profinite, `toPrimeSpectrum` is a
  homeomorphism `T × Spec R ≃ₜ Spec (LocallyConstant T R)`.
* `LocallyConstant.weaklyEtale`: for `T` compact, `LocallyConstant T R` is weakly étale over `R`.
  The multiplication map `S ⊗[R] S → S` is a localization, see
  `LocallyConstant.isLocalization_lmul'`.
* `LocallyConstant.liftPrimeSpectrum`: given a ring map `φ : R →+* B` and a continuous map
  `σ : Spec B → T`, the ring map `LocallyConstant T R →+* B` sending `f` to the element which is
  congruent to `φ (f (σ p))` modulo every prime `p` of `B`. It satisfies
  `Spec (liftPrimeSpectrum φ σ) p = toPrimeSpectrum (σ p, Spec φ p)`.

## References

The results on the prime spectrum (up to `LocallyConstant.homeomorphPrimeSpectrum`) are ported
from the `proetale` project (`Proetale.Algebra.PullbackProfinite`).
-/

@[expose] public section

open PrimeSpectrum TopologicalSpace

namespace LocallyConstant

variable {T : Type*} [TopologicalSpace T] {R : Type*} [CommRing R]

/-!
### Characteristic functions of clopen subsets
-/

section CharFn

variable {U V : Set T}

lemma charFn_apply_of_mem (hU : IsClopen U) {t : T} (ht : t ∈ U) :
    charFn R hU t = 1 :=
  Set.indicator_of_mem ht 1

lemma charFn_apply_of_notMem (hU : IsClopen U) {t : T} (ht : t ∉ U) :
    charFn R hU t = 0 :=
  Set.indicator_of_notMem ht 1

lemma charFn_mul_charFn (hU : IsClopen U) (hV : IsClopen V) :
    charFn R hU * charFn R hV = charFn R (hU.inter hV) := by
  ext t
  by_cases htU : t ∈ U <;> by_cases htV : t ∈ V <;>
    simp [charFn_apply_of_mem, charFn_apply_of_notMem, htU, htV, Set.mem_inter_iff]

lemma charFn_mul_charFn_compl (hU : IsClopen U) :
    charFn R hU * charFn R hU.compl = 0 := by
  ext t
  by_cases htU : t ∈ U <;>
    simp [charFn_apply_of_mem, charFn_apply_of_notMem, htU]

lemma charFn_add_charFn_compl (hU : IsClopen U) :
    charFn R hU + charFn R hU.compl = 1 := by
  ext t
  by_cases htU : t ∈ U <;>
    simp [charFn_apply_of_mem, charFn_apply_of_notMem, htU]

end CharFn

/-!
### The prime spectrum of `LocallyConstant T R`
-/

/-- The prime of `LocallyConstant T R` associated to a point `t : T` and a prime `p` of
`R`: the ideal of functions whose value at `t` lies in `p`. For `T` profinite this
defines a homeomorphism `T × Spec R ≃ₜ Spec (LocallyConstant T R)`, see
`LocallyConstant.homeomorphPrimeSpectrum`. -/
def toPrimeSpectrum (tp : T × PrimeSpectrum R) :
    PrimeSpectrum (LocallyConstant T R) :=
  PrimeSpectrum.comap (evalRingHom tp.1) tp.2

lemma mem_toPrimeSpectrum_asIdeal {tp : T × PrimeSpectrum R} {f : LocallyConstant T R} :
    f ∈ (toPrimeSpectrum tp).asIdeal ↔ f tp.1 ∈ tp.2.asIdeal :=
  Iff.rfl

@[simp]
lemma algebraMap_apply_apply (r : R) (t : T) :
    algebraMap R (LocallyConstant T R) r t = r :=
  rfl

lemma comap_algebraMap_toPrimeSpectrum (tp : T × PrimeSpectrum R) :
    PrimeSpectrum.comap (algebraMap R (LocallyConstant T R)) (toPrimeSpectrum tp) = tp.2 := by
  ext x
  change algebraMap R (LocallyConstant T R) x tp.1 ∈ tp.2.asIdeal ↔ x ∈ tp.2.asIdeal
  simp

lemma toPrimeSpectrum_mem_basicOpen {tp : T × PrimeSpectrum R} {f : LocallyConstant T R} :
    toPrimeSpectrum tp ∈ basicOpen f ↔ f tp.1 ∉ tp.2.asIdeal :=
  Iff.rfl

lemma continuous_toPrimeSpectrum :
    Continuous (toPrimeSpectrum : T × PrimeSpectrum R → _) := by
  refine isTopologicalBasis_basic_opens.continuous_iff.mpr fun s hs ↦ ?_
  obtain ⟨f, rfl⟩ := hs
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨t, p⟩ (htp : toPrimeSpectrum (t, p) ∈ basicOpen f)
  rw [toPrimeSpectrum_mem_basicOpen] at htp
  refine ⟨(⇑f ⁻¹' {f t}) ×ˢ (basicOpen (f t) : Set (PrimeSpectrum R)), ?_, ?_, ?_⟩
  · rintro ⟨t', p'⟩ ⟨ht' : f t' = f t, hp'⟩
    change f t' ∉ p'.asIdeal
    rw [ht']
    exact hp'
  · exact ((f.isLocallyConstant.isClopen_fiber _).isOpen).prod (basicOpen (f t)).2
  · exact ⟨rfl, htp⟩

section Profinite

variable [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

omit [T2Space T] [TotallyDisconnectedSpace T] in
lemma toPrimeSpectrum_surjective :
    Function.Surjective (toPrimeSpectrum : T × PrimeSpectrum R → _) := by
  intro P
  -- `T` is nonempty since `LocallyConstant T R` has a prime ideal.
  have hT : Nonempty T := by
    by_contra h
    rw [not_nonempty_iff] at h
    refine P.isPrime.one_notMem ?_
    have : (1 : LocallyConstant T R) = 0 := by ext t; exact h.elim t
    rw [this]
    exact zero_mem _
  -- The collection of clopens whose characteristic function does not lie in `P`.
  set C : Set (Set T) := {U | ∃ hU : IsClopen U, charFn R hU ∉ P.asIdeal} with hC
  -- It is a filter base of closed nonempty sets, hence has nonempty intersection.
  have hUniv : Set.univ ∈ C :=
    ⟨isClopen_univ, by
      have h1 : charFn R isClopen_univ = (1 : LocallyConstant T R) := by
        ext t; exact charFn_apply_of_mem _ (Set.mem_univ t)
      rw [h1]
      exact P.isPrime.one_notMem⟩
  have hinter : ∀ U ∈ C, ∀ V ∈ C, U ∩ V ∈ C := by
    rintro U ⟨hU, hU'⟩ V ⟨hV, hV'⟩
    refine ⟨hU.inter hV, fun hmem ↦ ?_⟩
    rw [← charFn_mul_charFn hU hV] at hmem
    exact (P.isPrime.mem_or_mem hmem).elim hU' hV'
  have hne : ∀ U ∈ C, U.Nonempty := by
    rintro U ⟨hU, hU'⟩
    rcases Set.eq_empty_or_nonempty U with rfl | h
    · refine absurd ?_ hU'
      have : charFn R hU = (0 : LocallyConstant T R) := by
        ext t; exact charFn_apply_of_notMem _ (Set.notMem_empty t)
      rw [this]
      exact zero_mem _
    · exact h
  have hclosed : ∀ U ∈ C, IsClosed U := by
    rintro U ⟨hU, -⟩
    exact hU.isClosed
  have : Nonempty C := ⟨⟨Set.univ, hUniv⟩⟩
  obtain ⟨t₀, ht₀⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun U : C ↦ (U.1 : Set T))
    (fun U V ↦ ⟨⟨U.1 ∩ V.1, hinter _ U.2 _ V.2⟩, Set.inter_subset_left,
      Set.inter_subset_right⟩)
    (fun U ↦ hne _ U.2)
    (fun U ↦ (hclosed _ U.2).isCompact)
    (fun U ↦ hclosed _ U.2)
  have ht₀' : ∀ U ∈ C, t₀ ∈ U := fun U hU ↦ Set.mem_iInter.mp ht₀ ⟨U, hU⟩
  -- Key: the characteristic function of any clopen containing `t₀` is not in `P`.
  have hkey : ∀ (U : Set T) (hU : IsClopen U), t₀ ∈ U → charFn R hU ∉ P.asIdeal := by
    intro U hU htU hmem
    have hcompl : charFn R hU.compl ∉ P.asIdeal := fun hc ↦ by
      have h1 : (1 : LocallyConstant T R) ∈ P.asIdeal := by
        rw [← charFn_add_charFn_compl (R := R) hU]
        exact add_mem hmem hc
      exact P.isPrime.one_notMem h1
    exact (ht₀' _ ⟨hU.compl, hcompl⟩ : t₀ ∈ Uᶜ) htU
  -- Key: any function vanishing at `t₀` lies in `P`.
  have hvanish : ∀ f : LocallyConstant T R, f t₀ = 0 → f ∈ P.asIdeal := by
    intro f hf
    have hU : IsClopen (⇑f ⁻¹' {0}) := f.isLocallyConstant.isClopen_fiber 0
    have hcompl : charFn R hU.compl ∈ P.asIdeal := by
      have hmul : charFn R hU * charFn R hU.compl ∈ P.asIdeal := by
        rw [charFn_mul_charFn_compl]
        exact zero_mem _
      exact (P.isPrime.mem_or_mem hmul).resolve_left (hkey _ hU hf)
    have heq : f = f * charFn R hU.compl := by
      ext x
      by_cases hx : f x = 0
      · simp [hx]
      · simp [charFn_apply_of_mem hU.compl (by simpa using hx)]
    rw [heq]
    exact P.asIdeal.mul_mem_left _ hcompl
  refine ⟨(t₀, PrimeSpectrum.comap (algebraMap R (LocallyConstant T R)) P), ?_⟩
  ext f
  change f t₀ ∈ (PrimeSpectrum.comap (algebraMap R (LocallyConstant T R)) P).asIdeal ↔
    f ∈ P.asIdeal
  change algebraMap R (LocallyConstant T R) (f t₀) ∈ P.asIdeal ↔ f ∈ P.asIdeal
  have hsub : f - algebraMap R (LocallyConstant T R) (f t₀) ∈ P.asIdeal := by
    refine hvanish _ ?_
    change f t₀ - algebraMap R (LocallyConstant T R) (f t₀) t₀ = 0
    rw [algebraMap_apply_apply, sub_self]
  constructor
  · intro h
    simpa using add_mem hsub h
  · intro h
    simpa using sub_mem h hsub

lemma toPrimeSpectrum_injective :
    Function.Injective (toPrimeSpectrum : T × PrimeSpectrum R → _) := by
  rintro ⟨t, p⟩ ⟨t', p'⟩ h
  have hp : p = p' := by
    have := congrArg (PrimeSpectrum.comap (algebraMap R (LocallyConstant T R))) h
    rwa [comap_algebraMap_toPrimeSpectrum, comap_algebraMap_toPrimeSpectrum] at this
  subst hp
  suffices ht : t = t' by rw [ht]
  by_contra hne
  have : TotallySeparatedSpace T := totallyDisconnectedSpace_iff_totallySeparatedSpace.mp ‹_›
  obtain ⟨U, hU, htU, ht'U⟩ := exists_isClopen_of_totally_separated hne
  have h1 : charFn R hU ∈ (toPrimeSpectrum (t', p)).asIdeal := by
    rw [mem_toPrimeSpectrum_asIdeal, charFn_apply_of_notMem hU ht'U]
    exact zero_mem _
  have h2 : charFn R hU ∉ (toPrimeSpectrum (t, p)).asIdeal := by
    rw [mem_toPrimeSpectrum_asIdeal, charFn_apply_of_mem hU htU]
    exact p.isPrime.one_notMem
  rw [h] at h2
  exact h2 h1

lemma isOpenMap_toPrimeSpectrum :
    IsOpenMap (toPrimeSpectrum : T × PrimeSpectrum R → _) := by
  intro W hW
  rw [isOpen_iff_forall_mem_open]
  rintro Q ⟨⟨t, p⟩, htp, rfl⟩
  obtain ⟨b, hb, htpb, hbW⟩ :=
    (isTopologicalBasis_isClopen.prod isTopologicalBasis_basic_opens).exists_subset_of_mem_open
      htp hW
  obtain ⟨U, hU, s, hs, rfl⟩ := hb
  obtain ⟨r, rfl⟩ := hs
  have hUclopen : IsClopen U := hU
  refine ⟨(basicOpen (charFn R hUclopen * algebraMap R (LocallyConstant T R) r) :
      Set (PrimeSpectrum (LocallyConstant T R))), ?_, (basicOpen _).2, ?_⟩
  · intro Q' hQ'
    obtain ⟨⟨t', p'⟩, rfl⟩ := toPrimeSpectrum_surjective Q'
    rw [SetLike.mem_coe, toPrimeSpectrum_mem_basicOpen] at hQ'
    have hval : (charFn R hUclopen * algebraMap R (LocallyConstant T R) r) t' =
        charFn R hUclopen t' * r := by simp
    rw [hval] at hQ'
    have ht'U : t' ∈ U := by
      by_contra ht'U
      rw [charFn_apply_of_notMem _ ht'U, zero_mul] at hQ'
      exact hQ' (zero_mem _)
    rw [charFn_apply_of_mem _ ht'U, one_mul] at hQ'
    exact ⟨(t', p'), hbW ⟨ht'U, hQ'⟩, rfl⟩
  · rw [SetLike.mem_coe, toPrimeSpectrum_mem_basicOpen]
    obtain ⟨htU, hpr⟩ := htpb
    have hval : (charFn R hUclopen * algebraMap R (LocallyConstant T R) r) t =
        charFn R hUclopen t * r := by simp
    rw [hval, charFn_apply_of_mem _ htU, one_mul]
    exact hpr

/-- For `T` profinite, the prime spectrum of `LocallyConstant T R` is `T × Spec R`.
This computes the Stacks 097D construction in one step: it is the topological
incarnation of `Spec (colim_S (S → R)) = lim_S (S × Spec R) = T × Spec R` over the
discrete quotients `S` of `T`, but is proved directly. -/
noncomputable def homeomorphPrimeSpectrum :
    T × PrimeSpectrum R ≃ₜ PrimeSpectrum (LocallyConstant T R) :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective _ ⟨toPrimeSpectrum_injective, toPrimeSpectrum_surjective⟩)
    continuous_toPrimeSpectrum isOpenMap_toPrimeSpectrum

@[simp]
lemma homeomorphPrimeSpectrum_apply (tp : T × PrimeSpectrum R) :
    homeomorphPrimeSpectrum tp = toPrimeSpectrum tp :=
  rfl

lemma homeomorphPrimeSpectrum_symm_snd (P : PrimeSpectrum (LocallyConstant T R)) :
    ((homeomorphPrimeSpectrum (T := T) (R := R)).symm P).2 =
      PrimeSpectrum.comap (algebraMap R (LocallyConstant T R)) P := by
  conv_rhs => rw [← (homeomorphPrimeSpectrum (T := T) (R := R)).apply_symm_apply P]
  rw [homeomorphPrimeSpectrum_apply, comap_algebraMap_toPrimeSpectrum]

end Profinite

/-!
### Evaluating locally constant functions along a map `Spec B → T`
-/

section LiftPrimeSpectrum

variable {B : Type*} [CommRing B]

/-- The image of an idempotent `e ∉ p` in the localization at the prime `p` is `1`. -/
lemma _root_.IsIdempotentElem.algebraMap_localization_atPrime_of_notMem {e : B}
    (he : IsIdempotentElem e) {p : Ideal B} [p.IsPrime] (hep : e ∉ p) :
    algebraMap B (Localization.AtPrime p) e = 1 :=
  (IsIdempotentElem.iff_eq_one_of_isUnit
    ((IsLocalization.AtPrime.isUnit_to_map_iff _ p e).2 hep)).1 (he.map _)

/-- The image of an idempotent `e ∈ p` in the localization at the prime `p` is `0`. -/
lemma _root_.IsIdempotentElem.algebraMap_localization_atPrime_of_mem {e : B}
    (he : IsIdempotentElem e) {p : Ideal B} [hp : p.IsPrime] (hep : e ∈ p) :
    algebraMap B (Localization.AtPrime p) e = 0 := by
  have h1 : 1 - e ∉ p := fun h ↦ hp.one_notMem (by simpa using add_mem h hep)
  simpa using he.one_sub.algebraMap_localization_atPrime_of_notMem h1

/-- For a clopen subset `U` of `Spec B` there is an element of `B` whose image in the
localization at `p` is `1` if `p ∈ U` and `0` otherwise. -/
lemma _root_.PrimeSpectrum.exists_algebraMap_localization_eq_of_isClopen
    {U : Set (PrimeSpectrum B)} (hU : IsClopen U) :
    ∃ e : B, ∀ p : PrimeSpectrum B,
      (p ∈ U → algebraMap B (Localization.AtPrime p.asIdeal) e = 1) ∧
      (p ∉ U → algebraMap B (Localization.AtPrime p.asIdeal) e = 0) := by
  obtain ⟨⟨e, he⟩, hUe⟩ := isIdempotentElemEquivClopens.surjective ⟨U, hU⟩
  have hU' : U = basicOpen e :=
    (congrArg (fun s : Clopens (PrimeSpectrum B) ↦ (s : Set (PrimeSpectrum B))) hUe).symm
  refine ⟨e, fun p ↦ ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩⟩
  · rw [hU'] at hp
    exact he.algebraMap_localization_atPrime_of_notMem hp
  · rw [hU', SetLike.mem_coe, mem_basicOpen, not_not] at hp
    exact he.algebraMap_localization_atPrime_of_mem hp

/-- Two elements of `B` with the same image in all localizations at primes are equal. -/
lemma _root_.PrimeSpectrum.eq_of_forall_algebraMap_localization_eq {a b : B}
    (h : ∀ p : PrimeSpectrum B, algebraMap B (Localization.AtPrime p.asIdeal) a =
      algebraMap B (Localization.AtPrime p.asIdeal) b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_localization _ fun J hJ ↦ ?_
  rw [map_sub, sub_eq_zero]
  exact h ⟨J, hJ.isPrime⟩

/-- An element of `B` whose image in the localization at `p` vanishes lies in `p`. -/
lemma _root_.PrimeSpectrum.mem_of_algebraMap_localization_eq_zero {a : B}
    (p : PrimeSpectrum B) (h : algebraMap B (Localization.AtPrime p.asIdeal) a = 0) :
    a ∈ p.asIdeal := by
  obtain ⟨⟨m, hm⟩, hma⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl _ a).1 h
  exact (p.isPrime.mem_or_mem (hma ▸ zero_mem _)).resolve_left hm

variable (φ : R →+* B) (σ : C(PrimeSpectrum B, T))

/-- Given `φ : R →+* B` and `σ : Spec B → T`, every `f : LocallyConstant T R` lifts to an element
of `B` whose image in the localization at `p` is that of `φ (f (σ p))`, for all primes `p`. -/
lemma exists_algebraMap_localization_eq (f : LocallyConstant T R) :
    ∃ b : B, ∀ p : PrimeSpectrum B, algebraMap B (Localization.AtPrime p.asIdeal) b =
      algebraMap B (Localization.AtPrime p.asIdeal) (φ (f (σ p))) := by
  let h : LocallyConstant (PrimeSpectrum B) B := (f.comap σ).map φ
  choose e he using fun y : B ↦ PrimeSpectrum.exists_algebraMap_localization_eq_of_isClopen
    (h.isLocallyConstant.isClopen_fiber y)
  refine ⟨∑ y ∈ h.range_finite.toFinset, e y * y, fun p ↦ ?_⟩
  rw [map_sum, Finset.sum_eq_single (h p)]
  · have h1 : algebraMap B (Localization.AtPrime p.asIdeal) (e (h p)) = 1 := (he _ p).1 rfl
    rw [map_mul, h1, one_mul]
    rfl
  · intro y _ hy
    rw [map_mul, (he y p).2 (Ne.symm hy), zero_mul]
  · simp

/-- Given a ring map `φ : R →+* B` and a continuous map `σ : Spec B → T`, this is the ring map
`LocallyConstant T R →+* B` sending `f` to the element of `B` which is `φ (f (σ p))` modulo
every prime `p` of `B`. It is obtained by gluing the constants `φ r` along the idempotents of `B`
corresponding to the clopen partition of `Spec B` given by the fibres of `f ∘ σ`. -/
noncomputable def liftPrimeSpectrum : LocallyConstant T R →+* B where
  toFun f := (exists_algebraMap_localization_eq φ σ f).choose
  map_one' := PrimeSpectrum.eq_of_forall_algebraMap_localization_eq fun p ↦ by
    rw [(exists_algebraMap_localization_eq φ σ 1).choose_spec]
    simp
  map_mul' f g := PrimeSpectrum.eq_of_forall_algebraMap_localization_eq fun p ↦ by
    rw [map_mul, (exists_algebraMap_localization_eq φ σ _).choose_spec,
      (exists_algebraMap_localization_eq φ σ f).choose_spec,
      (exists_algebraMap_localization_eq φ σ g).choose_spec]
    simp
  map_zero' := PrimeSpectrum.eq_of_forall_algebraMap_localization_eq fun p ↦ by
    rw [(exists_algebraMap_localization_eq φ σ 0).choose_spec]
    simp
  map_add' f g := PrimeSpectrum.eq_of_forall_algebraMap_localization_eq fun p ↦ by
    rw [map_add, (exists_algebraMap_localization_eq φ σ _).choose_spec,
      (exists_algebraMap_localization_eq φ σ f).choose_spec,
      (exists_algebraMap_localization_eq φ σ g).choose_spec]
    simp

/-- The image of `liftPrimeSpectrum φ σ f` in the localization at `p` is that of
`φ (f (σ p))`. -/
lemma algebraMap_localization_liftPrimeSpectrum (f : LocallyConstant T R)
    (p : PrimeSpectrum B) :
    algebraMap B (Localization.AtPrime p.asIdeal) (liftPrimeSpectrum φ σ f) =
      algebraMap B (Localization.AtPrime p.asIdeal) (φ (f (σ p))) :=
  (exists_algebraMap_localization_eq φ σ f).choose_spec p

/-- `liftPrimeSpectrum φ σ f` agrees with `φ (f (σ p))` modulo every prime `p`. -/
lemma liftPrimeSpectrum_sub_mem (f : LocallyConstant T R) (p : PrimeSpectrum B) :
    liftPrimeSpectrum φ σ f - φ (f (σ p)) ∈ p.asIdeal :=
  PrimeSpectrum.mem_of_algebraMap_localization_eq_zero p (by
    rw [map_sub, algebraMap_localization_liftPrimeSpectrum, sub_self])

/-- `liftPrimeSpectrum φ σ` is compatible with `φ` on constant functions. -/
@[simp]
lemma liftPrimeSpectrum_algebraMap (r : R) :
    liftPrimeSpectrum φ σ (algebraMap R (LocallyConstant T R) r) = φ r :=
  PrimeSpectrum.eq_of_forall_algebraMap_localization_eq fun p ↦
    algebraMap_localization_liftPrimeSpectrum φ σ _ p

/-- On prime spectra, `liftPrimeSpectrum φ σ` is `p ↦ (σ p, Spec φ p)`. -/
lemma comap_liftPrimeSpectrum (p : PrimeSpectrum B) :
    PrimeSpectrum.comap (liftPrimeSpectrum φ σ) p =
      toPrimeSpectrum (σ p, PrimeSpectrum.comap φ p) := by
  ext f
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, mem_toPrimeSpectrum_asIdeal,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have h := liftPrimeSpectrum_sub_mem φ σ f p
  exact ⟨fun hf ↦ by simpa using sub_mem hf h, fun hf ↦ by simpa using add_mem h hf⟩

end LiftPrimeSpectrum

/-!
### Finite clopen partitions
-/

section Partition

/-- Evaluation of a finite sum of locally constant functions. -/
@[simp]
lemma sum_apply {Y ι : Type*} [AddCommMonoid Y] (s : Finset ι) (f : ι → LocallyConstant T Y)
    (t : T) : (∑ i ∈ s, f i) t = ∑ i ∈ s, f i t :=
  by
  induction s using Finset.cons_induction <;> simp [*]

/-- On a compact space, any finite family `x` of locally constant functions is a linear
combination of the characteristic functions `χ j` of a common finite clopen partition, with
`t j` a point of the `j`-th cell. -/
lemma exists_finite_partition [CompactSpace T] {ι : Type*} [Finite ι]
    (x : ι → LocallyConstant T R) :
    ∃ (k : ℕ) (χ : Fin k → LocallyConstant T R) (t : Fin k → T),
      (∀ i, x i = ∑ j, x i (t j) • χ j) ∧
      (∀ j j', χ j * χ j' = if j = j' then χ j else 0) ∧ ∑ j, χ j = 1 := by
  classical
  let c := unflip x
  let e := c.range_finite.toFinset.equivFin.symm
  have hv (j) : (e j : ι → R) ∈ Set.range c := c.range_finite.mem_toFinset.1 (e j).2
  choose t ht using hv
  let χ (j) := charFn R (c.isLocallyConstant.isClopen_fiber (e j : ι → R))
  have hmem (t' : T) : c t' ∈ c.range_finite.toFinset :=
    c.range_finite.mem_toFinset.2 (Set.mem_range_self t')
  let j₀ (t' : T) := e.symm ⟨c t', hmem t'⟩
  have hj₀ (t' : T) (j) : c t' = e j ↔ j = j₀ t' := by
    rw [Equiv.eq_symm_apply, Subtype.ext_iff, eq_comm]
  have hχ (j) (t' : T) : χ j t' = if j = j₀ t' then 1 else 0 := by
    split_ifs with h
    · exact charFn_apply_of_mem _ ((hj₀ t' j).2 h)
    · exact charFn_apply_of_notMem _ fun h' ↦ h ((hj₀ t' j).1 h')
  refine ⟨_, χ, t, fun i ↦ ?_, fun j j' ↦ ?_, ?_⟩
  · ext t'
    simp only [sum_apply, smul_apply, hχ, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact (congrFun ((ht _).trans ((hj₀ t' _).2 rfl).symm) i).symm
  · ext t'
    by_cases h : j = j'
    · subst h
      simp only [ite_true, coe_mul, Pi.mul_apply, hχ]
      split_ifs <;> simp
    · simp only [h, ite_false, coe_mul, Pi.mul_apply, hχ, coe_zero, Pi.zero_apply]
      split_ifs with h₁ h₂
      · exact absurd (h₁.trans h₂.symm) h
      all_goals simp
  · ext t'
    simp [hχ]

end Partition

/-!
### `LocallyConstant T R` is weakly étale over `R`
-/

section WeaklyEtale

variable [CompactSpace T]

/-- For `T` compact, `LocallyConstant T R` is flat over `R`: every relation is trivialised by
the characteristic functions of a fine enough finite clopen partition. -/
instance flat : Module.Flat R (LocallyConstant T R) := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx ↦ ?_
  obtain ⟨k, χ, t, hx, -, -⟩ := exists_finite_partition x
  refine ⟨k, fun i j ↦ x i (t j), χ, hx, fun j ↦ ?_⟩
  simpa using congrArg (· (t j)) hfx

open TensorProduct in
/-- For `T` compact, every element of the kernel of the multiplication map
`S ⊗[R] S → S` of `S = LocallyConstant T R` is killed by an element mapping to `1`. -/
lemma exists_lmul'_eq_one_and_mul_eq_zero {z : LocallyConstant T R ⊗[R] LocallyConstant T R}
    (hz : Algebra.TensorProduct.lmul' R z = 0) :
    ∃ m, Algebra.TensorProduct.lmul' R m = 1 ∧ m * z = 0 := by
  classical
  obtain ⟨F, rfl⟩ := exists_finset z
  rw [← Finset.sum_coe_sort F] at hz ⊢
  obtain ⟨k, χ, t, hx, hχχ, hχ1⟩ :=
    exists_finite_partition (Sum.elim (fun i : F ↦ i.1.1) (fun i : F ↦ i.1.2))
  have hχx (j) (a) : χ j * Sum.elim (fun i : F ↦ i.1.1) (fun i : F ↦ i.1.2) a =
      Sum.elim (fun i : F ↦ i.1.1) (fun i : F ↦ i.1.2) a (t j) • χ j := by
    conv_lhs => rw [hx a]
    simp [Finset.mul_sum, hχχ]
  have hev (j) : ∑ i : F, i.1.1 (t j) * i.1.2 (t j) = 0 := by
    simpa using congrArg (· (t j)) hz
  refine ⟨∑ j, χ j ⊗ₜ χ j, ?_, ?_⟩
  · simp [hχχ, hχ1]
  · simp_rw [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
    have hχx₁ (j) (i : F) : χ j * i.1.1 = i.1.1 (t j) • χ j := hχx j (Sum.inl i)
    have hχx₂ (j) (i : F) : χ j * i.1.2 = i.1.2 (t j) • χ j := hχx j (Sum.inr i)
    simp_rw [hχx₁, hχx₂, smul_tmul_smul]
    calc _ = ∑ j, (∑ i : F, i.1.1 (t j) * i.1.2 (t j)) • (χ j ⊗ₜ[R] χ j) := by
          simp_rw [Finset.sum_smul]
      _ = 0 := by simp only [hev, zero_smul, Finset.sum_const_zero]

/-- For `T` compact, the multiplication map `S ⊗[R] S → S` of `S = LocallyConstant T R` is the
localization at the submonoid of elements mapping to `1`. -/
lemma isLocalization_lmul' :
    letI := (Algebra.TensorProduct.lmul' R (S := LocallyConstant T R)).toRingHom.toAlgebra
    IsLocalization (Submonoid.comap (Algebra.TensorProduct.lmul' R (S := LocallyConstant T R)) ⊥)
      (LocallyConstant T R) := by
  let := (Algebra.TensorProduct.lmul' R (S := LocallyConstant T R)).toRingHom.toAlgebra
  rw [isLocalization_iff]
  refine ⟨fun y ↦ ?_, fun z ↦ ⟨(z ⊗ₜ 1, 1), ?_⟩, fun {x y} hxy ↦ ?_⟩
  · rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Submonoid.mem_bot.1 y.2]
    exact isUnit_one
  · simp [RingHom.algebraMap_toAlgebra]
  · rw [RingHom.algebraMap_toAlgebra, ← sub_eq_zero, ← map_sub] at hxy
    obtain ⟨m, hm, hmz⟩ := exists_lmul'_eq_one_and_mul_eq_zero hxy
    exact ⟨⟨m, Submonoid.mem_bot.2 hm⟩, by rw [← sub_eq_zero, ← mul_sub, hmz]⟩

/-- For `T` compact (e.g. profinite), `LocallyConstant T R` is weakly étale over `R`. -/
instance weaklyEtale : Algebra.WeaklyEtale R (LocallyConstant T R) where
  flat_lmul' := by
    let := (Algebra.TensorProduct.lmul' R (S := LocallyConstant T R)).toRingHom.toAlgebra
    have := isLocalization_lmul' (T := T) (R := R)
    exact IsLocalization.flat _
      (Submonoid.comap (Algebra.TensorProduct.lmul' R (S := LocallyConstant T R)) ⊥)

end WeaklyEtale

end LocallyConstant
