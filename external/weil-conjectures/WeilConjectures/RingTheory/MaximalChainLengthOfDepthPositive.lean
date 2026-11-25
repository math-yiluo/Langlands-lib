/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelSeries
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.RingTheory.AssociatedPrimeMinimalOfDepth
import WeilConjectures.RingTheory.AssociatedPrimePowerQuotient
import WeilConjectures.RingTheory.DepthQuotientNonzerodivisor
import WeilConjectures.RingTheory.IsRegularOfDimensionDrop
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.KrullDimension.Regular

/-! Positive-dimensional induction step for maximal Cohen--Macaulay prime chains.
Source: Stacks Project, Algebra, Lemma 10.104.3 (Tag 00N9), via 10.103.9
(blueprint: lem-weil-pbc-cm-local-maximal-chain-length-positive). -/

@[expose] public section

universe u

namespace IsLocalRing

private theorem mem_of_comparable {α : Type*} [PartialOrder α]
    (p : LTSeries α) (hmax : IsMaxChain (fun a b : α ↦ a ≤ b) (Set.range p))
    (a : α) (ha : ∀ i, a ≤ p i ∨ p i ≤ a) : a ∈ Set.range p := by
  have hins : IsChain (fun a b : α ↦ a ≤ b) (insert a (Set.range p)) :=
    hmax.1.insert (by rintro b ⟨i, rfl⟩ _; exact ha i)
  rw [hmax.2 hins (Set.subset_insert _ _)]
  exact Set.mem_insert _ _

private theorem isMin_head_of_maxChain {α : Type*} [PartialOrder α]
    (p : LTSeries α) (hmax : IsMaxChain (fun a b : α ↦ a ≤ b) (Set.range p)) :
    IsMin p.head := by
  intro a ha
  obtain ⟨i, hi⟩ := mem_of_comparable p hmax a (fun i ↦ Or.inl (ha.trans (p.head_le i)))
  exact hi ▸ p.head_le i

private theorem last_eq_maximalIdeal {S : Type u} [CommRing S] [IsLocalRing S]
    (p : LTSeries (PrimeSpectrum S))
    (hmax : IsMaxChain (fun a b : PrimeSpectrum S ↦ a ≤ b) (Set.range p)) :
    p.last.asIdeal = maximalIdeal S := by
  let m : PrimeSpectrum S := ⟨maximalIdeal S, inferInstance⟩
  obtain ⟨i, hi⟩ := mem_of_comparable p hmax m
    (fun i ↦ Or.inr (le_maximalIdeal (p i).isPrime.ne_top))
  apply le_antisymm (le_maximalIdeal p.last.isPrime.ne_top)
  change m ≤ p.last
  rw [← hi]
  exact p.monotone (Fin.le_last i)

private theorem length_pos_of_dim_pos {S : Type u} [CommRing S] [IsLocalRing S]
    (d : ℕ) (hdim : ringKrullDim S = ((d + 1 : ℕ) : WithBot ℕ∞))
    (p : LTSeries (PrimeSpectrum S))
    (hmax : IsMaxChain (fun a b : PrimeSpectrum S ↦ a ≤ b) (Set.range p)) :
    0 < p.length := by
  by_contra hn
  have hz : p.length = 0 := by omega
  have hlast := last_eq_maximalIdeal p hmax
  have hmin := isMin_head_of_maxChain p hmax
  have heq : p.head = p.last := by
    change p 0 = p (Fin.last p.length)
    congr 1
    apply Fin.ext
    simp [hz]
  have hs : Subsingleton (PrimeSpectrum S) := by
    refine ⟨fun a b ↦ ?_⟩
    have hall (a : PrimeSpectrum S) : a = p.head := by
      apply le_antisymm
      · change a.asIdeal ≤ p.head.asIdeal
        rw [heq, hlast]
        exact le_maximalIdeal a.isPrime.ne_top
      · apply hmin
        change a.asIdeal ≤ p.head.asIdeal
        rw [heq, hlast]
        exact le_maximalIdeal a.isPrime.ne_top
    exact (hall a).trans (hall b).symm
  have hle : ringKrullDim S ≤ 0 := Order.krullDim_nonpos_of_subsingleton
  rw [hdim] at hle
  have : d + 1 ≤ 0 := by exact_mod_cast hle
  omega

private theorem second_lt {α : Type*} [PartialOrder α] (p : LTSeries α)
    (hp : p.length ≠ 0) : p.head < (p.tail hp).head := by
  change p 0 < p _
  apply p.strictMono
  change (0 : ℕ) < 1
  omega

private theorem exists_tail_of_ne_head {α : Type*} [PartialOrder α]
    (p : LTSeries α) (hp : p.length ≠ 0) (a : α) (ha : a ∈ Set.range p)
    (hne : a ≠ p.head) : a ∈ Set.range (p.tail hp) := by
  obtain ⟨i, rfl⟩ := ha
  have hi : 0 < i.val := by
    by_contra hi
    have : i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    exact hne (by rw [this]; rfl)
  refine ⟨⟨i.val - 1, ?_⟩, ?_⟩
  · change i.val - 1 < p.length - 1 + 1
    have := i.isLt
    omega
  · change p _ = p i
    congr 1
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega

private theorem maxChain_tail_in_subtype {α : Type*} [PartialOrder α]
    (p : LTSeries α) (hp : p.length ≠ 0)
    (hmax : IsMaxChain (fun a b : α ↦ a ≤ b) (Set.range p))
    (U : Set α) (hU : ∀ i, (p.tail hp) i ∈ U)
    (hmin : IsMin (⟨(p.tail hp).head, hU 0⟩ : U)) :
    ∃ q : LTSeries U,
      q.length = p.length - 1 ∧
      IsMaxChain (fun a b : U ↦ a ≤ b) (Set.range q) := by
  let t : LTSeries α := p.tail hp
  let q : LTSeries U := LTSeries.mk t.length (fun i ↦ ⟨t i, hU i⟩)
    (fun i j hij ↦ t.strictMono hij)
  refine ⟨q, rfl, ?_⟩
  have hhead : (⟨t.head, hU 0⟩ : U) = q.head := rfl
  refine ⟨?_, ?_⟩
  · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ _
    rcases le_total i j with h | h
    · exact Or.inl (q.monotone h)
    · exact Or.inr (q.monotone h)
  · intro c hc hqc
    apply Set.Subset.antisymm hqc
    intro a ha
    have hcomp (i) : a ≤ q i ∨ q i ≤ a := by
      by_cases he : a = q i
      · exact Or.inl he.le
      · exact hc ha (hqc ⟨i, rfl⟩) he
    have hqa : q.head ≤ a := by
      rcases hcomp 0 with h | h
      · exact hhead ▸ hmin (hhead.symm ▸ h)
      · exact h
    have hpa : p.head ≤ a.val := (second_lt p hp).le.trans hqa
    have hmem : a.val ∈ Set.range p := by
      apply mem_of_comparable p hmax
      intro i
      by_cases hi : p i = p.head
      · exact Or.inr (hi ▸ hpa)
      · obtain ⟨j, hj⟩ := exists_tail_of_ne_head p hp (p i) ⟨i, rfl⟩ hi
        exact (hcomp j).imp (fun h ↦ hj ▸ h) (fun h ↦ hj ▸ h)
    have hne : a.val ≠ p.head := by
      intro he
      have h := (second_lt p hp).trans_le hqa
      rw [he] at h
      exact lt_irrefl _ h
    obtain ⟨j, hj⟩ := exists_tail_of_ne_head p hp a.val hmem hne
    exact ⟨j, Subtype.ext hj⟩

private theorem second_mem_minimalPrimes_sup {S : Type u} [CommRing S]
    (p : LTSeries (PrimeSpectrum S)) (hp : p.length ≠ 0)
    (hmax : IsMaxChain (fun a b : PrimeSpectrum S ↦ a ≤ b) (Set.range p))
    (x : S) (hx : x ∈ (p.tail hp).head.asIdeal) (hx0 : x ∉ p.head.asIdeal) :
    (p.tail hp).head.asIdeal ∈ (p.head.asIdeal ⊔ Ideal.span {x}).minimalPrimes := by
  let t : LTSeries (PrimeSpectrum S) := p.tail hp
  refine ⟨⟨t.head.isPrime, sup_le (second_lt p hp).le
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))⟩, ?_⟩
  intro r hr hrle
  let a : PrimeSpectrum S := ⟨r, hr.1⟩
  have h0 : p.head ≤ a := le_sup_left.trans hr.2
  have h1 : a ≤ t.head := hrle
  have hmem : a ∈ Set.range p := by
    apply mem_of_comparable p hmax
    intro i
    by_cases hi : p i = p.head
    · exact Or.inr (hi ▸ h0)
    · obtain ⟨j, hj⟩ := exists_tail_of_ne_head p hp (p i) ⟨i, rfl⟩ hi
      exact Or.inl (h1.trans (hj ▸ t.head_le j))
  have hne : a ≠ p.head := by
    intro he
    have hxr : x ∈ a.asIdeal := hr.2
      ((show Ideal.span {x} ≤ p.head.asIdeal ⊔ Ideal.span {x} from le_sup_right)
      (Ideal.subset_span (by simp)))
    exact hx0 (he ▸ hxr)
  obtain ⟨j, hj⟩ := exists_tail_of_ne_head p hp a hmem hne
  have hb : t.head ≤ a := hj ▸ t.head_le j
  exact hb

private theorem associated_map_quotient {S : Type u} [CommRing S] [IsNoetherianRing S]
    (y : S) (r : Ideal S) (hr : Ideal.span {y} ≤ r)
    (hassoc : r ∈ associatedPrimes S (QuotSMulTop y S)) :
    r.map (Ideal.Quotient.mk (Ideal.span {y})) ∈
      associatedPrimes (S ⧸ Ideal.span {y}) (S ⧸ Ideal.span {y}) := by
  open scoped Pointwise in
    let I := Ideal.span {y}
    have heq : y • (⊤ : Ideal S) = I := by
      simp [I, ← Submodule.ideal_span_singleton_smul]
    let e : QuotSMulTop y S ≃ₗ[S] (S ⧸ I) := Submodule.quotEquivOfEq _ _ heq
    have ha := (e.isAssociatedPrime_iff).mp hassoc
    obtain ⟨hprime, z, hz⟩ := isAssociatedPrime_iff.mp ha
    apply isAssociatedPrime_iff.mpr
    refine ⟨r.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa [I] using hr),
      z, ?_⟩
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    change r ⊔ RingHom.ker (Ideal.Quotient.mk I) = _
    rw [I.mk_ker, sup_eq_left.mpr hr, hz]
    ext a
    simp [Submodule.mem_colon_singleton, Ideal.mem_comap, Algebra.smul_def]

/-- The successor step for the maximal-chain theorem, assuming its dimension-`d` case.
Source: Stacks Project, Algebra, Tag 00N9, proof via Tag 0AAE.
(blueprint: lem-weil-pbc-cm-local-maximal-chain-length-positive)

Proof: Maximality makes the first prime minimal, the last prime maximal, and every
adjacent pair saturated. The chain has positive length: otherwise the maximal ideal
is minimal, so every prime equals it and the ring has dimension zero, contradicting
its dimension `d + 1`. The finitely many minimal primes contain none of the second
prime, since the first prime lies strictly below it. Prime avoidance therefore gives
`x` in the second prime outside all minimal primes. The first prime is associated
in the Noetherian ring, and the second prime is minimal over the first plus `(x)`
by saturation and `x` not belonging to the first prime. The associated-prime power
quotient theorem gives a positive power `y` of `x` for which the second prime is
associated to `S/yS`. This power still avoids every minimal prime and belongs to
the maximal ideal. Dimension drop gives `dim(S/yS) = d`; the dimension-drop
regularity theorem makes `y` a nonzerodivisor, and the quotient depth theorem gives
depth at least `d` in this Noetherian local quotient. The associated element has
annihilator over the quotient equal to the image of the second prime, so associated
prime minimality makes that image minimal. Prime correspondence maps the tail of
the original chain to a strict chain in the quotient, of length `p.length - 1`.
It is maximal: its first prime is minimal, its last prime is the maximal ideal,
and saturation is preserved and reflected by prime correspondence. Apply `ih`
to this quotient chain to obtain `p.length - 1 = d`. The positive length of `p`
then gives `p.length = d + 1`. -/
theorem maximal_chain_length_eq_of_depth_pos {S : Type u} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] (d : ℕ)
    (ih : ∀ {T : Type u} [CommRing T] [IsNoetherianRing T] [IsLocalRing T],
      ringKrullDim T = (d : WithBot ℕ∞) →
      (d : ℕ∞) ≤ IsLocalRing.depth (R := T) T →
      ∀ q : LTSeries (PrimeSpectrum T),
        IsMaxChain (fun a b : PrimeSpectrum T ↦ a ≤ b) (Set.range q) → q.length = d)
    (hdim : ringKrullDim S = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hdepth : ((d + 1 : ℕ) : ℕ∞) ≤ IsLocalRing.depth (R := S) S)
    (p : LTSeries (PrimeSpectrum S))
    (hmax : IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p)) :
    p.length = d + 1 := by
  open scoped Pointwise in
    classical
    have hpos := length_pos_of_dim_pos d hdim p hmax
    let t : LTSeries (PrimeSpectrum S) := p.tail hpos.ne'
    have hfirst : p.head.asIdeal ∈ minimalPrimes S :=
      PrimeSpectrum.isMin_iff.mp (isMin_head_of_maxChain p hmax)
    have hnot : ¬ ((t.head.asIdeal : Set S) ⊆ ⋃ r ∈ minimalPrimes S, (r : Set S)) := by
      rw [Ideal.subset_union_prime_finite (minimalPrimes.finite_of_isNoetherianRing S)
        (⊥ : Ideal S) (⊥ : Ideal S) (fun r hr _ _ ↦ hr.isPrime)]
      rintro ⟨r, hr, hle⟩
      have h0 : p.head.asIdeal ≤ t.head.asIdeal := (second_lt p hpos.ne').le
      have hr0 := hr.2 ⟨p.head.isPrime, bot_le⟩ (h0.trans hle)
      have hb : t.head ≤ p.head := hle.trans hr0
      exact (second_lt p hpos.ne').not_ge hb
    obtain ⟨x, hx1, hxavoid⟩ := Set.not_subset.mp hnot
    have hxnot (r : Ideal S) (hr : r ∈ minimalPrimes S) : x ∉ r := by
      intro hx
      exact hxavoid (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, hx⟩⟩)
    have hxm : x ∈ maximalIdeal S := le_maximalIdeal t.head.isPrime.ne_top hx1
    have hAnn : Module.annihilator S S = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
    have hfirstassoc : p.head.asIdeal ∈ associatedPrimes S S := by
      apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      simpa only [hAnn] using hfirst
    have hsecond := second_mem_minimalPrimes_sup p hpos.ne' hmax x hx1
      (hxnot p.head.asIdeal hfirst)
    obtain ⟨k, hk, hkassoc⟩ := Module.exists_mem_associatedPrimes_quotient_pow
      (M := S) x hxm p.head.asIdeal t.head.asIdeal hfirstassoc hsecond
    let y := x ^ k
    have hy1 : y ∈ t.head.asIdeal := Ideal.pow_mem_of_mem _ hx1 k (by omega)
    have hym : y ∈ maximalIdeal S := le_maximalIdeal t.head.isPrime.ne_top hy1
    have hyavoid (r : Ideal S) (hr : r ∈ minimalPrimes S) : y ∉ r :=
      fun hy ↦ hxnot r hr (hr.isPrime.mem_of_pow_mem k hy)
    have hdrop : ringKrullDim (S ⧸ Ideal.span {y}) + 1 = ringKrullDim S := by
      have hd := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
        (M := S) (x := y) (by simpa only [hAnn] using hyavoid) hym
      have heq : y • (⊤ : Ideal S) = Ideal.span {y} := by
        simp [← Submodule.ideal_span_singleton_smul]
      rw [Module.supportDim_quotient_eq_ringKrullDim, Module.supportDim_self_eq_ringKrullDim,
        ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq S heq).toRingEquiv] at hd
      exact hd
    have hreg := RingTheory.Sequence.isRegular_of_dimension_drop (d + 1) hdim hdepth
      [y] (by simpa using hym) (by
        rw [Ideal.ofList_singleton]
        simpa only [List.length_singleton, Nat.cast_one] using (hdrop.trans hdim))
    have hyreg : y ∈ nonZeroDivisors S := by
      have hs := (RingTheory.Sequence.isRegular_cons_iff S y []).mp hreg
      apply mem_nonZeroDivisors_iff_left.mpr
      intro a ha
      exact hs.1.right_eq_zero_of_smul (by simpa only [smul_eq_mul] using ha)
    obtain ⟨hQ, hnQ, hdQ, _, hdepQ, _⟩ :=
      depth_quotient_nonzerodivisor S (d + 1) hdim hdepth y hym hyreg
    have : IsLocalRing (S ⧸ Ideal.span {y}) := hQ
    have : IsNoetherianRing (S ⧸ Ideal.span {y}) := hnQ
    simp only [Nat.add_sub_cancel] at hdQ hdepQ
    have hI : Ideal.span {y} ≤ t.head.asIdeal :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy1)
    have hminQ := Ideal.mem_minimalPrimes_of_depth_ge d hdQ hdepQ
      _ (associated_map_quotient y t.head.asIdeal hI hkassoc)
    let I := Ideal.span {y}
    let U := PrimeSpectrum.zeroLocus (R := S) I
    let e := I.primeSpectrumQuotientOrderIsoZeroLocus
    have hU (i) : t i ∈ U := hI.trans (t.head_le i)
    have hmin : IsMin (⟨t.head, hU 0⟩ : U) := by
      have hmin' : IsMin (e.symm ⟨t.head, hU 0⟩) := PrimeSpectrum.isMin_iff.mpr hminQ
      intro a ha
      exact e.symm.le_iff_le.mp (hmin' (e.symm.monotone ha))
    obtain ⟨q, hqlen, hqmax⟩ := maxChain_tail_in_subtype p hpos.ne' hmax U hU hmin
    let qQ := q.map e.symm e.symm.strictMono
    have hmaxQ : IsMaxChain (fun a b : PrimeSpectrum (S ⧸ I) ↦ a ≤ b)
        (Set.range qQ) := by
      have hh := hqmax.image e.symm
      convert hh using 1
      exact Set.range_comp e.symm q
    have heq := ih hdQ hdepQ qQ hmaxQ
    change q.length = d at heq
    omega

end IsLocalRing
