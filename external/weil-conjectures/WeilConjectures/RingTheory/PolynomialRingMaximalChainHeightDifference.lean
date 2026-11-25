/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import WeilConjectures.RingTheory.MaximalChainLengthOfDepth
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Maximal chains in polynomial rings over fields

Source: Stacks Project, Algebra, Lemma Tag 00OR (label
`lemma-dimension-height-polynomial-ring`)
(blueprint: lem-weil-pbc-polynomial-ring-maximal-chain-height-difference).
-/

@[expose] public section

universe u

namespace MvPolynomial

private theorem saturated_isMaxChain {α : Type u} [PartialOrder α]
    (c : LTSeries α) (hmin : IsMin c.head) (hmax : IsMax c.last)
    (hcov : ∀ i : Fin c.length, c i.castSucc ⋖ c i.succ) :
    IsMaxChain (fun x y : α ↦ x ≤ y) (Set.range c) := by
  classical
  have hchain : IsChain (fun x y : α ↦ x ≤ y) (Set.range c) := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ _
    exact (le_total i j).imp (fun h ↦ c.monotone h) (fun h ↦ c.monotone h)
  refine ⟨hchain, ?_⟩
  intro t ht hsub
  apply Set.Subset.antisymm hsub
  intro x hx
  have hcomp (i : Fin (c.length + 1)) : c i ≤ x ∨ x ≤ c i := by
    by_cases he : c i = x
    · exact Or.inl he.le
    · exact ht (hsub ⟨i, rfl⟩) hx he
  have hxlast : x ≤ c.last := by
    rcases hcomp (Fin.last c.length) with h | h
    · exact hmax h
    · exact h
  have hex : ∃ j : ℕ, ∃ hj : j < c.length + 1, x ≤ c ⟨j, hj⟩ :=
    ⟨c.length, by omega, hxlast⟩
  let j := Nat.find hex
  obtain ⟨hj, hxj⟩ := Nat.find_spec hex
  change j < c.length + 1 at hj
  change x ≤ c ⟨j, hj⟩ at hxj
  have heq : x = c ⟨j, hj⟩ := by
    by_cases hj0 : j = 0
    · have hi0 : (⟨j, hj⟩ : Fin (c.length + 1)) = 0 := Fin.ext hj0
      have hxhead : x ≤ c.head := by rw [hi0] at hxj; exact hxj
      have hh : c.head ≤ x := hmin hxhead
      simpa [hj0, RelSeries.head] using le_antisymm hxhead hh
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      let i : Fin c.length := ⟨j - 1, by omega⟩
      have hnot : ¬ x ≤ c i.castSucc := by
        intro h
        exact Nat.find_min hex (show j - 1 < j by omega) ⟨by omega, h⟩
      have hprev : c i.castSucc < x :=
        lt_of_le_not_ge ((hcomp i.castSucc).resolve_right hnot) hnot
      have hsucc : c i.succ = c ⟨j, hj⟩ := by
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ, i]
        omega
      exact ((hcov i).eq_or_eq hprev.le (hsucc ▸ hxj)).resolve_left
        (ne_of_gt hprev) |>.trans hsucc
  exact ⟨⟨j, hj⟩, heq.symm⟩

private theorem saturated_of_full_height {α : Type u} [PartialOrder α]
    (c : LTSeries α) (hlen : (c.length : ℕ∞) = Order.height c.last) :
    IsMin c.head ∧ ∀ i : Fin c.length, c i.castSucc ⋖ c i.succ := by
  have hind := Order.height_eq_index_of_length_eq_height_last hlen
  refine ⟨Order.height_eq_zero.mp (hind 0), ?_⟩
  intro i
  refine ⟨c.step i, ?_⟩
  intro x hprev hnext
  have h1 := Order.height_add_one_le hprev
  have h2 := Order.height_add_one_le hnext
  rw [hind i.castSucc] at h1
  rw [hind i.succ] at h2
  have h1' : ((i.val + 1 : ℕ) : ℕ∞) ≤ Order.height x := by simpa using h1
  have h2' : Order.height x + 1 ≤ ((i.val + 1 : ℕ) : ℕ∞) := by simpa using h2
  have h3 : ((i.val + 2 : ℕ) : ℕ∞) ≤ ((i.val + 1 : ℕ) : ℕ∞) := calc
    _ = ((i.val + 1 : ℕ) : ℕ∞) + 1 := by push_cast; rfl
    _ ≤ Order.height x + 1 := add_le_add h1' le_rfl
    _ ≤ _ := h2'
  have h4 : i.val + 2 ≤ i.val + 1 := by exact_mod_cast h3
  omega

private theorem smash_saturated {α : Type u} [PartialOrder α]
    (a b : LTSeries α) (h : a.last = b.head)
    (ha : ∀ i : Fin a.length, a i.castSucc ⋖ a i.succ)
    (hb : ∀ i : Fin b.length, b i.castSucc ⋖ b i.succ) :
    ∀ i : Fin (a.smash b h).length,
      (a.smash b h) i.castSucc ⋖ (a.smash b h) i.succ := by
  intro i
  change Fin (a.length + b.length) at i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [RelSeries.smash_castAdd, RelSeries.smash_succ_castAdd] using ha j
  · intro j
    simpa only [RelSeries.smash_natAdd, RelSeries.smash_succ_natAdd] using hb j

private theorem regular_depth (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (d : ℕ) (hd : ringKrullDim S = (d : WithBot ℕ∞)) :
    (d : ℕ∞) ≤ IsLocalRing.depth (R := S) S := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (show (IsLocalRing.maximalIdeal S).FG from
        (IsLocalRing.maximalIdeal S).fg_of_isNoetherianRing)
  have hlen : s.toList.length = d := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)
    rw [hd] at h
    have hsd : (IsLocalRing.maximalIdeal S).spanFinrank = d := by exact_mod_cast h
    simpa [hsd] using hcard
  have hrs : IsLocalRing.IsRegularSystemOfParameters s.toList :=
    ⟨by simpa using hspan, by rw [hlen, hd]⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators S d hd
    s.toList hrs).1
  unfold IsLocalRing.depth Ideal.depth
  split
  · exact le_top
  · apply le_sSup
    exact ⟨s.toList, hreg, fun x hx ↦ hrs.1 ▸ Ideal.subset_span hx, by rw [hlen]⟩

/-- In a polynomial ring over a field, prime heights are at most the number of variables,
and every saturated chain between two primes has the difference of their heights.
The chain `p = c 0 < c 1 < ⋯ < c t = q` is an `LTSeries` in `PrimeSpectrum P` (the chain
form of the landed sibling `finiteTypeDomain_ringKrullDim_localizationAtMaximal`), its
length `t` is `c.length`, and `c i.castSucc ⋖ c i.succ` (`CovBy`) says that no prime lies
strictly between consecutive members.

Source: Stacks Project, Algebra, Lemma Tag 00OR (label
`lemma-dimension-height-polynomial-ring`)
(blueprint: lem-weil-pbc-polynomial-ring-maximal-chain-height-difference).

Proof (the six steps of the node):
1. By `lem-weil-pbc-polynomial-ring-field-regular-ring` (00OQ), the polynomial
   ring is Noetherian and its localization at each prime is regular local,
   with its maximal ideal generated by dimension-many elements.
2. These generators form a regular sequence by
   `lem-weil-pbc-regular-local-generators-regular-sequence` (00NQ), so each
   localization has depth at least its dimension; dimension zero uses the empty sequence.
3. By `lem-weil-pbc-localization-dimension-chains-below-prime`, prime height is
   the finite dimension of that localization. Height is monotone by its chain
   definition. By `lem-weil-pbc-proper-ideal-contained-in-maximal`, put the upper
   prime inside a maximal ideal; its localization has dimension `n` by
   `lem-weil-pbc-polynomial-ring-maximal-localization-dimension` (00OP).
   This proves the height bound.
4. Since the lower height `h` is finite, a chain realizes it. It ends at the
   lower prime, starts at `(0)` by `lem-weil-pbc-polynomial-ring-domain`, and is
   saturated: otherwise appending, prepending, or inserting a prime would
   give a chain of length `h + 1`, contradicting the height definition.
5. Concatenate this chain with the given one. By
   `lem-weil-pbc-primes-of-localization` (00E3), it becomes a saturated chain
   of length `h + t` in the localization at the upper prime, from its least
   prime to its maximal ideal. Thus it is a maximal chain there.
6. By `lem-weil-pbc-cm-local-maximal-chain-length` (00N9), its length is the
   dimension of this Cohen--Macaulay local ring, hence the upper height.
   Subtract the lower height from `h + t = q.height` to conclude.
-/
theorem maximalChain_height_difference
    {k : Type u} [Field k] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    q.height ≤ (n : ℕ∞) ∧
      ∀ (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime], p ≤ q →
        ∀ (c : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) k))),
          c.head.asIdeal = p → c.last.asIdeal = q →
          (∀ i : Fin c.length, c i.castSucc ⋖ c i.succ) →
          (c.length : ℕ∞) = q.height - p.height := by
  have hbound : q.height ≤ (n : ℕ∞) := by
    obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q Ideal.IsPrime.ne_top'
    let : M.IsMaximal := hM
    have hd := ringKrullDim_localizationAtMaximal n M
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M)] at hd
    have hheight : M.height = (n : ℕ∞) := WithBot.coe_injective hd
    exact (Ideal.height_mono hqM).trans_eq hheight
  refine ⟨hbound, ?_⟩
  intro p hp hpq c hhead hlast hcov
  classical
  let P := MvPolynomial (Fin n) k
  let Q : PrimeSpectrum P := ⟨q, inferInstance⟩
  obtain ⟨a, halast, halen⟩ := Ideal.exists_ltSeries_length_eq_height p
  have haheight : (a.length : ℕ∞) = Order.height a.last := by
    rw [halast, ← PrimeSpectrum.height_eq_orderHeight]
    exact halen
  obtain ⟨hamin, hacov⟩ := saturated_of_full_height a haheight
  have hconnect : a.last = c.head := by
    apply PrimeSpectrum.ext
    exact congrArg PrimeSpectrum.asIdeal halast |>.trans hhead.symm
  let b : LTSeries (PrimeSpectrum P) := a.smash c hconnect
  have hblast : b.last = Q := by
    apply PrimeSpectrum.ext
    simpa [b] using hlast
  have hbmin : IsMin b.head := by simpa [b] using hamin
  have hbcov := smash_saturated a c hconnect hacov hcov
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime q) q
  let bi : LTSeries (Set.Iic Q) :=
    ⟨b.length, fun i ↦ ⟨b i, hblast ▸ b.monotone (Fin.le_last i)⟩, b.step⟩
  let bl : LTSeries (PrimeSpectrum (Localization.AtPrime q)) :=
    bi.map e.symm e.symm.strictMono
  have hblmin : IsMin bl.head := by
    intro x hx
    apply e.le_iff_le.mp
    have heh : e bl.head = bi.head := e.apply_symm_apply bi.head
    have hx' : (e x).val ≤ b.head := by
      have hh := e.monotone hx
      rw [heh] at hh
      exact hh
    change e (e.symm bi.head) ≤ e x
    rw [e.apply_symm_apply]
    exact hbmin hx'
  have hblmax : IsMax bl.last := by
    intro x _
    apply e.le_iff_le.mp
    have hel : e bl.last = bi.last := e.apply_symm_apply bi.last
    rw [hel]
    change (e x).val ≤ b.last
    rw [hblast]
    exact (e x).property
  have hblcov : ∀ i : Fin bl.length, bl i.castSucc ⋖ bl i.succ := by
    intro i
    change e.symm (bi i.castSucc) ⋖ e.symm (bi i.succ)
    apply (apply_covBy_apply_iff e.symm).mpr
    refine ⟨hbcov i |>.lt, ?_⟩
    intro x hx hy
    exact (hbcov i).2 hx hy
  have hblchain := saturated_isMaxChain bl hblmin hblmax hblcov
  let d := (IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank
  have hdim : ringKrullDim (Localization.AtPrime q) = (d : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime q)).symm
  have hdepth := regular_depth (Localization.AtPrime q) d hdim
  have hlength := IsLocalRing.maximal_chain_length_eq_of_depth d hdim hdepth bl hblchain
  have hqheight : q.height = (d : ℕ∞) := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)
    rw [hdim] at h
    exact WithBot.coe_injective h.symm
  have hab : (a.length + c.length : ℕ) = d := hlength
  rw [hqheight, ← hab, Nat.cast_add, ← halen]
  norm_cast
  omega

end MvPolynomial
