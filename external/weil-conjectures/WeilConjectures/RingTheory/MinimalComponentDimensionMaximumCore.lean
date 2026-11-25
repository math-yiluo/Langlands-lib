/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing
import all WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingChains
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg

/-!
# The maximum dimension of minimal components below a prime

Source: Stacks Project, Algebra, proof of Tag 00P1. The proof combines the common
maximal-chain length theorem for finite type domains (Tag 00OS) with the dimension
and transcendence degree theorem (Tag 00P0).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

-- Join longest chains below and above x. Their endpoints are extremal and their
-- successive pairs are covers, so the joined chain is maximal.
private theorem pure_dimension_sum {α : Type*} [PartialOrder α]
    (n : ℕ) (hdim : Order.krullDim α = (n : WithBot ℕ∞))
    (hpure : ∀ c : LTSeries α,
      IsMaxChain (fun x y : α ↦ x ≤ y) (Set.range c) → c.length = n)
    (x : α) : (Order.height x + Order.coheight x : ℕ∞) = n := by
  have hn : Order.krullDim α < ⊤ := by
    rw [hdim]
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n)
  have hh : Order.height x < ⊤ :=
    WithBot.coe_lt_coe.mp ((Order.height_le_krullDim x).trans_lt hn)
  have hc : Order.coheight x < ⊤ :=
    WithBot.coe_lt_coe.mp ((Order.coheight_le_krullDim x).trans_lt hn)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hh.ne
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hc.ne
  obtain ⟨c, hclast, hclen⟩ := Order.exists_series_of_height_eq_coe x ha.symm
  obtain ⟨e, hehead, helen⟩ := Order.exists_series_of_coheight_eq_coe x hb.symm
  have cbound (f : LTSeries α) (hf : f.last = x) : f.length ≤ a := by
    have h := Order.length_le_height hf.le
    rw [← ha] at h
    exact_mod_cast h
  have ebound (f : LTSeries α) (hf : f.head = x) : f.length ≤ b := by
    have h := Order.length_le_coheight hf.ge
    rw [← hb] at h
    exact_mod_cast h
  have hmin : IsMin c.head := by
    intro y hy
    by_contra h
    have hl : y < c.head := lt_of_le_not_ge hy h
    have hbound := cbound (c.cons y hl) (by simpa using hclast)
    simp only [RelSeries.cons_length, hclen] at hbound
    omega
  have hmax : IsMax e.last := by
    intro y hy
    by_contra h
    have hl : e.last < y := lt_of_le_not_ge hy h
    have hbound := ebound (e.snoc y hl) (by simpa using hehead)
    simp only [RelSeries.snoc_length, helen] at hbound
    omega
  have ccov (i : Fin c.length) : c i.castSucc ⋖ c i.succ := by
    refine ⟨c.step i, ?_⟩
    intro y hy hz
    have hbound := cbound (c.insertNth i y hy hz) (by
      change @Fin.insertNth (c.length + 1) (fun _ ↦ α) i.succ.castSucc y c.toFun
        (Fin.last (c.length + 1)) = x
      rw [Fin.insertNth_apply_above (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
        omega)]
      simp only [eq_rec_constant]
      have hi : (Fin.last (c.length + 1)).pred (by simp) = Fin.last c.length :=
        Fin.ext (by simp)
      rw [hi]
      exact hclast)
    simp only [RelSeries.insertNth_length, hclen] at hbound
    omega
  have ecov (i : Fin e.length) : e i.castSucc ⋖ e i.succ := by
    refine ⟨e.step i, ?_⟩
    intro y hy hz
    have hbound := ebound (e.insertNth i y hy hz) (by
      change @Fin.insertNth (e.length + 1) (fun _ ↦ α) i.succ.castSucc y e.toFun 0 = x
      rw [Fin.insertNth_apply_below (by simp [Fin.lt_def])]
      exact hehead)
    simp only [RelSeries.insertNth_length, helen] at hbound
    omega
  have hjoin : c.last = e.head := hclast.trans hehead.symm
  let f := c.smash e hjoin
  have hfcov (i : Fin f.length) : f i.castSucc ⋖ f i.succ := by
    change Fin (c.length + e.length) at i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [f, RelSeries.smash_castAdd, RelSeries.smash_succ_castAdd] using ccov j
    · simpa only [f, RelSeries.smash_natAdd, RelSeries.smash_succ_natAdd] using ecov j
  have hfmax : IsMaxChain (fun x y : α ↦ x ≤ y) (Set.range f) :=
    saturated_isMaxChain_of_nonempty f ⟨x⟩ (by simpa [f] using hmin)
      (by simpa [f] using hmax) hfcov
  have hlen := hpure f hfmax
  change c.length + e.length = n at hlen
  rw [hclen, helen] at hlen
  rw [← ha, ← hb, ← Nat.cast_add]
  exact_mod_cast hlen

private theorem quotient_dimension_eq_coheight {S : Type v} [CommRing S]
    (p : Ideal S) [p.IsPrime] :
    ringKrullDim (S ⧸ p) =
      (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum S) : WithBot ℕ∞) := by
  rw [Order.coheight_eq_krullDim_Ici]
  exact Order.krullDim_eq_of_orderIso p.primeSpectrumQuotientOrderIsoZeroLocus

private theorem quotient_dimension_eq_residue_trdeg
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime] (r : ℕ)
    (hr : Algebra.trdeg k p.ResidueField = (r : Cardinal.{v})) :
    ringKrullDim (S ⧸ p) = (r : WithBot ℕ∞) := by
  obtain ⟨n, hn, ht, _⟩ := finiteType_domain_ringKrullDim_eq_trdeg
    (k := k) (S := S ⧸ p)
  have he : Algebra.trdeg k (FractionRing (S ⧸ p)) =
      Algebra.trdeg k p.ResidueField :=
    ((FractionRing.algEquiv (A := S ⧸ p) p.ResidueField).restrictScalars k).trdeg_eq
  have hnr : n = r := by exact_mod_cast ht.symm.trans (he.trans hr)
  simpa [hnr] using hn

private theorem quotient_prime_data {S : Type v} [CommRing S]
    (p q : Ideal S) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) :
    ∃ P : PrimeSpectrum (S ⧸ q),
      P.asIdeal.comap (Ideal.Quotient.mk q) = p ∧
      Order.coheight P = Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum S) := by
  let e := q.primeSpectrumQuotientOrderIsoZeroLocus
  let f : PrimeSpectrum (S ⧸ q) → PrimeSpectrum S := fun z ↦ (e z).val
  have hf : StrictMono f := fun _ _ h ↦ e.strictMono h
  let x : PrimeSpectrum S := ⟨p, inferInstance⟩
  let P := e.symm ⟨x, hqp⟩
  have hP : f P = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hqp⟩)
  refine ⟨P, congrArg PrimeSpectrum.asIdeal hP, ?_⟩
  have hc := Order.coheight_eq_of_strictMono f hf (fun a b hab ↦ ?_) P
  · simpa only [hP] using hc
  · have hqb : q ≤ b.asIdeal := (e a).property.trans hab.le
    refine ⟨e.symm ⟨b, hqb⟩, ?_, ?_⟩
    · apply e.lt_iff_lt.mp
      rw [e.apply_symm_apply]
      exact hab
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hqb⟩)

private theorem domain_dimension_sum
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsDomain A] (P : PrimeSpectrum A) :
    ringKrullDim A = (Order.height P + Order.coheight P : ℕ∞) := by
  obtain ⟨n, hn, hpure⟩ :=
    (finiteTypeDomain_ringKrullDim_localizationAtMaximal (k := k) (S := A)).2
  have he := pure_dimension_sum n hn hpure P
  rw [he, hn]
  rfl

/-- The dimension bound for every minimal component below a prime.
Source: Stacks Project, Algebra, proof of Tag 00P1, lines 28238-28267.
(blueprint: lem-weil-pbc-minimal-component-dimension-maximum-bound).
Proof: put A = S/q and let P be the image of p in A. Ideal correspondence
identifies primes of A with primes of S containing q. The residue field of P
is canonically the residue field of p; it is the fraction field of A/P = S/p.
Thus the finite type domain dimension/transcendence-degree theorem gives
`dim(S/p) = r`. The maximal-chain theorem for that domain supplies a saturated
chain from p to a maximal ideal of S of length r.
Since hd bounds every chain below p by d, choose a longest chain from q to p,
of length s <= d. Such a chain exists: q <= p, and the set of possible natural
lengths is nonempty and bounded by d. It is saturated, and its first member is q.
Append the chosen chain above p, counting p only once. In the domain A, the
resulting chain starts at zero, ends at a maximal ideal, and is saturated, hence
is a maximal chain. The finite type domain maximal-chain theorem says its length
s+r is dim(A). Therefore dim(S/q) = s+r <= d+r.
-/
theorem minimal_component_dimension_maximum_bound
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (d r : ℕ)
    (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞))
    (hr : Algebra.trdeg k p.ResidueField = (r : Cardinal.{v})) :
    ∀ q : Ideal S, q.IsPrime → q ≤ p →
      (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q) →
      ringKrullDim (S ⧸ q) ≤ ((d + r : ℕ) : WithBot ℕ∞) := by
  intro q hq hqp _hminimal
  let : q.IsPrime := hq
  obtain ⟨P, hP, hc⟩ := quotient_prime_data p q hqp
  have hpheight : p.height = (d : ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p] at hd
    exact WithBot.coe_injective hd
  have hpcoheight : Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum S) = (r : ℕ∞) := by
    have he := quotient_dimension_eq_residue_trdeg (k := k) p r hr
    rw [quotient_dimension_eq_coheight] at he
    exact WithBot.coe_injective he
  have hh : Order.height P ≤ (d : ℕ∞) := by
    have he := Order.height_le_height_apply_of_strictMono
      (PrimeSpectrum.comap (Ideal.Quotient.mk q))
      (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective) P
    simpa only [← PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.comap_asIdeal,
      hP, hpheight] using he
  rw [domain_dimension_sum (k := k) P, hc, hpcoheight]
  exact WithBot.coe_mono (by simpa only [Nat.cast_add, add_comm] using add_le_add_right hh r)

/-- Some minimal component below a prime attains the dimension bound.
Source: Stacks Project, Algebra, proof of Tag 00P1, lines 28238-28267.
(blueprint: lem-weil-pbc-minimal-component-dimension-maximum-attained).
Proof: localization prime correspondence identifies the lengths of chains
below p with those in S_p. Since hd is the finite natural number d, the supremum
of these lengths is attained: if no chain had length d, all lengths would be
at most d-1 (and for d=0 the single-prime chain already attains it).
A length-d chain below p ends at p and starts at a minimal prime q of S;
otherwise appending p or prepending a smaller prime would contradict the bound d.
It is saturated for the same reason. Ideal correspondence gives a saturated
chain from zero to the image of p in the finite type domain S/q.
The residue field of p is the fraction field of S/p. The finite type domain
dimension/transcendence-degree theorem and hr give dim(S/p) = r, and the
maximal-chain theorem supplies a saturated chain of length r above p ending
at a maximal ideal. Append this to the length-d chain, counting p only once.
It is a maximal chain in S/q. The domain maximal-chain theorem makes its length
d+r equal to dim(S/q), giving the required q, its primality and minimality.
-/
theorem minimal_component_dimension_maximum_attained
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (d r : ℕ)
    (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞))
    (hr : Algebra.trdeg k p.ResidueField = (r : Cardinal.{v})) :
    ∃ q : Ideal S, q.IsPrime ∧ q ≤ p ∧
      (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q) ∧
      ringKrullDim (S ⧸ q) = ((d + r : ℕ) : WithBot ℕ∞) := by
  have hpheight : p.height = (d : ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p] at hd
    exact WithBot.coe_injective hd
  let x : PrimeSpectrum S := ⟨p, inferInstance⟩
  have hxheight : Order.height x = (d : ℕ∞) := by
    rw [← PrimeSpectrum.height_eq_orderHeight, hpheight]
  obtain ⟨c, hlast, hlen⟩ := Order.exists_series_of_height_eq_coe x hxheight
  let q := c.head.asIdeal
  have hminimal : ∀ t : Ideal S, t.IsPrime → t ≤ q → t = q := by
    intro t ht htq
    let y : PrimeSpectrum S := ⟨t, ht⟩
    have hy : y ≤ c.head := htq
    have he : c.head ≤ y := by
      by_contra h
      have hlt : y < c.head := lt_of_le_not_ge hy h
      have hb := Order.length_le_height (p := c.cons y hlt)
        (show (c.cons y hlt).last ≤ x by simpa using hlast.le)
      rw [hxheight, RelSeries.cons_length, hlen] at hb
      have hb' : d + 1 ≤ d := by exact_mod_cast hb
      omega
    exact le_antisymm htq he
  have hqp : q ≤ p := by
    have h : c.head ≤ c.last := c.head_le (Fin.last c.length)
    rw [hlast] at h
    exact h
  let : q.IsPrime := c.head.isPrime
  obtain ⟨P, hP, hc⟩ := quotient_prime_data p q hqp
  let e := q.primeSpectrumQuotientOrderIsoZeroLocus
  let z : LTSeries (PrimeSpectrum.zeroLocus (q : Set S)) :=
    ⟨c.length, fun i ↦ ⟨c i, c.head_le i⟩, fun i ↦ c.step i⟩
  let a := z.map e.symm e.symm.strictMono
  have halast : a.last = P := by
    apply PrimeSpectrum.comap_injective_of_surjective
      (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    apply PrimeSpectrum.ext
    change (e a.last).val.asIdeal = P.asIdeal.comap (Ideal.Quotient.mk q)
    rw [hP]
    have he : e a.last = z.last := e.apply_symm_apply z.last
    rw [he]
    exact congrArg PrimeSpectrum.asIdeal hlast
  have hlower : (d : ℕ∞) ≤ Order.height P := by
    have h := Order.length_le_height_last (p := a)
    rw [halast] at h
    change (c.length : ℕ∞) ≤ Order.height P at h
    simpa only [hlen] using h
  have hupper : Order.height P ≤ (d : ℕ∞) := by
    have h := Order.height_le_height_apply_of_strictMono
      (PrimeSpectrum.comap (Ideal.Quotient.mk q))
      (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective) P
    simpa only [← PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.comap_asIdeal,
      hP, hpheight] using h
  have hpcoheight : Order.coheight x = (r : ℕ∞) := by
    have he := quotient_dimension_eq_residue_trdeg (k := k) p r hr
    rw [quotient_dimension_eq_coheight] at he
    exact WithBot.coe_injective he
  refine ⟨q, inferInstance, hqp, hminimal, ?_⟩
  rw [domain_dimension_sum (k := k) P, le_antisymm hupper hlower, hc, hpcoheight]
  simp only [Nat.cast_add, WithBot.coe_add, WithBot.coe_natCast]

end AlgebraicGeometry
