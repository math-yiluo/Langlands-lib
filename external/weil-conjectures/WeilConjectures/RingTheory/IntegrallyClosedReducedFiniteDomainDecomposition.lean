/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Domain factors from integral closedness in total fractions

Source: Stacks Project, Algebra, Tag 030C, the idempotent argument.
(blueprint: lem-weil-pbc-integrally-closed-reduced-finite-domain-decomposition).
-/

@[expose] public section

universe u

private theorem minimalPrimes_pairwise_coprime
    (R : Type u) [CommRing R] [IsReduced R]
    (hfinite : (minimalPrimes R).Finite)
    (hclosed : IsIntegrallyClosedIn R (FractionRing R))
    (p q : Ideal R) (hp : p ∈ minimalPrimes R) (hq : q ∈ minimalPrimes R)
    (hpq : p ≠ q) : IsCoprime p q := by
  classical
  let S : Finset (Ideal R) := hfinite.toFinset.erase p
  have hS (r : Ideal R) : r ∈ S ↔ r ∈ minimalPrimes R ∧ r ≠ p := by
    simp only [S, Finset.mem_erase, Set.Finite.mem_toFinset, ne_eq]
    tauto
  have hnot (r : Ideal R) (hr : r ∈ S) : ¬p ≤ r := by
    intro hpr
    have heq : p = r := le_antisymm hpr (((hS r).mp hr).1.2 ⟨hp.isPrime, bot_le⟩ hpr)
    exact ((hS r).mp hr).2 heq.symm
  have havoid : ¬(p : Set R) ⊆ ⋃ r ∈ (S : Set (Ideal R)), (r : Set R) := by
    intro h
    obtain ⟨r, hr, hpr⟩ := (Ideal.subset_union_prime p p
      (fun r hr _ _ ↦ ((hS r).mp hr).1.isPrime)).mp h
    exact hnot r hr hpr
  obtain ⟨b, hbp, hb⟩ := Set.not_subset.mp havoid
  have hbnot (r : Ideal R) (hr : r ∈ S) : b ∉ r := by
    intro hbr
    exact hb (Set.mem_iUnion₂.mpr ⟨r, hr, hbr⟩)
  have hpn : ¬(S.inf id) ≤ p := by
    intro h
    obtain ⟨r, hr, hrp⟩ := hp.isPrime.inf_le'.mp h
    have heq : r = p := le_antisymm hrp (hp.2
      ⟨((hS r).mp hr).1.isPrime, bot_le⟩ hrp)
    exact ((hS r).mp hr).2 heq
  obtain ⟨a, ha, hap⟩ := Set.not_subset.mp hpn
  have hamem (r : Ideal R) (hr : r ∈ S) : a ∈ r := (show S.inf id ≤ r from Finset.inf_le hr) ha
  have hab : a * b = 0 := by
    have hz : a * b ∈ sInf (minimalPrimes R) := by
      rw [Ideal.mem_sInf]
      intro r hr
      by_cases hrp : r = p
      · subst r
        exact p.mul_mem_left a hbp
      · exact r.mul_mem_right b (hamem r ((hS r).mpr ⟨hr, hrp⟩))
    simpa only [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced,
      Ideal.mem_bot] using hz
  have hs : a + b ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    by_contra hc0
    have hcunion : a + b ∈ ⋃ r ∈ minimalPrimes R, (r : Set R) := by
      rw [Ideal.iUnion_minimalPrimes, Ideal.radical_bot_of_isReduced]
      exact ⟨c, hc0, by simpa [mul_comm] using hc⟩
    obtain ⟨r, hr, hsr⟩ := Set.mem_iUnion₂.mp hcunion
    by_cases hrp : r = p
    · subst r
      exact hap (p.add_mem_iff_left hbp |>.mp hsr)
    · exact hbnot r ((hS r).mpr ⟨hr, hrp⟩)
        (r.add_mem_iff_right (hamem r ((hS r).mpr ⟨hr, hrp⟩)) |>.mp hsr)
  let s : nonZeroDivisors R := ⟨a + b, hs⟩
  let x : FractionRing R := IsLocalization.mk' (FractionRing R) a s
  have hxs : x * algebraMap R (FractionRing R) (a + b) =
      algebraMap R (FractionRing R) a := IsLocalization.mk'_spec _ a s
  have hidem : x * x = x := by
    apply (IsLocalization.map_units (FractionRing R) s).mul_left_inj.mp
    apply (IsLocalization.map_units (FractionRing R) s).mul_left_inj.mp
    calc
      (x * x * algebraMap R (FractionRing R) (a + b)) *
          algebraMap R (FractionRing R) (a + b) =
          (x * algebraMap R (FractionRing R) (a + b)) ^ 2 := by ring
      _ = algebraMap R (FractionRing R) (a * a) := by rw [hxs, pow_two, map_mul]
      _ = algebraMap R (FractionRing R) (a * (a + b)) := by
        congr 1
        rw [mul_add, hab, add_zero]
      _ = (x * algebraMap R (FractionRing R) (a + b)) *
          algebraMap R (FractionRing R) (a + b) := by rw [hxs, map_mul]
  have hxint : IsIntegral R x := by
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C (1 : R)),
      Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      map_one, mul_sub, mul_one, hidem, sub_self]
  obtain ⟨e, he⟩ := (isIntegrallyClosedIn_iff.mp hclosed).2 hxint
  have hes : e * (a + b) = a := by
    apply IsFractionRing.injective R (FractionRing R)
    simpa only [map_mul, he] using hxs
  have heother : (1 - e) * (a + b) = b := by
    calc
      (1 - e) * (a + b) = (a + b) - e * (a + b) := by ring
      _ = b := by rw [hes]; ring
  have heq : e ∈ q := by
    have hqs : a + b ∉ q := by
      intro h
      exact hbnot q ((hS q).mpr ⟨hq, hpq.symm⟩)
        (q.add_mem_iff_right (hamem q ((hS q).mpr ⟨hq, hpq.symm⟩)) |>.mp h)
    have hm : e * (a + b) ∈ q := hes.symm ▸ hamem q ((hS q).mpr ⟨hq, hpq.symm⟩)
    exact (hq.isPrime.mem_or_mem hm).resolve_right hqs
  have hep : 1 - e ∈ p := by
    have hps : a + b ∉ p := by
      intro h
      exact hap (p.add_mem_iff_left hbp |>.mp h)
    have hm : (1 - e) * (a + b) ∈ p := heother.symm ▸ hbp
    exact (hp.isPrime.mem_or_mem hm).resolve_right hps
  exact Ideal.isCoprime_iff_exists.mpr ⟨1 - e, hep, e, heq, by ring⟩

/-- A reduced ring with finitely many minimal primes that is integrally closed in its
 total fraction ring splits into finitely many domains. This asserts no integral
 closedness of the factors.
Source: Stacks Project, Algebra, Tag 030C, proof, second and third paragraphs.
(blueprint: lem-weil-pbc-integrally-closed-reduced-finite-domain-decomposition).

Proof: enumerate the minimal primes p_i. The nonzerodivisors are precisely the complement
of their union. The primes disjoint from this set are exactly the minimal primes, by finite
prime avoidance. Their localizations are fields. The total fraction ring is reduced and
has just these finitely many maximal ideals, with intersection zero. The product of its
localizations is therefore its decomposition as the product of the fields R_{p_i}.
Each coordinate idempotent satisfies the monic polynomial T^2 - T, so integral closedness
lifts it uniquely to R. Injectivity of R into its total fractions shows that these lifted
idempotents are orthogonal and sum to one. Multiplication by them decomposes R into their
image rings: the forward map is r to (e_i r), and the inverse sums the components.
The i-th image ring embeds into R_{p_i}, because all its other coordinates vanish, and is
nonzero because its identity e_i has i-th coordinate one. It is thus a domain. Package the
image rings as CommRingCat objects indexed by Fin n. If there are no minimal primes, R is
the zero ring, which is the empty product. -/
theorem exists_finite_domain_factors_of_integrallyClosed_totalFractions
    (R : Type u) [CommRing R] [IsReduced R]
    (hfinite : (minimalPrimes R).Finite)
    (hclosed : IsIntegrallyClosedIn R (FractionRing R)) :
    ∃ (n : ℕ) (A : Fin n → CommRingCat.{u}),
      (∀ i : Fin n, IsDomain (A i)) ∧ Nonempty (R ≃+* (∀ i : Fin n, A i)) := by
  classical
  let := hfinite.fintype
  let n := Fintype.card (minimalPrimes R)
  let e : Fin n ≃ minimalPrimes R := (Fintype.equivFin (minimalPrimes R)).symm
  let P : Fin n → Ideal R := fun i ↦ (e i).val
  have hp (i : Fin n) : (P i).IsPrime := (e i).property.isPrime
  have hzero : (⨅ i, P i) = ⊥ := by
    have heq : (⨅ i, P i) = sInf (minimalPrimes R) := by
      apply le_antisymm
      · apply le_sInf
        intro p hpm
        obtain ⟨i, hi⟩ := e.surjective ⟨p, hpm⟩
        exact (iInf_le P i).trans_eq (congrArg Subtype.val hi)
      · apply le_iInf
        intro i
        exact sInf_le (e i).property
    rw [heq, Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced]
  have hcop : Pairwise (fun i j ↦ IsCoprime (P i) (P j)) := by
    intro i j hij
    apply minimalPrimes_pairwise_coprime R hfinite hclosed (P i) (P j)
      (e i).property (e j).property
    intro h
    exact hij (e.injective (Subtype.ext h))
  let A : Fin n → CommRingCat.{u} := fun i ↦ CommRingCat.of (R ⧸ P i)
  refine ⟨n, A, ?_, ?_⟩
  · intro i
    let : (P i).IsPrime := hp i
    exact inferInstanceAs (IsDomain (R ⧸ P i))
  · exact ⟨(RingEquiv.quotientBot R).symm.trans
      ((Ideal.quotEquivOfEq hzero.symm).trans
        (Ideal.quotientInfRingEquivPiQuotient P hcop))⟩
