/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.Height
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionAtPointComponents
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension

/-!
# Dimension at a point of a polynomial quotient

Source: Stacks Project, Algebra, Tags 00P2, 00P1, 00OP, and the opening of Tag 00SC
(blueprint: lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Tag 00P2 (`lemma-codimension`), applied to a polynomial
quotient; Tags 00P1 and 00OP give dimension n at every point of the polynomial spectrum.
This is the dimension identity used at the opening of Tag 00SC (`lemma-lci`).
(blueprint: lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference).

The heights of q in the quotient and its inverse image in the polynomial ring are finite
natural numbers h and h' (so 0 ≤ h), with h ≤ h' ≤ n; the local topological dimension
is n - h' + h.

Proof (the seven steps of the node):
1. The polynomial ring P and its quotient S are finite type k-algebras
   (`def-weil-pbc-finite-type-algebra`). P is a domain by
   `lem-weil-pbc-polynomial-ring-domain`, so its only minimal prime is zero.
   The inverse image q' of q under the quotient map is prime and contains I.
2. Apply `lem-weil-pbc-dimension-at-point-local-ring-trdeg` (00P1) to S at q and P at q'.
   Identify the local-ring dimensions with the heights by
   `lem-weil-pbc-localization-dimension-chains-below-prime`. Thus both heights are finite,
   and each local topological dimension is its height plus the residue-field trdeg.
3. By `lem-weil-pbc-localization-at-prime-of-quotient`, the quotient map induces a
   surjection P_q' → S_q. Composing with the residue map has kernel the maximal ideal
   q'P_q': the kernel is proper and hence lies in the maximal ideal, and the reverse
   inclusion follows directly from the definition of q'. It therefore identifies the
   residue fields as k-algebras. Algebraic independence is preserved, so their trdegs agree
   (`def-kun-transcendence-degree`).
4. Subtract the two finite dimension identities to obtain 00P2: the difference of the
   local topological dimensions equals h' - h.
5. By `lem-weil-pbc-dimension-at-point-components`, the dimension at q' of Spec P is
   dim P, since zero is the only minimal prime. Choose a maximal ideal using
   `lem-weil-pbc-proper-ideal-contained-in-maximal`. By
   `lem-weil-pbc-finite-type-domain-dimension-local-ring`, dim P is its local-ring dimension
   there, which is n by `lem-weil-pbc-polynomial-ring-maximal-localization-dimension` (00OP).
6. Steps 4 and 5 give dim_q Spec S = n - h' + h. The 00P1 identity at q' also gives
   n = h' + trdeg_k κ(q'), so h' ≤ n.
7. Lift any strict prime chain below q along the surjective quotient map. Inverse images
   are prime and remain strict: equal inverse images would give equal ideals by
   surjectivity. Their last member lies below q'. Taking suprema gives h ≤ h'. Both
   heights are nonnegative since the single-prime chain has length zero. -/
theorem topologicalKrullDimAt_polynomial_quotient_eq_height_difference
    {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : Ideal (MvPolynomial (Fin n) k ⧸ I)) [q.IsPrime] :
    ∃ h h' : ℕ,
      q.height = (h : ℕ∞) ∧
      (q.comap (Ideal.Quotient.mk I)).height = (h' : ℕ∞) ∧
      h ≤ h' ∧ h' ≤ n ∧
      topologicalKrullDimAt
        (⟨q, inferInstance⟩ : Spec (CommRingCat.of (MvPolynomial (Fin n) k ⧸ I))) =
        ((n - h' + h : ℕ) : WithBot ℕ∞) := by
  classical
  let p := q.comap (Ideal.Quotient.mk I)
  obtain ⟨d, r, hd, hr, hdim⟩ :=
    topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) q
  obtain ⟨d', r', hd', hr', hdim'⟩ :=
    topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) p
  have hq : q.height = (d : ℕ∞) := by
    exact_mod_cast (IsLocalization.AtPrime.ringKrullDim_eq_height q _).symm.trans hd
  have hp : p.height = (d' : ℕ∞) := by
    exact_mod_cast (IsLocalization.AtPrime.ringKrullDim_eq_height p _).symm.trans hd'
  let f : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k ⧸ I :=
    Ideal.Quotient.mkₐ k I
  let e : p.ResidueField ≃ₐ[k] q.ResidueField :=
    AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ p q f rfl)
      (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
        p q rfl)
  have hrr : r' = r := by
    have he := e.trdeg_eq
    rw [hr', hr] at he
    exact_mod_cast he
  obtain ⟨qs, hqs, hne, a, ha, hupper, hcomp, hquot, hquot', hmax, m, hm, hpm, hma⟩ :=
    dimension_at_point_components (k := k) p
  have : m.IsMaximal := hm
  have han : (a : WithBot ℕ∞) = (n : WithBot ℕ∞) :=
    hma.symm.trans (MvPolynomial.ringKrullDim_localizationAtMaximal n m)
  have hsum : d' + r = n := by
    have he := hdim'.symm.trans (ha.trans han)
    rw [hrr] at he
    exact_mod_cast he
  have hheight : q.height ≤ p.height := by
    change (⟨q, inferInstance⟩ : PrimeSpectrum _).asIdeal.height ≤
      (PrimeSpectrum.comap (Ideal.Quotient.mk I) ⟨q, inferInstance⟩).asIdeal.height
    rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
    apply Order.height_le_height_apply_of_strictMono
    intro x y hxy
    change x.asIdeal.comap (Ideal.Quotient.mk I) < y.asIdeal.comap (Ideal.Quotient.mk I)
    exact (Ideal.orderEmbeddingOfSurjective
      (f := Ideal.Quotient.mk I) (Ideal.Quotient.mk_surjective (I := I))).strictMono hxy
  have hdd : d ≤ d' := by
    rw [hq, hp] at hheight
    exact_mod_cast hheight
  refine ⟨d, d', hq, hp, hdd, ?_, ?_⟩
  · omega
  · have hle : d' ≤ n := by omega
    have harith : d + r = n - d' + d := by omega
    simpa [harith] using hdim

end AlgebraicGeometry
