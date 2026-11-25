/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Localization.Ideal

@[expose] public section

universe u

namespace Algebra

/-- The local topological dimension of a polynomial quotient cut out at the point by
an e-term regular sequence is n-e, and e is at most n. Source: Stacks Project,
Algebra, Lemma 00SC (5) implies (2), using 00KW and 00P2.
(blueprint: lem-weil-pbc-regular-sequence-dimension-at-point).
Proof: the quotient of the localized polynomial ring is the localization of the
quotient. The regular-sequence dimension formula says its dimension plus e equals
the dimension of the localized polynomial ring. These dimensions are the heights
of q and its inverse image. Substituting in the polynomial-quotient dimension-at-point
formula gives n-e; the bound on the inverse-image height gives e ≤ n. -/
theorem regularSequence_dimensionAtPoint
    (k : Type u) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Ideal (MvPolynomial (Fin n) k ⧸ I)) (hq : q.IsPrime)
    (e : ℕ) (h : Fin e → Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))
    (hreg : RingTheory.Sequence.IsRegular
      (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))) (List.ofFn h))
    (hgen : Ideal.map
      (algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))) I =
      Ideal.span (Set.range h)) :
    e ≤ n ∧ topologicalKrullDimAt
      (⟨q, hq⟩ : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I)) =
      ((n - e : ℕ) : WithBot ℕ∞) := by
  let : q.IsPrime := hq
  let P := MvPolynomial (Fin n) k
  let p := q.comap (Ideal.Quotient.mk I)
  let R := Localization.AtPrime p
  let J := I.map (algebraMap P R)
  have hM : Algebra.algebraMapSubmonoid (P ⧸ I) p.primeCompl = q.primeCompl := by
    exact q.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective
  let : IsLocalization q.primeCompl (R ⧸ J) := by
    rw [← hM]
    infer_instance
  let iso := IsLocalization.algEquiv q.primeCompl (R ⧸ J) (Localization.AtPrime q)
  obtain ⟨d, d', hd, hd', hdd, hd'n, hdim⟩ :=
    AlgebraicGeometry.topologicalKrullDimAt_polynomial_quotient_eq_height_difference n I q
  have hlist : Ideal.ofList (List.ofFn h) = J := by
    change Ideal.span {x | x ∈ List.ofFn h} = J
    have hs : {x | x ∈ List.ofFn h} = Set.range h := by
      ext x
      simp
    rw [hs]
    exact hgen.symm
  have hdrop := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular (List.ofFn h) hreg
  rw [hlist, ringKrullDim_eq_of_ringEquiv iso.toRingEquiv,
    IsLocalization.AtPrime.ringKrullDim_eq_height q,
    IsLocalization.AtPrime.ringKrullDim_eq_height p, hd, hd', List.length_ofFn] at hdrop
  have heq : d + e = d' := by exact_mod_cast hdrop
  refine ⟨by omega, ?_⟩
  have harith : n - d' + d = n - e := by omega
  simpa [harith] using hdim

end Algebra
