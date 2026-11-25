/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Regular.Flat
import WeilConjectures.RingTheory.IsRegularOfDimensionDrop
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Equations of a global complete intersection at a prime

Source: Stacks Project, Algebra, proofs of Lemmas 10.135.3 and 10.135.4 (Tags 00SB, 00SC)
(blueprint: lem-weil-pbc-global-complete-intersection-local-regular-sequence).
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- (blueprint: lem-weil-pbc-global-complete-intersection-local-regular-sequence)
Stacks Project, Algebra, proof of Tag 00SB and the last paragraph of the proof of Tag 00SC.
For a nonzero quotient of an `m`-variable polynomial ring by `t` equations of dimension
`m - t`, the equations form a regular sequence after localization at any prime containing
these equations. The dimension hypothesis is written additively, avoiding truncated
subtraction when `t > m`.

Proof (the six steps of the node):
1. Choose a maximal ideal containing the given prime and localize there. All equations
lie in the maximal ideal of this local ring (`def-weil-pbc-localization-at-prime`).
2. This is a regular local ring of dimension `m`, by
`lem-weil-pbc-polynomial-ring-field-regular-ring` and
`lem-weil-pbc-polynomial-ring-maximal-localization-dimension`. Its maximal ideal has a
regular sequence of `m` generators by `lem-weil-pbc-regular-local-generators-regular-sequence`,
so its depth is at least `m` (`def-weil-pbc-depth`).
3. Apply `lem-weil-pbc-noetherian-height-quotient-bound` to the `t` equations: the local
quotient has dimension at least `m - t` (`def-weil-pbc-krull-dimension-ring`).
4. Lift chains of primes of the local quotient to the global quotient via the prime correspondence
for localizations. Thus its dimension is at most the global dimension `m - t`
(`def-kun-topological-krull-dimension`), giving equality.
5. Apply `lem-weil-pbc-cm-local-dimension-drop-regular-sequence` to obtain regularity at
this maximal ideal (`def-weil-pbc-regular-sequence`).
6. Localize further at the given prime using
`lem-weil-pbc-weakly-regular-sequence-localization-prime`; identify this iterated localization with
the original localization (localization at a prime commutes with a previous localization). The
isomorphism preserves the successive quotients and multiplication maps, hence regularity. This final
passage from a maximal ideal to the given prime is the node's elaboration of Tag 00SC. -/
theorem isRegular_localizationAtPrime_of_quotient_dimension
    (k : Type u) [Field k] (m t : ℕ) (f : Fin t → MvPolynomial (Fin m) k)
    [Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f))]
    (hdim : topologicalKrullDim
      (AlgebraicGeometry.Spec
        (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) +
      (t : WithBot ℕ∞) = (m : WithBot ℕ∞))
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : Ideal.span (Set.range f) ≤ q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      ((List.ofFn f).map (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime q))) := by
  classical
  let Q := MvPolynomial (Fin m) k
  let fs := List.ofFn f
  let J := Ideal.span (Set.range f)
  -- The ordered list and the given family generate the same ideal.
  have hfs : Ideal.ofList fs = J := by
    change Ideal.span {x | x ∈ fs} = J
    congr 1
    ext x
    simp [fs]
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q Ideal.IsPrime.ne_top'
  let := hM
  let R := Localization.AtPrime M
  have : IsRegularLocalRing R := inferInstance
  let gs := fs.map (algebraMap Q R)
  have hmem : ∀ g ∈ gs, g ∈ IsLocalRing.maximalIdeal R := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff R M a).mpr
    exact hqM (hq (by
      change a ∈ J
      rw [← hfs]
      exact Ideal.subset_span ha))
  have hd : ringKrullDim R = (m : WithBot ℕ∞) :=
    ringKrullDim_localizationAtMaximal m M
  obtain ⟨s, hcard, hs⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  let rs := s.toList
  have hspan : Ideal.span {x | x ∈ rs} = IsLocalRing.maximalIdeal R := by
    simpa [rs] using hs
  have hlen : rs.length = m := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hd] at h
    have hrank : (IsLocalRing.maximalIdeal R).spanFinrank = m := by exact_mod_cast h
    simp [rs, hcard, hrank]
  have hparams : IsLocalRing.IsRegularSystemOfParameters rs :=
    ⟨hspan, by rw [hlen, hd]⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    R m hd rs hparams).1
  -- A regular system of parameters witnesses the required depth bound.
  have hdepth : (m : ℕ∞) ≤ IsLocalRing.depth (R := R) R := by
    unfold IsLocalRing.depth Ideal.depth
    split_ifs
    · exact le_top
    · apply le_sSup
      refine ⟨rs, hreg, ?_, ?_⟩
      · intro x hx
        rw [← hspan]
        exact Ideal.subset_span hx
      · rw [hlen]
  have hlength : gs.length = t := by simp [gs, fs]
  -- Squeeze the local quotient dimension between the height bound and global dimension.
  have hlower : (m : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.ofList gs) + t := by
    have h := ringKrullDim_le_ringKrullDim_quotient_add_card gs.toFinset (by
      intro x hx
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact hmem x (by simpa using hx))
    have he : Ideal.span (gs.toFinset : Set R) = Ideal.ofList gs := by
      congr 1
      ext x
      simp
    rw [hd, he] at h
    exact h.trans (add_le_add le_rfl (by exact_mod_cast
      ((List.toFinset_card_le gs).trans_eq hlength)))
  have hupper : ringKrullDim (R ⧸ Ideal.ofList gs) ≤ ringKrullDim (Q ⧸ J) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient]
    let e : PrimeSpectrum.zeroLocus (R := R) (Ideal.ofList gs) ↪o
        PrimeSpectrum.zeroLocus (R := Q) J := {
      toFun := fun p => ⟨PrimeSpectrum.comap (algebraMap Q R) p.1, by
        change J ≤ p.1.asIdeal.comap (algebraMap Q R)
        rw [← hfs, Ideal.map_le_iff_le_comap.symm, Ideal.map_ofList]
        exact p.2⟩
      inj' := by
        intro p p' h
        apply Subtype.ext
        apply PrimeSpectrum.ext
        exact (IsLocalization.orderEmbedding M.primeCompl R).injective
          (congrArg (fun p => p.1.asIdeal) h)
      map_rel_iff' := by
        intro p p'
        exact (IsLocalization.orderEmbedding M.primeCompl R).le_iff_le }
    exact Order.krullDim_le_of_orderEmbedding e
  have hglobal : ringKrullDim (Q ⧸ J) + (t : WithBot ℕ∞) = m := by
    change topologicalKrullDim (PrimeSpectrum (Q ⧸ J)) + _ = _ at hdim
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hdim
  have hdrop : ringKrullDim (R ⧸ Ideal.ofList gs) +
      (gs.length : WithBot ℕ∞) = (m : WithBot ℕ∞) := by
    rw [hlength]
    exact le_antisymm ((add_le_add hupper le_rfl).trans_eq hglobal) hlower
  have hregular := RingTheory.Sequence.isRegular_of_dimension_drop m hd hdepth gs hmem hdrop
  -- Localize R directly into Q_q; no choice of an iterated-localization isomorphism.
  let S := Localization.AtPrime q
  have hle : M.primeCompl ≤ q.primeCompl := fun x hx hxq => hx (hqM hxq)
  let : Algebra R S := IsLocalization.localizationAlgebraOfSubmonoidLe R S
    M.primeCompl q.primeCompl hle
  let : IsScalarTower Q R S := IsLocalization.localization_isScalarTower_of_submonoid_le
    R S M.primeCompl q.primeCompl hle
  let : IsLocalization (q.primeCompl.map (algebraMap Q R)) S :=
    IsLocalization.isLocalization_of_submonoid_le R S M.primeCompl q.primeCompl hle
  have hweak := hregular.1.of_isLocalization S (q.primeCompl.map (algebraMap Q R))
  have hmap : gs.map (algebraMap R S) = fs.map (algebraMap Q S) := by
    simp only [gs, List.map_map]
    congr 1
    exact congrArg (fun h : Q →+* S => (h : Q → S))
      (IsScalarTower.algebraMap_eq Q R S).symm
  rw [hmap] at hweak
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := S) (fun g hg => ?_)).mpr hweak
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S q a).mpr
  apply hq
  change a ∈ J
  rw [← hfs]
  exact Ideal.subset_span ha

end MvPolynomial
