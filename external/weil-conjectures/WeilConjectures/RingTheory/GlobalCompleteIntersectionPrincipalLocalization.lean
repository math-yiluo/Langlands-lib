/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Principal localization of a global complete intersection

Source: Stacks Project, Algebra, Lemma Tag 00SA (lemma-localize-lci), part (1)
(blueprint: lem-weil-pbc-global-complete-intersection-principal-localization).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A principal localization of a global complete intersection over a field is a global
complete intersection over that field.

Source: Stacks Project, Algebra, Lemma Tag 00SA (lemma-localize-lci), part (1)
(blueprint: lem-weil-pbc-global-complete-intersection-principal-localization).

Proof: If the localization is zero, use the zero-ring clause. Otherwise its source and
any polynomial quotient presenting the source are nonzero. Transport Mathlib's naive
presentation of that quotient to `T`, compose it with `Presentation.localizationAway`,
and reindex the resulting variables and relations by `Fin (n + 1)` and `Fin (c + 1)`.
Mathlib's composition theorem supplies the kernel calculation and quotient equivalence.
For the dimension, embed the localized spectrum as an open subspace of the original
polynomial quotient's spectrum. Its dimension is bounded above by the ambient dimension.
Choose a point of the nonempty localized spectrum. Equidimensionality gives dimension
`n - c` at its image, which is bounded above by the dimension of this open neighborhood
by the infimum defining local dimension. Thus the localization has dimension `n - c`,
equal to `(n + 1) - (c + 1)`, as required. -/
theorem isGlobalCompleteIntersection_localizationAway
    (k : Type u) (T : Type v) [Field k] [CommRing T] [Algebra k T]
    (hT : IsGlobalCompleteIntersection k T) (g : T) :
    IsGlobalCompleteIntersection k (Localization.Away g) := by
  classical
  by_cases hzero : Subsingleton (Localization.Away g)
  · exact Or.inl hzero
  have : Nontrivial (Localization.Away g) := not_subsingleton_iff_nontrivial.mp hzero
  have : Nontrivial T := (algebraMap T (Localization.Away g)).domain_nontrivial
  rcases hT with hT | ⟨n, c, f, hcn, ⟨e⟩, hdim⟩
  · exact False.elim (zero_ne_one (hT.elim 0 1))
  let A := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)
  have : Nontrivial A := e.toEquiv.nontrivial
  let P : Presentation k T (Fin n) (Fin c) :=
    (Presentation.naive (v := f)).ofAlgEquiv e
  let Q := (Presentation.localizationAway (Localization.Away g) g).comp P
  let ev : Fin (n + 1) ≃ Unit ⊕ Fin n :=
    Fintype.equivOfCardEq (by simp [Nat.add_comm])
  let er : Fin (c + 1) ≃ Unit ⊕ Fin c :=
    Fintype.equivOfCardEq (by simp [Nat.add_comm])
  let Q' := Q.reindex ev er
  refine Or.inr ⟨n + 1, c + 1, Q'.relation, Nat.add_le_add_right hcn 1, ?_, ?_⟩
  · rw [Q'.span_range_relation_eq_ker]
    exact ⟨Q'.quotientEquiv.restrictScalars k⟩
  · rw [Nat.add_sub_add_right]
    let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
    let j := H.symm ∘ PrimeSpectrum.comap (algebraMap T (Localization.Away g))
    have hj : Topology.IsOpenEmbedding j :=
      H.symm.isOpenEmbedding.comp (PrimeSpectrum.localization_away_isOpenEmbedding _ g)
    have hA : topologicalKrullDim (PrimeSpectrum A) = (↑(n - c) : WithBot ℕ∞) := by
      rw [← H.isHomeomorph.topologicalKrullDim_eq] at hdim
      exact hdim
    have hlocal := AlgebraicGeometry.topologicalKrullDimAt_spec_quotient_mvPolynomial_of_eq
      k n c f inferInstance ⟨hcn, hA⟩
    rw [hj.isEmbedding.topologicalKrullDim_eq_range]
    apply le_antisymm
    · exact (topologicalKrullDim_subspace_le _ _).trans_eq hA
    · obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum (Localization.Away g)))
      rw [← hlocal (j x)]
      exact iInf₂_le (TopologicalSpace.Opens.mk (Set.range j) hj.isOpen_range)
        (Set.mem_range_self x)

end Algebra
