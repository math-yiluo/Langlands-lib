/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import all WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import WeilConjectures.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import WeilConjectures.RingTheory.CompleteIntersectionPresentationStableConormal
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Rank of the conormal module at a complete intersection point

Source: Stacks Project, Algebra, Lemma 00SC, implication (1) implies (4)
(blueprint: lem-weil-pbc-lci-conormal-free-rank-codimension).
-/

@[expose] public section

universe u

namespace Ideal

private theorem basis_of_stably_free {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (a b : ℕ)
    (e : (M × (Fin a → R)) ≃ₗ[R] (Fin b → R)) :
    a ≤ b ∧ Nonempty (Module.Basis (Fin (b - a)) R M) := by
  let i : M →ₗ[R] (Fin b → R) := e.toLinearMap.comp (LinearMap.inl R M (Fin a → R))
  let s : (Fin b → R) →ₗ[R] M :=
    (LinearMap.fst R M (Fin a → R)).comp e.symm.toLinearMap
  have hs : s.comp i = LinearMap.id := by
    ext x
    simp [s, i]
  let : Module.Projective R M := Module.Projective.of_split i s hs
  let : Module.Finite R M := Module.Finite.of_surjective s (by
    intro x
    exact ⟨i x, LinearMap.congr_fun hs x⟩)
  let : Module.Free R M := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank R M + a = b := by
    simpa only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] using e.finrank_eq
  refine ⟨by omega, ⟨Module.finBasisOfFinrankEq R M (by omega)⟩⟩

/-- Stacks Project, Algebra, Lemma 00SC, implication (1) implies (4).
(blueprint: lem-weil-pbc-lci-conormal-free-rank-codimension)
The dimension here is the topological dimension at the point, not the dimension of its
local ring. `I.Cotangent` is `I/I²` with its canonical quotient-ring action, and
`Localization.AtPrime q.asIdeal` acts on its localization by Mathlib's fraction action
`OreLocalization.instModule`.

Proof plan, following the node's six steps:
1. Localize at `g`. The localization-prime-residue-field-iso lemma identifies the prime
   above `q` and its local ring with `S_q`. Choose a global complete intersection
   presentation `k[y₁, ..., yₘ]/J` with `t` equations and dimension `m - t`.
2. The principal-localization-open-immersion and dimension-at-point-open-subspace lemmas
   preserve dimension at `q`. Global-complete-intersection-equidimensional gives `d = m - t`.
3. Global-complete-intersection-local-regular-sequence gives a regular sequence of length
   `t` at the corresponding polynomial prime. Regular-sequence-conormal-free gives a
   free conormal module with the classes of those equations as basis.
4. Localization-module-exact identifies this conormal module with the localization of
   `J/J²`, over the local ring identified with `S_q` in step 1.
5. Conormal-module-principal-localization compares the two polynomial presentations.
   Localize its isomorphism again at the prime: if `N = (I/I²)_q`, it yields
   `N ⊕ S_q^m ≅ S_q^(t+n)`; successive module localizations identify its first term with `N`.
6. This makes `N` a finite projective module, hence flat by projective-module-flat.
   Finite-flat-local-free gives freeness. Reduction to the residue field computes the
   basis cardinality as `t + n - m = n - d`, hence also `0 ≤ d ≤ n`.
-/
theorem exists_basis_cotangent_localization_of_completeIntersection
    {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))
    (hci : ∃ g : MvPolynomial (Fin n) k ⧸ I,
      g ∉ q.asIdeal ∧ Algebra.IsGlobalCompleteIntersection k (Localization.Away g)) :
    ∃ d : ℕ, topologicalKrullDimAt q = (d : WithBot ℕ∞) ∧ d ≤ n ∧
      Nonempty (Module.Basis (Fin (n - d)) (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl I.Cotangent)) := by
  classical
  obtain ⟨g, hg, hci⟩ := hci
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum (Localization.Away g),
      PrimeSpectrum.comap (algebraMap _ (Localization.Away g)) p = q := by
    have hq : q ∈ Set.range (PrimeSpectrum.comap
        (algebraMap _ (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hg
    exact hq
  let : Nontrivial (Localization.Away g) := p.nontrivial
  rcases hci with hz | ⟨m, t, f, htm, ⟨e⟩, hdim⟩
  · exact False.elim (zero_ne_one (hz.elim 0 1))
  let T := MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)
  let : Nontrivial T := e.toEquiv.nontrivial
  let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
  have hdT : topologicalKrullDim (AlgebraicGeometry.Spec (CommRingCat.of T)) =
      ((m - t : ℕ) : WithBot ℕ∞) := by
    exact H.isHomeomorph.topologicalKrullDim_eq.trans hdim
  have hd : topologicalKrullDimAt q = ((m - t : ℕ) : WithBot ℕ∞) := by
    rw [← hp, ← Algebra.dimAt_openEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away g) g) p]
    rw [← H.apply_symm_apply p, ← Algebra.dimAt_openEmbedding H.isOpenEmbedding (H.symm p)]
    exact AlgebraicGeometry.topologicalKrullDimAt_spec_quotient_mvPolynomial_of_eq
      k m t f inferInstance ⟨htm, hdT⟩ (H.symm p)
  obtain ⟨E⟩ := Ideal.stable_conormal_of_completeIntersection_presentation n I q g hg
    m t f htm e hdim
  obtain ⟨hle, ⟨b⟩⟩ := basis_of_stably_free m (t + n) E
  have hdn : m - t ≤ n := by omega
  have hr : t + n - m = n - (m - t) := by omega
  exact ⟨m - t, hd, hdn, ⟨b.reindex (finCongr hr)⟩⟩

end Ideal
