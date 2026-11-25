/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
import WeilConjectures.RingTheory.PrincipalLocalizationAlgEquiv
import WeilConjectures.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Principal localization preserves the specified complete intersection presentation

Source: Stacks Project, Algebra, Lemma Tag 00SS (2), with the dimension argument
from Tag 00SA and the paragraph after Definition 00S9.
(blueprint: new-principal-localization-ci).
-/

@[expose] public section
universe u
namespace Algebra

/-- Polynomial quotient presentations commute with scalar extension. -/
private noncomputable def fibrePresentationEquiv
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R) :
    (_root_.TensorProduct R K (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) ≃ₐ[K]
      (MvPolynomial (Fin n) K ⧸
        Ideal.span (Set.range (fun i ↦ MvPolynomial.map (algebraMap R K) (f i)))) := by
  let e := MvPolynomial.algebraTensorAlgEquiv R K (σ := Fin n)
  refine (Algebra.TensorProduct.tensorQuotientEquiv K _ K _).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  rw [Ideal.map_span, Ideal.map_span]
  congr 1
  ext x
  simp [e, Set.mem_image, Set.mem_range, Algebra.TensorProduct.includeRight_apply]

/-- A nonempty open subspace of a spectrum with constant local dimension has that dimension. -/
private theorem principalOpen_dim
    {A B : Type u} [CommRing A] [CommRing B] [Nontrivial B]
    (j : PrimeSpectrum B → PrimeSpectrum A) (hj : Topology.IsOpenEmbedding j)
    (d : WithBot ℕ∞) (hd : topologicalKrullDim (PrimeSpectrum A) = d)
    (hl : ∀ x : PrimeSpectrum A, topologicalKrullDimAt x = d) :
    topologicalKrullDim (PrimeSpectrum B) = d := by
  rw [hj.isEmbedding.topologicalKrullDim_eq_range]
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le _ _).trans_eq hd
  · obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum B))
    rw [← hl (j x)]
    exact iInf₂_le (TopologicalSpace.Opens.mk (Set.range j) hj.isOpen_range)
      (Set.mem_range_self x)

/-- Adjoining an inverse preserves the relative global complete intersection condition.
After tensoring with every residue field of the base, the original presentation has
equidimensional fibres of dimension `n - c` by `hrel`. The enlarged fibre is the
principal open where the image of `h` is invertible, presented with one extra
variable and one extra equation. Principal opens preserve the local dimensions on
this equidimensional fibre, so its dimension is still `n - c`, equal to
`(n + 1) - (c + 1)`. This is exactly the defining fibre condition. Source: Stacks
Project, Algebra, Lemma Tag 00SS, part (2).
(blueprint: new-principal-localization-ci) -/
theorem principalLocalization_ci
    (R : Type u) [CommRing R] (n c : ℕ)
    (f : Fin c → MvPolynomial (Fin n) R)
    (hrel : IsRelativeGlobalCompleteIntersectionPresentation f)
    (h : MvPolynomial (Fin n) R) :
    IsRelativeGlobalCompleteIntersectionPresentation
        (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (n + 1)) R)
          (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
          (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last n) - 1)) := by
  intro p hp hnonzero
  let := hp
  let := hnonzero
  let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let g : S := Ideal.Quotient.mk (Ideal.span (Set.range f)) h
  obtain ⟨e, _⟩ := principalLocalization_algEquiv R n c f h
  let E := (Algebra.TensorProduct.congr
    (AlgEquiv.refl (R := p.ResidueField) (A₁ := p.ResidueField)) e).trans
      (IsLocalization.Away.tensorProductEquivTMulRight R p.ResidueField g
        (Localization.Away g))
  let F := p.Fiber S
  let a : F := _root_.TensorProduct.tmul R (1 : p.ResidueField) g
  let : Nontrivial (Localization.Away a) := E.symm.toEquiv.nontrivial
  let : Nontrivial F := (algebraMap F (Localization.Away a)).domain_nontrivial
  obtain ⟨hc, hdim⟩ := hrel p inferInstance
  let q := fibrePresentationEquiv R p.ResidueField n c f
  let Q := MvPolynomial (Fin n) p.ResidueField ⧸
    Ideal.span (Set.range (fun i ↦ MvPolynomial.map (algebraMap R p.ResidueField) (f i)))
  let : Nontrivial Q := q.symm.toEquiv.nontrivial
  let H := PrimeSpectrum.homeomorphOfRingEquiv q.toRingEquiv
  have hQ : topologicalKrullDim (PrimeSpectrum Q) = (n - c : ℕ) := by
    rw [← H.isHomeomorph.topologicalKrullDim_eq]
    exact hdim
  have hlocal := AlgebraicGeometry.topologicalKrullDimAt_spec_quotient_mvPolynomial_of_eq
    p.ResidueField n c
    (fun i ↦ MvPolynomial.map (algebraMap R p.ResidueField) (f i))
    inferInstance ⟨hc, hQ⟩
  have hloc : topologicalKrullDim (PrimeSpectrum (Localization.Away a)) =
      (n - c : ℕ) := by
    apply principalOpen_dim (H ∘ PrimeSpectrum.comap (algebraMap F (Localization.Away a)))
      (H.isOpenEmbedding.comp (PrimeSpectrum.localization_away_isOpenEmbedding _ a))
      _ hQ
    intro x
    exact hlocal x
  refine ⟨Nat.add_le_add_right hc 1, ?_⟩
  rw [Nat.add_sub_add_right]
  have hE := IsHomeomorph.topologicalKrullDim_eq _
    (PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv).isHomeomorph
  exact hE.trans hloc

end Algebra
