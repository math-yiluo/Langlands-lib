/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersection
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.MvPolynomial.Rename
import WeilConjectures.RingTheory.FibreDimensionNeighborhood
import WeilConjectures.RingTheory.PolynomialQuotientDimensionLowerBound
import WeilConjectures.RingTheory.EquationCountLocalizePresentation
import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Choosing a localization with the expected fibre dimensions

Source: Stacks Project, Algebra, Lemma 00ST (3), using 00QH and 0B7I.
-/

@[expose] public section

universe u

namespace Algebra

/-- Reindex a finite polynomial presentation along equivalences of both index types. -/
private noncomputable def reindex_quotient
    {R : Type u} [CommRing R] {ι σ ι' σ' : Type}
    (ev : ι ≃ ι') (er : σ ≃ σ') (f : σ → MvPolynomial ι R) :
    (MvPolynomial ι R ⧸ Ideal.span (Set.range f)) ≃ₐ[R]
      (MvPolynomial ι' R ⧸ Ideal.span
        (Set.range (fun j ↦ MvPolynomial.rename ev (f (er.symm j))))) := by
  let e := MvPolynomial.renameEquiv R ev
  apply Ideal.quotientEquivAlg _ _ e
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨f (er.symm j), ⟨er.symm j, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨er i, by simp [e]⟩

/-- The naive presentation base changes to the quotient by its coefficient images. -/
private noncomputable def polynomialQuotient_baseChange
    (R : Type u) (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R) :
    (MvPolynomial (Fin n) R' ⧸
      Ideal.span (Set.range (fun i ↦ MvPolynomial.map (algebraMap R R') (f i))))
      ≃ₐ[R'] _root_.TensorProduct R R'
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) := by
  classical
  let P := (Presentation.naive (v := f)).baseChange R'
  exact (Ideal.quotientEquivAlgOfEq R' P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars R')

/-- There is a polynomial avoiding q whose enlarged quotient has the expected fibre dimensions.
Source: Stacks Project, Algebra, Lemma 00ST (3), proof via 00QH, and dimension formula 0B7I.
(blueprint: new-equation-count-localize-rgci).

Proof: the finite polynomial quotient S is finite type over R. Apply 00QH at q to find
an open neighbourhood V where each point has local fibre dimension at most n-c. Since basic
opens form a basis, choose g avoiding q with D(g) contained in V, and lift g to a polynomial h
using quotient surjectivity. Over a residue field, the fibre of S is a polynomial quotient
by c equations in n variables. The polynomial quotient dimension formula and Krull's height
bound imply local dimension at least n-c at each point. The fibre of S_g is the principal
open defined by g in the corresponding fibre of S, and dimension at a point is unchanged
on an open subspace. Thus all points of each fibre of S_g have local dimension exactly n-c.
The inverse-variable presentation identifies T with S_g, and base change transports this
identification to every fibre. For a nonzero fibre the spectrum is nonempty; its dimension
is the supremum of its local dimensions (0B7I), hence n-c. The count for the displayed
presentation is (n+1)-(c+1)=n-c, and c+1 ≤ n+1 follows from c ≤ n. Reindex the Option variables
and equations by Fin (n+1) and Fin (c+1), using their standard equivalences. The quotient
isomorphism under this reindexing and the fibre dimensions provide the existential finite
presentation in the definition of IsRelativeGlobalCompleteIntersection. -/
theorem localized_presentation_is_relativeGlobalCompleteIntersection
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hdim : let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
      let p := PrimeSpectrum.comap (algebraMap R S) q
      c ≤ n ∧ topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩) = (n - c : ℕ))
    : ∃ h : MvPolynomial (Fin n) R,
    let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
    let g : S := Ideal.Quotient.mk _ h
    g ∉ q.asIdeal ∧
    let relations : Option (Fin c) → MvPolynomial (Option (Fin n)) R :=
      Option.elim' (MvPolynomial.rename some h * MvPolynomial.X none - 1)
        (fun i ↦ MvPolynomial.rename some (f i))
    let T := MvPolynomial (Option (Fin n)) R ⧸ Ideal.span (Set.range relations)
    IsRelativeGlobalCompleteIntersection (algebraMap R T) ∧
      (∀ (p : Ideal R) (_hp : p.IsPrime),
        letI : p.IsPrime := _hp
        Nontrivial (p.Fiber T) →
          c + 1 ≤ n + 1 ∧
            topologicalKrullDim (PrimeSpectrum (p.Fiber T)) =
              (n + 1 - (c + 1) : ℕ)) := by
  classical
  let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  obtain ⟨g, hg, hupper⟩ := exists_away_fibre_dimension_le (R := R) (S := S)
    q (n - c) hdim.2
  obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective g
  subst g
  let relations : Option (Fin c) → MvPolynomial (Option (Fin n)) R :=
    Option.elim' (MvPolynomial.rename some h * MvPolynomial.X none - 1)
      (fun i ↦ MvPolynomial.rename some (f i))
  let T := MvPolynomial (Option (Fin n)) R ⧸ Ideal.span (Set.range relations)
  let fr : Fin (c + 1) → MvPolynomial (Fin (n + 1)) R :=
    fun j ↦ MvPolynomial.rename (finSuccEquiv n).symm (relations (finSuccEquiv c j))
  let U := MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span (Set.range fr)
  let E : T ≃ₐ[R] U :=
    reindex_quotient (finSuccEquiv n).symm (finSuccEquiv c).symm relations
  obtain ⟨e, _, _⟩ := exists_localization_presentation R n c f h
  have hc : c + 1 ≤ n + 1 := Nat.add_le_add_right hdim.1 1
  have hsub : n + 1 - (c + 1) = n - c := by omega
  have hfibre (p : Ideal R) (hp : p.IsPrime) :
      letI : p.IsPrime := hp
      Nontrivial (p.Fiber T) →
        topologicalKrullDim (PrimeSpectrum (p.Fiber T)) = (n - c : ℕ) := by
    let : p.IsPrime := hp
    intro hn
    have : Nontrivial (p.Fiber T) := hn
    let eT : p.Fiber T ≃ₐ[p.ResidueField]
        p.Fiber (Localization.Away (Ideal.Quotient.mk _ h)) :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField]
        p.ResidueField) e
    have : Nontrivial (p.Fiber (Localization.Away (Ideal.Quotient.mk _ h))) :=
      eT.symm.toEquiv.nontrivial
    have hu := hupper (⟨p, hp⟩ : PrimeSpectrum R) inferInstance
    have hdT : topologicalKrullDim (PrimeSpectrum (p.Fiber T)) =
        topologicalKrullDim
          (PrimeSpectrum (p.Fiber (Localization.Away (Ideal.Quotient.mk _ h)))) :=
      IsHomeomorph.topologicalKrullDim_eq
        (PrimeSpectrum.homeomorphOfRingEquiv eT.toRingEquiv)
        (PrimeSpectrum.homeomorphOfRingEquiv eT.toRingEquiv).isHomeomorph
    let eU : p.Fiber U ≃ₐ[p.ResidueField] p.Fiber T :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField]
        p.ResidueField) E.symm
    let eP := polynomialQuotient_baseChange R p.ResidueField (n + 1) (c + 1) fr
    have : Nontrivial (p.Fiber U) := eU.toEquiv.nontrivial
    have : Nontrivial (MvPolynomial (Fin (n + 1)) p.ResidueField ⧸
        Ideal.span (Set.range (fun i ↦ MvPolynomial.map
          (algebraMap R p.ResidueField) (fr i)))) := eP.toEquiv.nontrivial
    have hl := AlgebraicGeometry.sub_le_topologicalKrullDim_spec_mvPolynomial_quotient
      p.ResidueField (n + 1) (c + 1) hc
      (fun i ↦ MvPolynomial.map (algebraMap R p.ResidueField) (fr i))
    have hdP := IsHomeomorph.topologicalKrullDim_eq
      (PrimeSpectrum.homeomorphOfRingEquiv (eP.trans eU).toRingEquiv)
      (PrimeSpectrum.homeomorphOfRingEquiv (eP.trans eU).toRingEquiv).isHomeomorph
    apply le_antisymm
    · exact hdT.le.trans hu
    · change ((n + 1 - (c + 1) : ℕ) : WithBot ℕ∞) ≤
        topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin (n + 1)) p.ResidueField ⧸
          Ideal.span (Set.range (fun i ↦ MvPolynomial.map
            (algebraMap R p.ResidueField) (fr i))))) at hl
      rw [hsub, hdP] at hl
      exact hl
  refine ⟨h, hg, ?_, ?_⟩
  · change IsRelativeGlobalCompleteIntersection (algebraMap R T)
    unfold IsRelativeGlobalCompleteIntersection
    rw [toAlgebra_algebraMap]
    refine ⟨n + 1, c + 1, fr, E.symm, ?_⟩
    intro p hp hn
    let : p.IsPrime := hp
    have : Nontrivial (p.Fiber U) := hn
    let eU : p.Fiber U ≃ₐ[p.ResidueField] p.Fiber T :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField]
        p.ResidueField) E.symm
    have : Nontrivial (p.Fiber T) := eU.symm.toEquiv.nontrivial
    refine ⟨hc, ?_⟩
    rw [hsub]
    exact (IsHomeomorph.topologicalKrullDim_eq
      (PrimeSpectrum.homeomorphOfRingEquiv eU.toRingEquiv)
      (PrimeSpectrum.homeomorphOfRingEquiv eU.toRingEquiv).isHomeomorph).trans
      (hfibre p hp inferInstance)
  · intro p hp hn
    exact ⟨hc, by simpa only [hsub] using hfibre p hp hn⟩

end Algebra
