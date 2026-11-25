/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersection
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
import WeilConjectures.RingTheory.EquationCountLocalizePresentation
import WeilConjectures.RingTheory.EquationCountLocalizeRGCI

/-!
# Localizing an equation-count presentation

Source: Stacks Project, Algebra, Lemma 00ST (3)
(blueprint: lem-weil-pbc-equation-count-localize-relative-global-complete-intersection).
-/

@[expose] public section

universe u

namespace Algebra

/-- At a prime where the fibre has dimension equal to the number of variables minus the
number of equations, adjoining the inverse of a suitable polynomial gives a relative global
complete intersection with this specific enlarged presentation: besides the ring-map predicate
`IsRelativeGlobalCompleteIntersection`, which only asserts some presentation, the second conjunct
is the definition's fibre condition for THIS presentation with `n+1` variables and `c+1`
equations. The `Option` indices add one variable and one equation. The inequalities encode
signed dimension counts without truncated subtraction.

Source: Stacks Project, Algebra, Lemma 00ST (3)
(blueprint: lem-weil-pbc-equation-count-localize-relative-global-complete-intersection).

Proof: apply the fibre-dimension upper-semicontinuity lemma 00QH to obtain an open neighbourhood
of the given prime on which local fibre dimensions are at most `n-c`. Choose a basic open
`D(g)` inside it and lift `g` to a polynomial `h`. The polynomial-quotient presentation of
localization identifies the enlarged quotient with `S_g`, sending the old variables to their
images and the new variable to `1/g`. Polynomial scalar extension and tensor-quotient base
change present every fibre of `S` by `c` equations in `n` variables. The height-difference
formula and Krull's height bound give the lower bound `n-c` at every point of every fibre.
Tensoring localization with the residue field identifies every fibre of `S_g` with the
localization of the corresponding fibre of `S`. Its spectrum is the basic open `D(g)` in that
fibre. Local dimension is unchanged on an open subspace, so both bounds apply and give equality
at every point. Finally, dimension is the supremum of the dimensions at points, so every
nonempty fibre of the enlarged quotient has dimension `n-c = (n+1)-(c+1)`. These are the seven
steps of the blueprint proof, using respectively the bounded-open-upstairs, basic-open localization,
polynomial-quotient localization, height-quotient-bound, localization-tensor, dimension on open
subspaces, and dimension-supremum-local-dimensions nodes. -/
theorem exists_localization_relativeGlobalCompleteIntersection
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hdim :
      let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
      let p := PrimeSpectrum.comap (algebraMap R S) q
      c ≤ n ∧ topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩) = (n - c : ℕ)) :
    ∃ h : MvPolynomial (Fin n) R,
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
              topologicalKrullDim (PrimeSpectrum (p.Fiber T)) = (n + 1 - (c + 1) : ℕ)) ∧
        ∃ e : T ≃ₐ[R] Localization.Away g,
          (∀ i : Fin n,
            e (Ideal.Quotient.mk _ (MvPolynomial.X (some i))) =
              algebraMap S (Localization.Away g) (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
          e (Ideal.Quotient.mk _ (MvPolynomial.X none)) =
            IsLocalization.Away.invSelf g := by
  obtain ⟨h, hh⟩ := localized_presentation_is_relativeGlobalCompleteIntersection R n c f q hdim
  obtain ⟨e, hevars, henew⟩ := exists_localization_presentation R n c f h
  refine ⟨h, ?_⟩
  exact ⟨hh.1, hh.2.1, hh.2.2, ⟨e, hevars, henew⟩⟩

end Algebra
