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
import WeilConjectures.RingTheory.PrincipalLocalizationCI

/-!
# Principal localization of a relative global complete intersection

Source: Stacks Project, Algebra, Lemma Tag 00SS, part (2)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-principal-localization).
-/

@[expose] public section

universe u

namespace Algebra

/-- If `T = R[x_1,…,x_n]/(f_1,…,f_c)` is a relative global complete intersection (for this
presentation), then for `h ∈ R[x_1,…,x_n]` with image `g ∈ T` the presentation
`T' = R[x_1,…,x_{n+1}]/(f_1,…,f_c,h x_{n+1} - 1)` (old variables `Fin.castSucc i`, new variable
`Fin.last n`, new equation appended with `Fin.snoc`) is a relative global complete intersection,
and the `R`-algebra map `T' → T_g` with `x_i ↦ x_i/1` and `x_{n+1} ↦ 1/g` is an isomorphism.
Source: Stacks Project, Algebra, Lemma Tag 00SS, part (2)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-principal-localization).

Proof: identify the enlarged quotient with the principal localization by the
polynomial quotient localization lemma.  Tensoring with residue fields identifies
its fibres with principal localizations of the original fibres.  The dimension
condition is preserved on the corresponding basic open, using equidimensionality
of the original complete-intersection fibres and invariance of local dimension on
open subspaces; hence the enlarged presentation has dimension `(n+1)-(c+1)`.
-/
theorem relativeGlobalCompleteIntersection_principalLocalization
    (R : Type u) [CommRing R] (n c : ℕ)
    (f : Fin c → MvPolynomial (Fin n) R)
    (hrel : IsRelativeGlobalCompleteIntersectionPresentation f)
    (h : MvPolynomial (Fin n) R) :
    IsRelativeGlobalCompleteIntersectionPresentation
        (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (n + 1)) R)
          (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
          (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last n) - 1)) ∧
      ∃ e :
          (MvPolynomial (Fin (n + 1)) R ⧸
              Ideal.span (Set.range
                (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (n + 1)) R)
                  (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
                  (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last n) - 1)))) ≃ₐ[R]
            Localization.Away
              (Ideal.Quotient.mk (Ideal.span (Set.range f)) h),
        (∀ i : Fin n,
          e (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.castSucc i))) =
            algebraMap
              (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
              (Localization.Away
                (Ideal.Quotient.mk (Ideal.span (Set.range f)) h))
              (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
        e (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.last n))) =
          IsLocalization.Away.invSelf
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) h) := by
  exact ⟨principalLocalization_ci R n c f hrel h, principalLocalization_algEquiv R n c f h⟩

end Algebra
