/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionBaseChange
import WeilConjectures.RingTheory.PolynomialLocalClosedFiberEquiv
import WeilConjectures.RingTheory.GlobalCompleteIntersectionLocalRegularSequence

/-! # Regularity of complete-intersection equations in the polynomial closed fibre

Source: Stacks Project, Algebra, Tag 00SV, first paragraph of the proof, using 00SC.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Algebra

private theorem fieldCase
    {k : Type u} [Field k] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) k)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime]
    (hQ : Ideal.span (Set.range f) ≤ Q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime Q)
      ((List.ofFn f).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime Q))) := by
  let S := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)
  have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top inferInstance) hQ)
  let p : Ideal k := ⊥
  let e : p.Fiber S ≃ₐ[k] S :=
    (Algebra.TensorProduct.congr p.algEquivResidueFieldOfField.symm
      (AlgEquiv.refl : S ≃ₐ[k] S)).trans (Algebra.TensorProduct.lid k S)
  have : Nontrivial (p.Fiber S) := e.toEquiv.nontrivial
  obtain ⟨hc, hd⟩ := h p inferInstance
  have hdim : topologicalKrullDim (PrimeSpectrum S) = (n - c : ℕ) := by
    let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
    exact (IsHomeomorph.topologicalKrullDim_eq H H.isHomeomorph).symm.trans hd
  apply MvPolynomial.isRegular_localizationAtPrime_of_quotient_dimension k n c f
    _ Q hQ
  change topologicalKrullDim (PrimeSpectrum S) + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)
  rw [hdim]
  norm_cast
  exact Nat.sub_add_cancel hc

/-- The equations are regular in the closed fibre of the polynomial local map, before
lifting regularity to the polynomial local ring itself.
Source: Stacks Project, Algebra, Tag 00SV, first paragraph of the proof, using 00SC.
(blueprint: lem-weil-pbc-relative-ci-closed-fiber-regular-sequence).

Proof: Put `P = R[x]` and contract `Q` to `p` in `R`. The fibre-prime correspondence
provides a prime of `κ(p) ⊗[R] P` contracting to `Q`. Polynomial scalar extension
identifies this fibre ring with `κ(p)[x]`, taking each equation to its coefficientwise
residue-field image. The corresponding prime contains these images, so the quotient
by their ideal is nonzero. Base change (00SS) preserves the specified relative complete
intersection, and its only nonempty fibre over the field `κ(p)` has dimension `n-c`,
with `c ≤ n`. Equivalently its dimension plus `c` is `n`. Apply the field-case theorem
00SC to obtain regularity at the corresponding polynomial fibre prime. The natural
fibre-local-ring isomorphism (0H9M) identifies this ring with the closed fibre of the
map `R_p → P_Q`. Indeed the extended maximal ideal of `R_p` equals the extension of
`p`, since the denominators in `R \ p` become units. The isomorphism carries each
closed-fibre equation to the equation used in 00SC; transport regularity through it.
For no equations the fibre local ring is still nonzero; if the original quotient is
zero no prime containing all equations exists. No Noetherian hypothesis is needed for
this identification and field-case argument.
-/
theorem isRegular_closedFiber_of_relativeCompleteIntersection
    {R : Type u} [CommRing R] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime]
    (hQ : Ideal.span (Set.range f) ≤ Q) :
    let p := Q.comap (algebraMap R (MvPolynomial (Fin n) R))
    let φ := Localization.localRingHom p Q (algebraMap R (MvPolynomial (Fin n) R)) rfl
    let I := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map φ
    RingTheory.Sequence.IsRegular (Localization.AtPrime Q ⧸ I)
      (((List.ofFn f).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))).map
          (Ideal.Quotient.mk I))  := by
  classical
  let p := Q.comap (algebraMap R (MvPolynomial (Fin n) R))
  let φ := Localization.localRingHom p Q (algebraMap R (MvPolynomial (Fin n) R)) rfl
  let I := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map φ
  let g : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) p.ResidueField :=
    MvPolynomial.map (algebraMap R p.ResidueField)
  let fk := fun i ↦ g (f i)
  obtain ⟨Qk, hQk, hcontract, e, he⟩ :=
    MvPolynomial.exists_polynomial_local_closedFiber_equiv n Q
  have hk : IsRelativeGlobalCompleteIntersectionPresentation fk :=
    (relativeGlobalCompleteIntersection_baseChange R p.ResidueField n c f).2 h
  have hspan : Ideal.span (Set.range fk) ≤ Qk := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f i ∈ Qk.comap g
    rw [hcontract]
    exact hQ (Ideal.subset_span ⟨i, rfl⟩)
  have hreg := fieldCase fk hk Qk hspan
  have hlist : List.Forall₂
      (fun (r : Localization.AtPrime Q ⧸ I) (s : Localization.AtPrime Qk) ↦
        ∀ x, e (r • x) = s • e x)
      (((List.ofFn f).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))).map
          (Ideal.Quotient.mk I))
      ((List.ofFn fk).map
        (algebraMap (MvPolynomial (Fin n) p.ResidueField) (Localization.AtPrime Qk))) := by
    rw [show List.ofFn fk = (List.ofFn f).map g by
      simp only [List.map_ofFn, Function.comp_def, fk]]
    simp only [List.map_map]
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro a _ x
    simp only [smul_eq_mul, map_mul, Function.comp_def]
    rw [he]
  exact (e.toAddEquiv.isRegular_congr hlist).mpr hreg

end Algebra
