/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement

/-! # Translation preserving a strictly standard witness

Source: Stacks Project, Tag 07CR, the change of generators in the opening paragraph.
(blueprint: lem-weil-pbc-popescu-translated-presentation-data).
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial

/-- Choose a strictly standard presentation whose generators vanish under the given section.

Source: Stacks Project, Tag 07CR, opening paragraph.
(blueprint: lem-weil-pbc-popescu-translated-presentation-data).

Proof: unpack strict standardness to obtain a presentation `P`, an integer `c`, minor
coefficients, and the ideal-square containment. For each generator choose a lift `bᵢ`
in `R` of its image under `ρ`. Let `τ` substitute `Xᵢ + C bᵢ` for `Xᵢ`; its inverse
substitutes `Xᵢ - C bᵢ`, since both composites fix constants and variables. The new
presentation has generator values `P.val i - algebraMap R A (b i)`, relations
`τ (P.relation j)`, and polynomial lift `τ ∘ P.σ`. Evaluation of a translated
polynomial at the new values equals the original evaluation, by equality on constants
and variables. Thus the new relations span the new evaluation kernel and the lift is
still a right inverse. The new generator values have zero image under `ρ`.
Polynomial induction, using additivity and the Leibniz rule, gives
`pderiv i (τ f) = τ (pderiv i f)`; hence evaluating each new Jacobian minor gives
exactly the old minor. Keep the old minor coefficients. Finally apply `τ` to the
ideal-square containment: an algebra automorphism preserves ideal spans, sums and
products, and the transported lift makes the left-hand side its image under `τ`.
This proves both strictly standard witness conditions for the same new presentation.
No constant-minor lifting or conclusion about an auxiliary algebra is used. -/
theorem exists_popescu_translated_presentation_data
    (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] [FinitePresentation R A] (π : R)
    (ρ : (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
      (R ⧸ Ideal.span {π ^ 4}))
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π)) :
    ∃ (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m)) (hc : c ≤ min n m)
      (b : {I : Finset (Fin n) // I.card = c} → A),
      (∀ i, ρ (Ideal.Quotient.mk _ (P.val i)) = 0) ∧
      algebraMap R A π = ∑ I : {I : Finset (Fin n) // I.card = c}, b I *
        Matrix.det (fun j i : Fin c =>
          aeval P.val (pderiv (I.val.orderEmbOfFin I.property i)
            (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j)))) ∧
      (∀ j : Fin m, c ≤ j.val →
        P.σ (algebraMap R A π) * P.relation j ∈
          Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
            (Ideal.span (Set.range P.relation)) ^ 2) := by
  classical
  obtain ⟨n, m, c, P, hc, b, hminor, hsq⟩ := hstandard
  have hr (i : Fin n) : ∃ r : R,
      Ideal.Quotient.mk (Ideal.span {π ^ 4}) r = ρ (Ideal.Quotient.mk _ (P.val i)) :=
    Ideal.Quotient.mk_surjective _
  choose r hr using hr
  let τplus : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval (fun i => X i + C (r i))
  let τminus : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval (fun i => X i - C (r i))
  have hplus : τplus.comp τminus = AlgHom.id R _ := by
    ext i
    simp [τplus, τminus]
  have hminus : τminus.comp τplus = AlgHom.id R _ := by
    ext i
    simp [τplus, τminus]
  let τ : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
    AlgEquiv.ofAlgHom τplus τminus hplus hminus
  let val : Fin n → A := fun i => P.val i - algebraMap R A (r i)
  have heval : (aeval val).comp τ.toAlgHom = aeval P.val := by
    ext i
    simp [τ, τplus, val]
  have heval_apply (f : MvPolynomial (Fin n) R) :
      aeval val (τ f) = aeval P.val f := DFunLike.congr_fun heval f
  have hspan : Ideal.span (Set.range (fun j => τ (P.relation j))) =
      RingHom.ker (aeval val) := by
    rw [show Set.range (fun j => τ (P.relation j)) =
      τ.toRingHom '' Set.range P.relation by
        exact Set.range_comp τ.toRingHom P.relation]
    rw [← Ideal.map_span, P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val]
    ext f
    rw [Ideal.mem_map_iff_of_surjective τ.toRingHom τ.surjective, RingHom.mem_ker]
    constructor
    · rintro ⟨g, hg, rfl⟩
      change aeval val (τ g) = 0
      rw [heval_apply]
      exact hg
    · intro hf
      refine ⟨τ.symm f, ?_, τ.apply_symm_apply f⟩
      rw [RingHom.mem_ker, ← heval_apply, τ.apply_symm_apply]
      exact hf
  let Q : Presentation R A (Fin n) (Fin m) :=
    { val := val
      σ' := fun a => τ (P.σ a)
      aeval_val_σ' := fun a => by rw [heval_apply, P.aeval_val_σ]
      relation := fun j => τ (P.relation j)
      span_range_relation_eq_ker := by
        simpa only [Generators.ker_eq_ker_aeval_val] using hspan }
  have hderiv (i : Fin n) (f : MvPolynomial (Fin n) R) :
      pderiv i (τ f) = τ (pderiv i f) := by
    induction f using MvPolynomial.induction_on with
    | C a => simp [τ, τplus]
    | add f g hf hg => simp [hf, hg]
    | mul_X f j hf =>
      simp only [map_mul, pderiv_mul, hf]
      have hX : τ (X j) = X j + C (r j) := by simp [τ, τplus]
      rw [hX]
      by_cases hji : j = i <;> simp [pderiv_X, hji, τ, τplus]
  refine ⟨n, m, c, Q, hc, b, ?_, ?_, ?_⟩
  · intro i
    change ρ (Ideal.Quotient.mk _ (P.val i - algebraMap R A (r i))) = 0
    rw [map_sub, map_sub]
    have hcomm : ρ (Ideal.Quotient.mk _ (algebraMap R A (r i))) =
        Ideal.Quotient.mk (Ideal.span {π ^ 4}) (r i) :=
      (ρ.comp (Ideal.Quotient.mkₐ R _)).commutes (r i)
    rw [hcomm, hr, sub_self]
  · convert hminor using 1
    apply Finset.sum_congr rfl
    intro I _
    congr 1
    congr 1
    ext j i
    change aeval val (pderiv _ (τ (P.relation _))) = _
    rw [hderiv, heval_apply]
  · intro j hj
    have h := Ideal.mem_map_of_mem τ.toRingHom (hsq j hj)
    have hinit : τ.toRingHom '' {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} =
        {f | ∃ k : Fin m, k.val < c ∧ f = Q.relation k} := by
      ext f
      constructor
      · rintro ⟨g, ⟨k, hk, rfl⟩, rfl⟩
        exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨P.relation k, ⟨k, hk, rfl⟩, rfl⟩
    have hrel : τ.toRingHom '' Set.range P.relation = Set.range Q.relation := by
      simp only [← Set.range_comp]
      rfl
    rw [Ideal.add_eq_sup, Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span,
      hinit, hrel] at h
    simpa [Q, Generators.σ, Ideal.add_eq_sup] using h


end Algebra
