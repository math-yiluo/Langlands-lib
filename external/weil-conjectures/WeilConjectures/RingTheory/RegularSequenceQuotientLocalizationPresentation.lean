/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Regular-sequence presentations of principal localizations

Source: Stacks Project, Algebra, proofs of Tags 07BV and 00SA
(blueprint: lem-weil-pbc-regular-sequence-quotient-localization-presentation).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

open MvPolynomial

private theorem exists_nested_presentation
    (k : Type u) [Field k] (n : ℕ) (f : List (MvPolynomial (Fin n) k))
    (hf : IsRegular (MvPolynomial (Fin n) k) f)
    [IsDomain (MvPolynomial (Fin n) k ⧸ Ideal.ofList f)]
    (g : MvPolynomial (Fin n) k ⧸ Ideal.ofList f) (hg : g ≠ 0) :
    ∃ q : List (MvPolynomial Unit (MvPolynomial (Fin n) k)),
      q.length = f.length + 1 ∧
      IsRegular (MvPolynomial Unit (MvPolynomial (Fin n) k)) q ∧
      Nonempty ((MvPolynomial Unit (MvPolynomial (Fin n) k) ⧸ Ideal.ofList q) ≃ₐ[k]
        Localization.Away g) := by
  let R := MvPolynomial (Fin n) k
  let I : Ideal R := Ideal.ofList f
  let A := R ⧸ I
  let S := MvPolynomial Unit R
  obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective g
  let t : S := C h * X () - 1
  let Q : Ideal S := I.map C
  let fs : List S := f.map C
  have hQ : Ideal.ofList fs = Q := (Ideal.map_ofList C f).symm
  let e0 : (S ⧸ Q) ≃ₐ[k] MvPolynomial Unit A :=
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Unit) I).symm.restrictScalars k
  have he0 : e0 (Ideal.Quotient.mk Q t) = C g * X () - 1 := by
    let μ : S →+* MvPolynomial Unit A := eval₂Hom (C.comp (Ideal.Quotient.mk I)) X
    change μ (C h * X () - 1) = _
    rw [map_sub μ, map_mul μ, map_one μ]
    have hC : μ (C h) = C g := by
      exact (eval₂Hom_C _ _ _).trans (congrArg C hh)
    have hX : μ (X ()) = X () := eval₂Hom_X' _ _ _
    rw [hC, hX]
  let J : Ideal S := Ideal.span {t}
  have he1 : Ideal.span {C g * X () - 1} =
      (J.map (Ideal.Quotient.mk Q)).map e0.toRingHom := by
    simp only [J, Ideal.map_span, Set.image_singleton]
    change Ideal.span {C g * X () - 1} = Ideal.span {e0 (Ideal.Quotient.mk Q t)}
    rw [he0]
  let e1 := Ideal.quotientEquivAlg (J.map (Ideal.Quotient.mk Q))
    (Ideal.span {C g * X () - 1}) e0 he1
  let e2 := IsLocalization.Away.mvPolynomialQuotientEquiv (Localization.Away g) g
  have hq : Ideal.ofList (fs ++ [t]) = Q ⊔ J := by
    rw [Ideal.ofList_append, hQ, Ideal.ofList_singleton]
  let e : (S ⧸ Ideal.ofList (fs ++ [t])) ≃ₐ[k] Localization.Away g :=
    (Ideal.quotientEquivAlgOfEq k hq).trans
      (((DoubleQuot.quotQuotEquivQuotSupₐ k Q J).symm.trans e1).trans
        (e2.restrictScalars k))
  have hweak : IsWeaklyRegular S fs := hf.toIsWeaklyRegular.of_flat
  have ht : IsSMulRegular (S ⧸ Q) (Ideal.Quotient.mk Q t) := by
    apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
    intro a ha
    apply e0.injective
    have H := congrArg e0 ha
    rw [smul_eq_mul, map_mul, map_zero, he0] at H
    exact (mul_eq_zero.mp H).resolve_left (by
      intro ht0
      have H := congrArg (constantCoeff (σ := Unit) (R := A)) ht0
      simp only [map_sub, map_mul, map_one, map_zero,
        constantCoeff_X, mul_zero, zero_sub, neg_eq_zero] at H
      exact one_ne_zero H)
  have htail : IsWeaklyRegular (S ⧸ (Ideal.ofList fs • ⊤ : Submodule S S)) [t] := by
    rw [hQ, Ideal.smul_eq_mul, Ideal.mul_top]
    rw [← isWeaklyRegular_map_algebraMap_iff (S ⧸ Q)]
    simpa [isWeaklyRegular_singleton_iff] using ht
  refine ⟨fs ++ [t], by simp [fs], ?_, ⟨e⟩⟩
  refine ⟨(isWeaklyRegular_append_iff S fs [t]).mpr ⟨hweak, htail⟩, ?_⟩
  have hne : Ideal.ofList (fs ++ [t]) ≠ ⊤ := by
    intro H
    have H' : (1 : S ⧸ Ideal.ofList (fs ++ [t])) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (H ▸ (by trivial : (1 : S) ∈ (⊤ : Ideal S)))
    have H'' := congrArg e H'
    simp only [map_one, map_zero] at H''
    have hinj := IsLocalization.injective (Localization.Away g)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
    exact one_ne_zero (hinj (by simpa only [map_one, map_zero] using H''))
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top, ne_eq, eq_comm] using hne


/-- A principal localization of a domain presented by a regular sequence has a
regular-sequence presentation with one extra variable and one extra equation.
Source: Stacks Project, Algebra, proof of Tag 07BV (lemma-colimit-syntomic),
and proof of Tag 00SA (lemma-localize-lci).
(blueprint: lem-weil-pbc-regular-sequence-quotient-localization-presentation).

Proof: Put R = k[X_1,...,X_n] and A = R/(f). Lift g to h in R. In R[T], use
f followed by hT - 1. Adjoining a polynomial variable is faithfully flat, so
f remains regular, and its quotient is A[T]. The image gT - 1 in that quotient
is nonzero (its constant coefficient is -1). Since A is a domain, A[T] is a
domain, so this last equation is a nonzerodivisor. Its quotient is A[1/g]:
send T to the inverse of g, and use the universal property in the reverse
direction. This localization is nonzero because A is a domain and g is nonzero.
Consequently the whole sequence is regular. Reindex the n old variables and
T by Fin (n + 1); the sequence has length f.length + 1. This also handles an
empty sequence f, and g = 1 gives A itself with a redundant variable T = 1. -/
theorem exists_localizationAway_presentation
    (k : Type u) [Field k] (n : ℕ) (f : List (MvPolynomial (Fin n) k))
    (hf : IsRegular (MvPolynomial (Fin n) k) f)
    [IsDomain (MvPolynomial (Fin n) k ⧸ Ideal.ofList f)]
    (g : MvPolynomial (Fin n) k ⧸ Ideal.ofList f) (hg : g ≠ 0) :
    ∃ q : List (MvPolynomial (Fin (n + 1)) k),
      q.length = f.length + 1 ∧
      IsRegular (MvPolynomial (Fin (n + 1)) k) q ∧
      Nonempty ((MvPolynomial (Fin (n + 1)) k ⧸ Ideal.ofList q) ≃ₐ[k]
        Localization.Away g) := by
  classical
  obtain ⟨q, hq, hreg, ⟨e⟩⟩ := exists_nested_presentation k n f hf g hg
  let ev : Unit ⊕ Fin n ≃ Fin (n + 1) := Fintype.equivOfCardEq (by simp [Nat.add_comm])
  let es : MvPolynomial Unit (MvPolynomial (Fin n) k) ≃ₐ[k]
      MvPolynomial (Fin (n + 1)) k :=
    (sumAlgEquiv k Unit (Fin n)).symm.trans (renameEquiv k ev)
  refine ⟨q.map es, by simpa using hq, ?_, ?_⟩
  · refine (es.toRingEquiv.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun r _ y ↦ es.map_mul r y
  · let eq := Ideal.quotientEquivAlg (Ideal.ofList q) (Ideal.ofList (q.map es)) es
      (Ideal.map_ofList es.toRingHom q).symm
    exact ⟨eq.symm.trans e⟩

end RingTheory.Sequence
