/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Polynomial presentation of a principal localization

Source: Stacks Project, Algebra, Lemma 00ST (3), localization presentation in its proof.
-/

@[expose] public section

universe u

namespace Algebra

/-- Adjoining an inverse variable presents the principal localization, for any polynomial h.
Source: Stacks Project, Algebra, Lemma 00ST (3), and the universal property of localization.
(blueprint: new-equation-count-localize-presentation).

Proof: evaluate the old variables in S_g and the new variable at the inverse of g.
Every renamed f_i evaluates to zero, and h times the inverse evaluates to one, so this
map descends to the displayed quotient T. Conversely, the old variables define R[x] → T;
the f_i vanish, hence this descends to S → T. The image of g is a unit, with inverse the
class of the new variable, by the extra relation. The localization universal property
therefore gives S_g → T. The composites fix the old variables and the inverse variable;
polynomial induction and quotient surjectivity give the identity on T. The other composite
fixes S, hence is the identity by uniqueness for localization. These maps are R-algebra maps
and give the equivalence with the stated generator formulas. This also applies when g is
zero: both rings are then the zero ring. -/
theorem exists_localization_presentation
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (h : MvPolynomial (Fin n) R) :
      let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
      let g : S := Ideal.Quotient.mk _ h
      let relations : Option (Fin c) → MvPolynomial (Option (Fin n)) R :=
        Option.elim' (MvPolynomial.rename some h * MvPolynomial.X none - 1)
          (fun i ↦ MvPolynomial.rename some (f i))
      let T := MvPolynomial (Option (Fin n)) R ⧸ Ideal.span (Set.range relations)
      ∃ e : T ≃ₐ[R] Localization.Away g,
        (∀ i : Fin n,
          e (Ideal.Quotient.mk _ (MvPolynomial.X (some i))) =
            algebraMap S (Localization.Away g) (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
        e (Ideal.Quotient.mk _ (MvPolynomial.X none)) = IsLocalization.Away.invSelf g := by
  classical
  let I := Ideal.span (Set.range f)
  let S := MvPolynomial (Fin n) R ⧸ I
  let g : S := Ideal.Quotient.mk I h
  let L := Localization.Away g
  let relations : Option (Fin c) → MvPolynomial (Option (Fin n)) R :=
    Option.elim' (MvPolynomial.rename some h * MvPolynomial.X none - 1)
      (fun i ↦ MvPolynomial.rename some (f i))
  let J := Ideal.span (Set.range relations)
  let T := MvPolynomial (Option (Fin n)) R ⧸ J
  let old : MvPolynomial (Fin n) R →ₐ[R] L :=
    (Algebra.algHom R S L).comp (Ideal.Quotient.mkₐ R I)
  let ev : MvPolynomial (Option (Fin n)) R →ₐ[R] L :=
    MvPolynomial.aeval (Option.elim' (IsLocalization.Away.invSelf g)
      (fun i ↦ old (MvPolynomial.X i)))
  have ev_rename (p : MvPolynomial (Fin n) R) :
      ev (MvPolynomial.rename some p) = old p := by
    have he : ev.comp (MvPolynomial.rename some) = old := by
      ext i
      simp [ev]
    exact AlgHom.congr_fun he p
  have hev : ∀ p ∈ J, ev p = 0 := by
    have hker : J ≤ RingHom.ker ev.toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i, rfl⟩
      change ev (relations i) = 0
      cases i with
      | none =>
        simp only [relations, Option.elim'_none, map_sub, map_mul, map_one, ev_rename]
        simp only [ev, MvPolynomial.aeval_X, Option.elim'_none]
        change algebraMap S L g * IsLocalization.Away.invSelf g - 1 = 0
        rw [IsLocalization.Away.mul_invSelf, sub_self]
      | some i =>
        rw [show relations (some i) = MvPolynomial.rename some (f i) from rfl,
          ev_rename]
        have hf : Ideal.Quotient.mk I (f i) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
        change algebraMap S L (Ideal.Quotient.mk I (f i)) = 0
        rw [hf, map_zero]
    exact fun p hp ↦ hker hp
  let forward : T →ₐ[R] L := Ideal.Quotient.liftₐ J ev hev
  have forward_mk (p : MvPolynomial (Option (Fin n)) R) :
      forward (Ideal.Quotient.mk J p) = ev p := rfl
  let ren : MvPolynomial (Fin n) R →ₐ[R] T :=
    (Ideal.Quotient.mkₐ R J).comp (MvPolynomial.rename some)
  have hren : ∀ p ∈ I, ren p = 0 := by
    have hker : I ≤ RingHom.ker ren.toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i, rfl⟩
      change Ideal.Quotient.mk J (MvPolynomial.rename some (f i)) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span ⟨some i, rfl⟩
    exact fun p hp ↦ hker hp
  let base : S →ₐ[R] T := Ideal.Quotient.liftₐ I ren hren
  have base_mk (p : MvPolynomial (Fin n) R) :
      base (Ideal.Quotient.mk I p) = Ideal.Quotient.mk J (MvPolynomial.rename some p) := rfl
  have hmul : base g * Ideal.Quotient.mk J (MvPolynomial.X none) = 1 := by
    rw [base_mk, ← map_mul, ← map_one (Ideal.Quotient.mk J),
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span ⟨none, rfl⟩
  have hunit : IsUnit (base g) := isUnit_iff_exists_inv.mpr
    ⟨Ideal.Quotient.mk J (MvPolynomial.X none), hmul⟩
  let backward : L →ₐ[R] T := IsLocalization.Away.liftAlgHom g hunit
  have backward_base (s : S) : backward (algebraMap S L s) = base s := by
    exact IsLocalization.Away.lift_eq g hunit s
  have backward_inv : backward (IsLocalization.Away.invSelf g) =
      Ideal.Quotient.mk J (MvPolynomial.X none) := by
    apply hunit.mul_left_cancel
    rw [hmul]
    have hh := congrArg backward (IsLocalization.Away.mul_invSelf (S := L) g)
    simpa only [map_mul, map_one, backward_base] using hh
  have forward_base (s : S) : forward (base s) = algebraMap S L s := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [base_mk, forward_mk, ev_rename]
    rfl
  have hleft : backward.comp forward = AlgHom.id R T := by
    apply Ideal.Quotient.algHom_ext
    ext i
    cases i with
    | none =>
      change backward (forward (Ideal.Quotient.mk J (MvPolynomial.X none))) = _
      rw [forward_mk]
      simp only [ev, MvPolynomial.aeval_X, Option.elim'_none]
      exact backward_inv
    | some i =>
      change backward (forward (Ideal.Quotient.mk J (MvPolynomial.X (some i)))) = _
      rw [forward_mk]
      simp only [ev, MvPolynomial.aeval_X, Option.elim'_some]
      change backward (algebraMap S L (Ideal.Quotient.mk I (MvPolynomial.X i))) = _
      rw [backward_base, base_mk, MvPolynomial.rename_X]
      rfl
  have hright : forward.comp backward = AlgHom.id R L := by
    apply IsLocalization.algHom_ext (Submonoid.powers g)
    ext s
    change forward (backward (algebraMap S L s)) = algebraMap S L s
    rw [backward_base, forward_base]
  let e : T ≃ₐ[R] L := AlgEquiv.ofAlgHom forward backward hright hleft
  refine ⟨e, ?_, ?_⟩
  · intro i
    change forward (Ideal.Quotient.mk J (MvPolynomial.X (some i))) = _
    rw [forward_mk]
    simp only [ev, MvPolynomial.aeval_X, Option.elim'_some]
    rfl
  · change forward (Ideal.Quotient.mk J (MvPolynomial.X none)) = _
    rw [forward_mk]
    simp only [ev, MvPolynomial.aeval_X, Option.elim'_none]
    rfl

end Algebra
