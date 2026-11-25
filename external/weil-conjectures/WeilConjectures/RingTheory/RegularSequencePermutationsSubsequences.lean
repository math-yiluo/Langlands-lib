/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Data.List.OfFn

/-! Equivalence between permutation and subsequence regularity.
Source: Stacks Project, Algebra, Lemma 10.68.10, Tag 07DW.
(blueprint: lem-weil-pbc-regular-sequence-permutations-subsequences-proof).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence



private theorem weaklyRegular_swap_of_regular_elements
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {a b : R} (hab : IsWeaklyRegular M [a, b]) (hb : IsSMulRegular M b) :
    IsWeaklyRegular M [b, a] := by
  apply hab.prototype_perm (List.Perm.swap b a [])
  intro x y l hsub
  dsimp only
  intro _
  have hlen := hsub.length_le
  have hl : l = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
  subst l
  have hy : IsSMulRegular M y := by
    have hmem : y ∈ [a, b] := hsub.subset (by simp)
    rcases List.mem_cons.mp hmem with hya | hyb
    · subst y
      exact (isWeaklyRegular_cons_iff M a [b]).mp hab |>.1
    · have hyb : y = b := by simpa using hyb
      simpa only [hyb] using hb
  have heq : (Ideal.ofList ([] : List R) • (⊤ : Submodule R M)) = ⊥ := by simp
  have hy' := ((Submodule.quotEquivOfEqBot _ heq).isSMulRegular_congr y).mpr hy
  exact (isSMulRegular_iff_torsionBy_eq_bot _ _).mp hy'

private theorem weaklyRegular_sublists_perm
    {R : Type*} [CommRing R] {s t : List R} (hp : s.Perm t)
    {M : Type*} [AddCommGroup M] [Module R M]
    (h : ∀ l : List R, l.Sublist s → IsWeaklyRegular M l) :
    ∀ l : List R, l.Sublist t → IsWeaklyRegular M l := by
  induction hp generalizing M with
  | nil => exact h
  | @cons a s t hp ih =>
    intro l hl
    rcases List.sublist_cons_iff.mp hl with hskip | ⟨tail, rfl, htail⟩
    · exact ih (fun l hl ↦ h l (hl.cons a)) l hskip
    · apply IsWeaklyRegular.cons
      · exact (isWeaklyRegular_cons_iff M a []).mp
          (h [a] ((List.nil_sublist s).cons_cons a)) |>.1
      · apply ih (M := QuotSMulTop a M) ?_ tail htail
        intro l hl
        exact (isWeaklyRegular_cons_iff M a l).mp (h (a :: l) (hl.cons_cons a)) |>.2
  | swap a b s =>
    intro l hl
    rcases List.sublist_cons_iff.mp hl with hskip | ⟨tail, rfl, htail⟩
    · exact h l (hskip.trans (((List.Sublist.refl s).cons a).cons_cons b))
    · rcases List.sublist_cons_iff.mp htail with hskip | ⟨rest, rfl, hrest⟩
      · exact h (a :: tail) ((hskip.cons_cons a).cons b)
      · have hbal := h (b :: a :: rest) ((hrest.cons_cons a).cons_cons b)
        have ha := (isWeaklyRegular_cons_iff M a []).mp
          (h [a] (((List.nil_sublist s).cons_cons a).cons b)) |>.1
        have hparts := (isWeaklyRegular_append_iff M [b, a] rest).mp hbal
        apply (isWeaklyRegular_append_iff M [a, b] rest).mpr
        refine ⟨weaklyRegular_swap_of_regular_elements hparts.1 ha, ?_⟩
        have heq : Ideal.ofList [a, b] = Ideal.ofList [b, a] := by
          apply congrArg Ideal.span
          exact Set.ext fun x ↦ (List.Perm.swap b a []).mem_iff
        let e := Submodule.quotEquivOfEq _ _
          (congrArg (fun I : Ideal R ↦ I • (⊤ : Submodule R M)) heq)
        exact (e.isWeaklyRegular_congr rest).mpr hparts.2
  | trans hp₁ hp₂ ih₁ ih₂ => exact ih₂ (ih₁ h)

/-- Source: Stacks Project, Algebra, Lemma 10.68.10, Tag 07DW.
(blueprint: lem-weil-pbc-regular-sequence-permutations-subsequences-proof).
The equivalence is proved by induction on the length, using the two-element swap lemma.
-/
theorem isRegular_permutations_iff_subsequences
    {R : Type u} [CommRing R] (r : ℕ) (f : Fin r → R)
    (hproper : Ideal.ofList (List.ofFn f) ≠ ⊤) :
    (∀ l : List R, (List.ofFn f).Perm l → IsRegular R l) ↔
      (∀ l : List R, l.Sublist (List.ofFn f) → IsRegular R l) := by
  constructor
  · intro h l hl
    obtain ⟨tail, hp⟩ := hl.exists_perm_append
    have hr := h (l ++ tail) hp
    refine ⟨(isWeaklyRegular_append_iff R l tail).mp hr.toIsWeaklyRegular |>.1, ?_⟩
    intro heq
    apply hr.top_ne_smul
    rw [Ideal.ofList_append, Submodule.sup_smul, ← heq, top_sup_eq]
  · intro h l hp
    refine ⟨weaklyRegular_sublists_perm hp
      (fun l hl ↦ (h l hl).toIsWeaklyRegular) l (.refl l), ?_⟩
    have heq : Ideal.ofList l = Ideal.ofList (List.ofFn f) := by
      apply congrArg Ideal.span
      exact Set.ext fun x ↦ hp.mem_iff.symm
    change (⊤ : Ideal R) ≠ Ideal.ofList l • (⊤ : Ideal R)
    rw [Ideal.smul_eq_mul, Ideal.mul_top, heq]
    exact hproper.symm

end RingTheory.Sequence
