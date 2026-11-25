/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.DirectSum.Module

/-!
# One-step approximation from homogeneous initial-ideal generators

Source: Stacks Project, Algebra, Lemma 05GH, proof, second and third paragraphs
(blueprint: lem-weil-pbc-associated-graded-ideal-approximation).
-/

@[expose] public section

universe u
open scoped BigOperators

namespace Ideal

private noncomputable def initialForm {A : Type u} [CommRing A]
    (J : Ideal A) (n : ℕ) (x : A) (hx : x ∈ J ^ n) : associatedGraded J :=
  DirectSum.of (fun k : ℕ ↦ associatedGradedPiece J k) n
    (Submodule.Quotient.mk (⟨x, hx⟩ : (J ^ n : Ideal A)))

/-- Choose finite initial forms directly from the generating set. This avoids
constructing a homogeneous ideal and then homogenizing its generators. -/
private theorem finite_initial_forms {A : Type u} [CommRing A]
    (J K : Ideal A) [IsNoetherianRing (associatedGraded J)] :
    ∃ (t : ℕ) (d : Fin t → ℕ) (h : Fin t → A)
      (_hhK : ∀ i, h i ∈ K) (hhJ : ∀ i, h i ∈ J ^ (d i)),
      ∀ (n : ℕ) (x : A) (_hxK : x ∈ K) (hxJ : x ∈ J ^ n),
        ∃ q : Fin t → associatedGraded J,
          initialForm J n x hxJ =
            ∑ i, q i * initialForm J (d i) (h i) (hhJ i) := by
  classical
  let T := Σ n : ℕ, {x : A // x ∈ K ∧ x ∈ J ^ n}
  let v : T → associatedGraded J :=
    fun z ↦ initialForm J z.1 z.2.1 z.2.2.2
  have hfg : (Ideal.span (Set.range v)).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨F, hF, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := associatedGraded J)
      (Set.range v)).mp hfg
  have hlift : ∀ z : F, ∃ w : T, v w = z.1 := fun z ↦ hF z.2
  choose lift hlift using hlift
  let t := Fintype.card F
  let e : Fin t ≃ F := (Fintype.equivFin F).symm
  let w : Fin t → T := fun i ↦ lift (e i)
  have hrange : Set.range (fun i ↦ v (w i)) = (F : Set (associatedGraded J)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      change v (lift (e i)) ∈ F
      rw [hlift]
      exact (e i).2
    · intro hz
      refine ⟨e.symm ⟨z, hz⟩, ?_⟩
      change v (lift (e (e.symm ⟨z, hz⟩))) = z
      rw [e.apply_symm_apply, hlift]
  refine ⟨t, fun i ↦ (w i).1, fun i ↦ (w i).2.1,
    fun i ↦ (w i).2.2.1, fun i ↦ (w i).2.2.2, ?_⟩
  intro n x hxK hxJ
  have hmem : initialForm J n x hxJ ∈
      Submodule.span (associatedGraded J) (Set.range (fun i ↦ v (w i))) := by
    rw [hrange, ← hspan]
    exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨n, ⟨x, hxK, hxJ⟩⟩, rfl⟩)
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  refine ⟨q, ?_⟩
  simpa only [smul_eq_mul] using hq.symm

/-- Multiplication by a homogeneous initial form contributes to degree n
through an actual coefficient in J^(n-d). -/
private theorem product_component_coefficient {A : Type u} [CommRing A]
    (J : Ideal A) (q : associatedGraded J) (d : ℕ) (h : A)
    (hh : h ∈ J ^ d) (n : ℕ) :
    ∃ a : A, a ∈ J ^ (n - d) ∧ ∃ hah : a * h ∈ J ^ n,
      (q * initialForm J d h hh) n =
        (Submodule.Quotient.mk (⟨a * h, hah⟩ : (J ^ n : Ideal A)) :
          associatedGradedPiece J n) := by
  classical
  induction q using DirectSum.induction_on with
  | zero =>
      refine ⟨0, by simp, by simp, ?_⟩
      simp only [zero_mul, DFinsupp.zero_apply]
      change (0 : associatedGradedPiece J n) =
        Submodule.Quotient.mk (0 : (J ^ n : Ideal A))
      exact (Submodule.Quotient.mk_zero _).symm
  | add q r ihq ihr =>
      obtain ⟨a, ha, hah, heqa⟩ := ihq
      obtain ⟨b, hb, hbh, heqb⟩ := ihr
      have habh : (a + b) * h ∈ J ^ n := by
        rw [add_mul]
        exact (J ^ n).add_mem hah hbh
      refine ⟨a + b, (J ^ (n - d)).add_mem ha hb, habh, ?_⟩
      rw [add_mul, DFinsupp.add_apply, heqa, heqb, ← Submodule.Quotient.mk_add]
      congr 1
      apply Subtype.ext
      exact (add_mul a b h).symm
  | of k y =>
      induction y using Submodule.Quotient.induction_on with
      | _ a =>
          by_cases hkn : k + d = n
          · subst n
            have hah : a.1 * h ∈ J ^ (k + d) := by
              simpa [pow_add] using Ideal.mul_mem_mul a.2 hh
            refine ⟨a.1, by simpa only [Nat.add_sub_cancel] using a.2, hah, ?_⟩
            change (initialForm J k a.1 a.2 * initialForm J d h hh) (k + d) = _
            rw [initialForm, initialForm, associatedGraded_mul]
            exact DirectSum.of_eq_same _ _
          · refine ⟨0, by simp, by simp, ?_⟩
            change (initialForm J k a.1 a.2 * initialForm J d h hh) n = _
            rw [initialForm, initialForm, associatedGraded_mul]
            rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hkn)]
            simp only [zero_mul]
            change (0 : associatedGradedPiece J n) =
              Submodule.Quotient.mk (0 : (J ^ n : Ideal A))
            exact (Submodule.Quotient.mk_zero _).symm

/-- Homogeneous initial forms give finite one-step ideal approximation data.
Source: Stacks Project, Tag 05GH, proof, second and third paragraphs.
(blueprint: lem-weil-pbc-associated-graded-ideal-approximation)

Proof: Take the ideal spanned by all initial forms of elements of K in J^n.
Noetherianity and finite-subset extraction choose finitely many of these very
initial forms, with degrees d and representatives h in K intersect J^d.
Express each initial form of x in their span. Degree-n projection of a product
with the degree-d initial form of h is represented by a*h with a in J^(n-d):
prove this by direct-sum induction, lifting each homogeneous coefficient to
its ideal-power representative. Applying projection to the finite-sum equality
makes x minus the resulting sum zero modulo J^(n+1). It also lies in K since
x and every h do. This argument does not require completeness of the ring. -/
theorem exists_associatedGraded_ideal_approximation {A : Type u} [CommRing A]
    (J K : Ideal A) [IsNoetherianRing (associatedGraded J)] :
    ∃ (t : ℕ) (d : Fin t → ℕ) (h : Fin t → A),
      (∀ i, h i ∈ K) ∧ (∀ i, h i ∈ J ^ (d i)) ∧
      ∀ (n : ℕ) (x : A), x ∈ K → x ∈ J ^ n →
        ∃ a : Fin t → A, (∀ i, a i ∈ J ^ (n - d i)) ∧
          x - ∑ i, a i * h i ∈ K ∧ x - ∑ i, a i * h i ∈ J ^ (n + 1) := by
  classical
  obtain ⟨t, d, h, hhK, hhJ, hforms⟩ := finite_initial_forms J K
  refine ⟨t, d, h, hhK, hhJ, ?_⟩
  intro n x hxK hxJ
  obtain ⟨q, hq⟩ := hforms n x hxK hxJ
  have hc (i : Fin t) := product_component_coefficient J (q i) (d i) (h i) (hhJ i) n
  choose a ha hah hea using hc
  refine ⟨a, ha, ?_, ?_⟩
  · exact K.sub_mem hxK (Submodule.sum_mem _ fun i _ => K.mul_mem_left _ (hhK i))
  · let y : (J ^ n : Ideal A) := ∑ i, (⟨a i * h i, hah i⟩ : (J ^ n : Ideal A))
    have hsum : (Submodule.Quotient.mk y : associatedGradedPiece J n) =
        ∑ i, (Submodule.Quotient.mk (⟨a i * h i, hah i⟩ : (J ^ n : Ideal A)) :
          associatedGradedPiece J n) :=
      map_sum (Submodule.comap (J ^ n).subtype (J ^ (n + 1))).mkQ _ _
    have Hn := congrArg
      (DirectSum.component A ℕ (fun k ↦ associatedGradedPiece J k) n) hq
    rw [map_sum] at Hn
    change (initialForm J n x hxJ) n = ∑ i, (q i * initialForm J (d i) (h i) (hhJ i)) n
      at Hn
    rw [initialForm, DirectSum.of_eq_same] at Hn
    simp only [hea] at Hn
    have heq : (Submodule.Quotient.mk (⟨x, hxJ⟩ : (J ^ n : Ideal A)) :
        associatedGradedPiece J n) = Submodule.Quotient.mk y := Hn.trans hsum.symm
    have hmem := (Submodule.Quotient.eq _).mp heq
    change x - y.1 ∈ J ^ (n + 1) at hmem
    simpa [y] using hmem

end Ideal
