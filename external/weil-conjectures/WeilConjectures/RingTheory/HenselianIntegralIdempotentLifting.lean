/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.Algebra.Group.Idempotent
import WeilConjectures.RingTheory.EtaleSectionLiftingOfGabberRoots
import WeilConjectures.RingTheory.HenselianOfEtaleSectionLifting

/-!
# Idempotent lifting in integral algebras over henselian pairs

Source: Stacks Project, More on Algebra, Lemma 15.11.6 (Tag 09XI), (3) ⇒ (4)
(blueprint: lem-weil-pbc-henselian-pair-integral-idempotent-lifting).
-/

@[expose] public section

universe u v

namespace Algebra

private theorem finite_idempotent_lifting
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
    (e₀ : B ⧸ I.map (algebraMap A B)) (he₀ : IsIdempotentElem e₀) :
    ∃! e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap A B)) e = e₀ := by
  -- Simple-root lifting gives Gabber's root condition at the residue class of 1.
  have hroots : ∀ (n : ℕ), 1 ≤ n → ∀ (a : Fin (n + 1) → A),
      (∀ j, a j ∈ I) → ∀ (f : Polynomial A), f.Monic →
        f = (Polynomial.X ^ n * (Polynomial.X - 1) +
          Finset.univ.sum (fun j : Fin (n + 1) ↦ Polynomial.C (a j) * Polynomial.X ^ (j : ℕ))) →
          ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α := by
    intro n _hn a ha f hf hform
    have hmap : f.map (Ideal.Quotient.mk I) =
        Polynomial.X ^ n * (Polynomial.X - 1) := by
      rw [hform]
      simp [Polynomial.map_sum, Ideal.Quotient.eq_zero_iff_mem.mpr (ha _)]
    have hmem : f.eval 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval_map_apply]
      simp [hmap]
    have hunit : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
      rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hmap]
      simp
    obtain ⟨α, hα, hdiff⟩ := HenselianRing.is_henselian f hf 1 hmem hunit
    exact ⟨α, hdiff, hα⟩
  have hsections : ∀ (A' : Type (max u v)) [CommRing A'] [Algebra A A']
      [Etale A A'] (σ : A' →ₐ[A] A ⧸ I),
      ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ := by
    intro A' _ _ _ σ
    exact exists_etale_section_lift_of_gabber_roots A I HenselianRing.jac hroots A' σ
  exact (henselianRing_of_etale_section_lifting A I hsections).2.2 B e₀ he₀

private theorem finite_subalgebra_mem_map
    (A : Type u) [CommRing A] (I : Ideal A)
    (C : Type v) [CommRing C] [Algebra A C]
    {z : C} (hz : z ∈ I.map (algebraMap A C)) :
    ∃ (S : Subalgebra A C) (_ : S.FG) (z' : S),
      (z' : C) = z ∧ z' ∈ I.map (algebraMap A S) := by
  classical
  -- Induction records the finitely many coefficients needed to witness ideal membership.
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨⊥, ⟨∅, by simp⟩, algebraMap A (⊥ : Subalgebra A C) a,
      rfl, Ideal.mem_map_of_mem _ ha⟩
  | zero =>
    exact ⟨⊥, ⟨∅, by simp⟩, 0, rfl, Ideal.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨S, hS, x', rfl, hx'⟩ := ihx
    obtain ⟨T, hT, y', rfl, hy'⟩ := ihy
    let jS := Subalgebra.inclusion (show S ≤ S ⊔ T from le_sup_left)
    let jT := Subalgebra.inclusion (show T ≤ S ⊔ T from le_sup_right)
    have hmS : (I.map (algebraMap A S)).map jS.toRingHom =
        I.map (algebraMap A ↥(S ⊔ T)) := by
      rw [Ideal.map_map]
      rfl
    have hmT : (I.map (algebraMap A T)).map jT.toRingHom =
        I.map (algebraMap A ↥(S ⊔ T)) := by
      rw [Ideal.map_map]
      rfl
    refine ⟨S ⊔ T, hS.sup hT, jS x' + jT y', rfl, Ideal.add_mem _ ?_ ?_⟩
    · rw [← hmS]
      exact Ideal.mem_map_of_mem _ hx'
    · rw [← hmT]
      exact Ideal.mem_map_of_mem _ hy'
  | smul c x hx ih =>
    obtain ⟨S, hS, x', rfl, hx'⟩ := ih
    let T := S ⊔ Algebra.adjoin A {c}
    let j := Subalgebra.inclusion (show S ≤ T from le_sup_left)
    let c' : T := ⟨c, (show Algebra.adjoin A {c} ≤ T from le_sup_right)
      (Algebra.subset_adjoin (by simp))⟩
    have hm : (I.map (algebraMap A S)).map j.toRingHom =
        I.map (algebraMap A T) := by
      rw [Ideal.map_map]
      rfl
    refine ⟨T, hS.sup (by simpa using Subalgebra.fg_adjoin_finset (R := A) {c}), c' * j x', rfl, ?_⟩
    apply Ideal.mul_mem_left
    rw [← hm]
    exact Ideal.mem_map_of_mem _ hx'

private theorem finite_subalgebra_for_congruence
    (A : Type u) [CommRing A] (I : Ideal A)
    (C : Type v) [CommRing C] [Algebra A C]
    (s : Finset C) {z : C} (hz : z ∈ I.map (algebraMap A C)) :
    ∃ (S : Subalgebra A C) (_ : S.FG),
      (↑s : Set C) ⊆ S ∧ ∃ z' : S, (z' : C) = z ∧ z' ∈ I.map (algebraMap A S) := by
  obtain ⟨T, hT, z', hz', hmem⟩ := finite_subalgebra_mem_map A I C hz
  let S := T ⊔ Algebra.adjoin A (↑s : Set C)
  let j := Subalgebra.inclusion (show T ≤ S from le_sup_left)
  have hm : (I.map (algebraMap A T)).map j.toRingHom =
      I.map (algebraMap A S) := by
    rw [Ideal.map_map]
    rfl
  refine ⟨S, hT.sup (Subalgebra.fg_adjoin_finset s), ?_, j z', hz', ?_⟩
  · intro x hx
    exact (show Algebra.adjoin A (↑s : Set C) ≤ S from le_sup_right)
      (Algebra.subset_adjoin hx)
  · rw [← hm]
    exact Ideal.mem_map_of_mem _ hmem

private theorem finite_of_fg_subalgebra
    (A : Type u) [CommRing A] (C : Type v) [CommRing C] [Algebra A C]
    [Algebra.IsIntegral A C] (S : Subalgebra A C) (hS : S.FG) : Module.Finite A S := by
  obtain ⟨s, hs, rfl⟩ := Subalgebra.fg_def.mp hS
  exact Algebra.finite_adjoin_of_finite_of_isIntegral hs
    (fun x _ ↦ Algebra.IsIntegral.isIntegral x)

private theorem map_extended_ideal_subtype
    (A : Type u) [CommRing A] (C : Type v) [CommRing C] [Algebra A C]
    (I : Ideal A) (S : Subalgebra A C) {z : S}
    (hz : z ∈ I.map (algebraMap A S)) : (z : C) ∈ I.map (algebraMap A C) := by
  have hm : (I.map (algebraMap A S)).map S.val.toRingHom =
      I.map (algebraMap A C) := by
    rw [Ideal.map_map]
    rfl
  rw [← hm]
  exact Ideal.mem_map_of_mem _ hz

/-- For an integral algebra `C` over a henselian pair `(A, I)`, each idempotent modulo
`IC` lifts uniquely to an idempotent of `C`. Here `IC` is the extension of `I` along
`algebraMap A C`. The henselian hypothesis is the predicate recorded by
`def-weil-pbc-henselian-terminology`, equivalent to the finite-algebra idempotent criterion.
Source: Stacks Project, More on Algebra, Lemma 15.11.6 (Tag 09XI), (3) ⇒ (4)
(blueprint: lem-weil-pbc-henselian-pair-integral-idempotent-lifting).

Proof (the node's direct reduction to finite subalgebras):
1. An `A`-subalgebra `C'` generated by finitely many elements of `C` is module-finite:
its generators satisfy the same monic equations in the subring, and
`lem-weil-pbc-finite-of-integral-generators` applies. The inclusion sends `IC'` into `IC`.
If an element of `C'` is a sum of terms `φ(i) y` with `i ∈ I` and all `y ∈ C'`, the sum
is computed inside `C'`, so the element lies in `IC'` by injectivity of the inclusion.
2. Lift a quotient idempotent to `c ∈ C`. Write `c² - c` as a finite sum `Σ φ(iₖ)yₖ`.
Take `C'` generated by `c` and all witnesses `yₖ`. Step 1 makes it finite and ensures
`c² - c ∈ IC'`. By the finite-algebra criterion of
`def-weil-pbc-henselian-terminology` (Stacks 09XI), the class of `c` in `C'/IC'` lifts
to an idempotent `e'`. Its image in `C` is an idempotent congruent to `c` modulo `IC`.
3. If idempotents `e, f ∈ C` have the same quotient image, write `e - f = Σ φ(iₖ)yₖ`.
Take `C'` generated by `e`, `f` and all witnesses. Step 1 gives a finite algebra with
`e - f ∈ IC'`. Uniqueness in the same finite-algebra criterion gives `e = f` in `C'`,
hence in `C`. Thus the quotient map on idempotents is both surjective and injective. -/
theorem existsUnique_isIdempotentElem_of_henselianRing
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (C : Type v) [CommRing C] [Algebra A C] [Algebra.IsIntegral A C]
    (e₀ : C ⧸ I.map (algebraMap A C)) (he₀ : IsIdempotentElem e₀) :
    ∃! e : C, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap A C)) e = e₀ := by
  classical
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective e₀
  have hmem : c * c - c ∈ I.map (algebraMap A C) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, he₀.eq, sub_self]
  obtain ⟨S, hS, hs, z, hz, hzmem⟩ :=
    finite_subalgebra_for_congruence A I C {c} hmem
  let c' : S := ⟨c, hs (by simp)⟩
  have hz' : z = c' * c' - c' := Subtype.ext hz
  have hc' : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A S)) c') := by
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
    exact hz' ▸ hzmem
  let := finite_of_fg_subalgebra A C S hS
  obtain ⟨e', he', _⟩ := finite_idempotent_lifting A I S _ hc'
  have he : IsIdempotentElem (e' : C) := by
    exact congr_arg Subtype.val he'.1.eq
  have hec : Ideal.Quotient.mk (I.map (algebraMap A C)) (e' : C) =
      Ideal.Quotient.mk _ c := by
    rw [Ideal.Quotient.eq]
    exact map_extended_ideal_subtype A C I S (Ideal.Quotient.eq.mp he'.2)
  refine ⟨(e' : C), ⟨he, hec⟩, ?_⟩
  intro f hf
  have hfe : f - (e' : C) ∈ I.map (algebraMap A C) :=
    Ideal.Quotient.eq.mp (hf.2.trans hec.symm)
  obtain ⟨T, hT, ht, w, hw, hwmem⟩ :=
    finite_subalgebra_for_congruence A I C {f, (e' : C)} hfe
  let f' : T := ⟨f, ht (by simp)⟩
  let e'' : T := ⟨(e' : C), ht (by simp)⟩
  have hf' : IsIdempotentElem f' := Subtype.ext hf.1.eq
  have he'' : IsIdempotentElem e'' := Subtype.ext he.eq
  have hw' : w = f' - e'' := Subtype.ext hw
  have hquot : Ideal.Quotient.mk (I.map (algebraMap A T)) f' =
      Ideal.Quotient.mk _ e'' := Ideal.Quotient.eq.mpr (hw' ▸ hwmem)
  have hequot : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A T)) e'') := by
    rw [IsIdempotentElem, ← map_mul, he''.eq]
  let := finite_of_fg_subalgebra A C T hT
  obtain ⟨g, hg, huniq⟩ := finite_idempotent_lifting A I T _ hequot
  have hfg : f' = g := huniq f' ⟨hf', hquot⟩
  have heg : e'' = g := huniq e'' ⟨he'', rfl⟩
  exact congr_arg Subtype.val (hfg.trans heg.symm)

end Algebra
