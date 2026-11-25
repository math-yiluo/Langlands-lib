/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.StrictlyStandardElement
@[expose] public section
universe u v
/-- Every elementary standard element is strictly standard.
Source: Stacks Project, Smoothing Ring Maps, Definition Tag 07C7 and Lemma Tag 07F5.
(blueprint: lem-weil-pbc-elementary-to-strict)
Choose the coefficient of the initial Jacobian minor for the subset of its columns and
set all other coefficients to zero; transposing the minor matrix preserves its determinant,
and the relation condition is unchanged. -/
theorem elementary_standard_is_strict
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] {a : A}
    (ha : Algebra.IsElementaryStandardElement (R := R) a) :
    Algebra.IsStrictlyStandardElement (R := R) a := by
  classical
  obtain ⟨n, m, c, P, hc, b, hab, hrel⟩ := ha
  let e : Fin c ↪ Fin n := (Fin.castLEOrderEmb (le_trans hc (min_le_left n m))).toEmbedding
  let s : Finset (Fin n) := Finset.univ.map e
  have hs : s.card = c := by simp [s]
  let s₀ : {s : Finset (Fin n) // s.card = c} := ⟨s, hs⟩
  have he : (fun i : Fin c => Fin.castLE (le_trans hc (min_le_left n m)) i) =
      s.orderEmbOfFin hs := by
    apply Finset.orderEmbOfFin_unique hs
    · intro i
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · exact (Fin.castLEOrderEmb (le_trans hc (min_le_left n m))).strictMono
  refine ⟨n, m, c, P, hc, (fun t => if t = s₀ then b else 0), ?_, hrel⟩
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hab]
  congr 1
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, s₀]
  rw [← he]
