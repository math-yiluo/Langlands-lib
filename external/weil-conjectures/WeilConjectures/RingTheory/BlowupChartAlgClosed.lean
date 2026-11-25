/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Integral points over an algebraically closed residue field

Let `R` be a local ring with algebraically closed residue field `κ` and `ι : R → F` a map to a
field killing the maximal ideal. An element of `F` integral over `R` lies in the image of `ι`:
the field `κ(t)` is algebraic over `κ = κ̄`.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace BlowupChart

/-- Let `R` be a local ring with algebraically closed residue field and `ι : R → F` a ring map to a
field killing the maximal ideal. A root in `F` of a monic polynomial over `R` lies in the image
of `ι`. -/
theorem exists_eq_of_monic_eval₂_eq_zero {R F : Type*} [CommRing R] [IsLocalRing R]
    [IsAlgClosed (ResidueField R)] [Field F] (ι : R →+* F)
    (hι : ∀ r ∈ maximalIdeal R, ι r = 0) {q : R[X]} (hq : q.Monic) {t : F}
    (ht : q.eval₂ ι t = 0) : ∃ τ : R, ι τ = t := by
  let ι' : ResidueField R →+* F := Ideal.Quotient.lift (maximalIdeal R) ι hι
  have hcomp : ι'.comp (residue R) = ι :=
    RingHom.ext fun r => Ideal.Quotient.lift_mk (maximalIdeal R) ι hι
  let : Algebra (ResidueField R) F := ι'.toAlgebra
  have hint : IsIntegral (ResidueField R) t := by
    refine ⟨q.map (residue R), hq.map _, ?_⟩
    rw [eval₂_map]
    change eval₂ (ι'.comp (residue R)) t q = 0
    rw [hcomp]
    exact ht
  have hmon := minpoly.monic hint
  have hdeg : (minpoly (ResidueField R) t).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hint)
  have h := minpoly.aeval (ResidueField R) t
  rw [eq_X_add_C_of_degree_eq_one hdeg, hmon.leadingCoeff, C_1, one_mul, aeval_add, aeval_X,
    aeval_C, add_eq_zero_iff_eq_neg] at h
  obtain ⟨τ, hτ⟩ := residue_surjective (-(minpoly (ResidueField R) t).coeff 0)
  refine ⟨τ, ?_⟩
  rw [h, ← hcomp, RingHom.comp_apply, hτ, map_neg]
  rfl

/-- If `K` is infinite and `c : K → R` has injective residues, then for a nonzero polynomial `P`
over the residue field, `P(-c̄ i) ≠ 0` for some index `i`. -/
theorem exists_eval_neg_residue_ne_zero {R K : Type*} [CommRing R] [IsLocalRing R] [Infinite K]
    {c : K → R} (hc : Function.Injective (residue R ∘ c)) {P : (ResidueField R)[X]}
    (hP : P ≠ 0) : ∃ i, P.eval (-residue R (c i)) ≠ 0 := by
  classical
  by_contra! h
  have : Finite K := Finite.of_injective (β := P.roots.toFinset)
    (fun i => ⟨-residue R (c i), Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (h i))⟩)
    (fun i j hij => hc (neg_inj.mp (congrArg Subtype.val hij)))
  exact not_finite K

end BlowupChart
