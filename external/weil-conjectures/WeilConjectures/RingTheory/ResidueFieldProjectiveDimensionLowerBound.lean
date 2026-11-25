/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension

/-!
# Embedding dimension bounds the length of a residue-field resolution

Source: Stacks Project, Algebra, Lemma 00OA
(blueprint: lem-weil-pbc-residue-field-pd-ge-embedding-dimension).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- In a Noetherian local ring, every projective resolution of the residue field of length
at most `d` satisfies `dim (m/m²) ≤ d`. Source: Stacks Project, Algebra, Lemma 00OA
(blueprint: lem-weil-pbc-residue-field-pd-ge-embedding-dimension).

Proof:
1. Unpack the bounded projective resolution `P`. Mathlib's `P.extMk_surjective`
   represents every class in `Extⁱ(κ, Y)` by a map `Pᵢ → Y`. For `i > d`, the
   source is zero, so this map and its Ext class are zero. This gives Mathlib's
   `HasProjectiveDimensionLE κ d`.
2. Apply the source library's proved Serre theorem
   `IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField` to make `R` regular.
   Its proof uses induction on the number of generators of the maximal ideal,
   change of rings and the residue-field retract; it does not use this theorem.
3. The source library's `projectiveDimension_quotient_maximalIdeal` identifies
   the projective dimension of `R/m` with the minimal number of generators of `m`,
   using a regular sequence generating `m`. Transport along the canonical linear
   equivalence to the universe-shrunk quotient used by that theorem.
4. The minimal number of generators of `m` is `finrank κ (m/m²)` by Mathlib's
   `spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`. Rewrite the projective
   dimension bound and reflect the natural-number casts.

The two source-library results are in
`WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension`, Serre's theorem
(Stacks 00OC) and the regular-local residue-field dimension formula. -/
theorem finrank_cotangentSpace_le_of_hasProjectiveResolutionLE
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (d : ℕ)
    (h : ModuleCat.HasProjectiveResolutionLE (ModuleCat.of R (ResidueField R)) d) :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤ d := by
  obtain ⟨P, hP⟩ := h
  have hdim : CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of R (ResidueField R)) d := by
    refine CategoryTheory.HasProjectiveDimensionLT.mk ?_
    intro i hi Y e
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (i + 1) rfl
    have hf0 : f = 0 := (hP i (by omega)).eq_of_src f 0
    subst f
    simp
  have : IsRegularLocalRing R :=
    IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField d hdim
  have hle := (CategoryTheory.projectiveDimension_le_iff
    (ModuleCat.of R (ResidueField R)) d).mpr hdim
  let e : ResidueField R ≃ₗ[R] Shrink.{u} (R ⧸ maximalIdeal R) :=
    (Shrink.linearEquiv R _).symm
  rw [CategoryTheory.projectiveDimension_eq_of_iso e.toModuleIso,
    IsRegularLocalRing.projectiveDimension_quotient_maximalIdeal,
    spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at hle
  exact_mod_cast hle

end IsLocalRing
