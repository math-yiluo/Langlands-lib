/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CoefficientResidueSection
import WeilConjectures.RingTheory.CohenRingLiftToCompleteLocal
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Power series presentations of complete local rings

Source: Stacks Project, Algebra, Theorem 032A, part (2) and its proof
(blueprint: lem-weil-pbc-cohen-structure-power-series-surjection).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A complete local ring with finitely generated maximal ideal is a quotient of a power series
ring over a characteristic-zero field or a Cohen ring of the residue characteristic.
Source: Stacks Project, Algebra, Theorem 032A, part (2) and the final paragraph of its proof
(blueprint: lem-weil-pbc-cohen-structure-power-series-surjection).

Proof:
1. Choose a finite family `y : Fin n → R` spanning the maximal ideal, using its finite
   generation. Each `y i` lies in that ideal, including the empty family when it is zero.
2. In characteristic zero use `exists_residue_section` to obtain a map from the residue
   field into `R` splitting reduction. The residue field is a characteristic-zero field.
3. In prime characteristic use `exists_cohenRing` and `exists_cohenRing_lift` to obtain
   a Cohen ring and a map into `R` lifting its prescribed residue isomorphism. Its composite
   with reduction is surjective. These existing lemmas supply the compatible lifts and limit
   of the second paragraph of the source proof.
4. For either coefficient map apply `MvPowerSeries.exists_ringHom_of_isAdicComplete`
   to obtain `φ` sending constants to their coefficient images and `X i` to `y i`.
5. Let `I` be the ideal spanned by the variables. Mathlib makes the source `I`-adically
   complete. Mapping the ideal's generators shows `I.map φ = maximalIdeal R`, so the target
   is Hausdorff for this mapped ideal. The composite of `φ` with reduction modulo `I.map φ`
   is surjective: lift a residue by a coefficient and use its constant series. Apply
   `surjective_of_mk_map_comp_surjective` (Stacks 0315 successive approximation). This gives
   surjectivity without the finite-module detour through Stacks 031D. -/
theorem cohen_structure_power_series_surjection
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hfg : (maximalIdeal R).FG) [IsAdicComplete (maximalIdeal R) R]
    (p : ℕ) [CharP (ResidueField R) p] :
    ∃ (n : ℕ) (Λ : Type u) (_ : CommRing Λ),
      (p = 0 → IsField Λ ∧ CharZero Λ) ∧
      (0 < p → IsCohenRing p Λ) ∧
      ∃ φ : MvPowerSeries (Fin n) Λ →+* R, Function.Surjective φ := by
  classical
  obtain ⟨n, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hymem (i : Fin n) : y i ∈ maximalIdeal R := by
    rw [← hy]
    exact Submodule.subset_span ⟨i, rfl⟩
  have presentation (Λ : Type u) [CommRing Λ] (α : Λ →+* R)
      (hα : Function.Surjective ((residue R).comp α)) :
      ∃ φ : MvPowerSeries (Fin n) Λ →+* R, Function.Surjective φ := by
    obtain ⟨φ, hC, hX, _⟩ := MvPowerSeries.exists_ringHom_of_isAdicComplete
      (maximalIdeal R) α n y hymem
    let I : Ideal (MvPowerSeries (Fin n) Λ) := Ideal.span (Set.range MvPowerSeries.X)
    have hmap : I.map φ = maximalIdeal R := by
      rw [Ideal.map_span, ← Set.range_comp]
      simpa only [Function.comp_def, hX] using hy
    have : IsHausdorff (I.map φ) R := hmap.symm ▸ inferInstance
    refine ⟨φ, surjective_of_mk_map_comp_surjective (I := I) φ ?_⟩
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hα (residue R r)
    refine ⟨MvPowerSeries.C a, ?_⟩
    change Ideal.Quotient.mk (I.map φ) (φ (MvPowerSeries.C a)) = _
    rw [hC]
    change Ideal.Quotient.mk (maximalIdeal R) (α a) =
      Ideal.Quotient.mk (maximalIdeal R) r at ha
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha ⊢
    simpa only [hmap] using ha
  rcases CharP.char_is_prime_or_zero (ResidueField R) p with hp | hp
  · obtain ⟨Λ, hcomm, hΛ, ⟨e⟩⟩ := exists_cohenRing p hp (ResidueField R)
    let _ := hcomm
    obtain ⟨α, hα⟩ := exists_cohenRing_lift R p Λ hΛ e
    refine ⟨n, Λ, hcomm, ?_, fun _ ↦ hΛ, presentation Λ α ?_⟩
    · intro hzero
      exact False.elim (hp.ne_zero hzero)
    · rw [hα]
      exact e.surjective.comp Ideal.Quotient.mk_surjective
  · subst p
    have : CharZero (ResidueField R) := CharP.charP_to_charZero (ResidueField R)
    obtain ⟨α, hα⟩ := exists_residue_section R
    refine ⟨n, ResidueField R, inferInstance, fun _ ↦ ⟨Field.toIsField _, inferInstance⟩,
      ?_, presentation (ResidueField R) α ?_⟩
    · intro hpos
      exact False.elim (Nat.lt_irrefl 0 hpos)
    · rw [hα]
      exact Function.surjective_id

end IsLocalRing
