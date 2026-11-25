/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters

import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! # Full parameter coordinates over a field

Source: Stacks Project, More on Algebra, Lemma Tag 07NM (1).
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace MvPowerSeries

/-- A full regular parameter system gives coordinates on field power series.
Source: Stacks Project, More on Algebra, Lemma Tag 07NM (1).
(blueprint: lem-weil-pbc-power-series-full-coordinates-field)

Proof: Obtain completeness, domain structure, dimension n and the variables' maximal
ideal from `power_series_field_cohen_regular_complete`. Each entry of t is in the
maximal ideal. Apply `exists_ringHom_of_isAdicComplete` to the coefficient inclusion
and the entries of t, giving a ring endomorphism f which fixes constants and carries
the standard variables to t. The image of the variables ideal is the maximal ideal
because t generates it. Modulo that ideal the map is surjective: every series is
congruent to its constant coefficient, by `quotient_first_variables`. The source is
complete for the variables ideal and the target separated for its image. Mathlib's
`surjective_of_mk_map_comp_surjective` gives surjectivity of f. A nonzero kernel element
in this domain would be a nonzero divisor, so
`ringKrullDim_succ_le_of_surjective` would give n+1 <= n, a contradiction. Thus f is
bijective. Its constant values make it a K-algebra map, giving an algebra equivalence.
Finally rename Fin t.length to Fin n using hlen and check the variable images.
The argument includes n=0 and the empty parameter system.
-/
theorem exists_algEquiv_full_parameters_field
    (K : Type u) [Field K] (n : ℕ) (t : List (MvPowerSeries (Fin n) K))
    (hparams : IsLocalRing.IsRegularSystemOfParameters t) (hlen : t.length = n) :
    ∃ e : MvPowerSeries (Fin t.length) K ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ i : Fin t.length, e (X i) = t.get i := by
  classical
  let S := MvPowerSeries (Fin n) K
  let v : Fin n → S := fun i ↦ t.get (Fin.cast hlen.symm i)
  have hdata := power_series_field_cohen_regular_complete
    (Λ := K) n (Or.inl (Field.toIsField K))
  rcases hdata with ⟨_, _, _, _, hm, _, _, hc, _, hd⟩ | ⟨p, hp, _⟩
  swap
  · obtain ⟨_, _, hv, _⟩ := hp
    let := hv
    exact False.elim (IsDiscreteValuationRing.not_isField K (Field.toIsField K))
  have : IsAdicComplete (IsLocalRing.maximalIdeal S) S := hc
  have ht (i : Fin n) : v i ∈ IsLocalRing.maximalIdeal S := by
    rw [← hparams.1]
    exact Ideal.subset_span (List.get_mem _ _)
  obtain ⟨f, hfC, hfX, _⟩ := exists_ringHom_of_isAdicComplete
    (IsLocalRing.maximalIdeal S) (C : K →+* S) n v ht
  let I : Ideal S := Ideal.span (Set.range (X : Fin n → S))
  have : IsAdicComplete I S := by simpa only [hm] using hc
  have hmap : I.map f = IsLocalRing.maximalIdeal S := by
    rw [Ideal.map_span, ← Set.range_comp]
    have heq : Set.range (f ∘ (X : Fin n → S)) = {a | a ∈ t} := by
      ext a
      simp only [Set.mem_range, Function.comp_apply, hfX,
        List.mem_iff_get]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨Fin.cast hlen.symm i, hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨Fin.cast hlen i, by simpa [v] using hi⟩
    rw [heq]
    exact hparams.1
  have : IsHausdorff (I.map f) S := hmap.symm ▸ inferInstance
  have hsurj : Function.Surjective f := by
    apply surjective_of_mk_map_comp_surjective (I := I)
    intro a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨C (constantCoeff g), ?_⟩
    change Ideal.Quotient.mk (I.map f) (f (C (constantCoeff g))) = _
    rw [hfC, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    rw [hmap, hm]
    rw [← (quotient_first_variables K n n le_rfl).2.2.2.2.1]
    apply RingHom.mem_ker.mpr
    change constantCoeff (C (constantCoeff g) - g : MvPowerSeries (Fin n) K) = 0
    simp
  have hinj : Function.Injective f := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro g hg
    by_contra hne
    have hdim := ringKrullDim_succ_le_of_surjective f hsurj
      (mem_nonZeroDivisors_of_ne_zero hne) hg
    rw [hd] at hdim
    have hbad : n + 1 ≤ n := by exact_mod_cast hdim
    omega
  let e : S ≃ₐ[K] S :=
    AlgEquiv.ofBijective { __ := f, commutes' := hfC } ⟨hinj, hsurj⟩
  refine ⟨(renameEquiv K (finCongr hlen)).trans e, ?_⟩
  intro i
  change e (rename (finCongr hlen) (X i)) = _
  rw [rename_X]
  simpa [v, e] using hfX (finCongr hlen i)

end MvPowerSeries
