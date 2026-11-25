/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.RingTheory.CohenRing

import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! # Full parameter coordinates over a Cohen ring

Source: Stacks Project, More on Algebra, Lemma Tag 07NM (3).
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace MvPowerSeries

/-- Parameters complementary to the coefficient uniformizer give Cohen coordinates.
Source: Stacks Project, More on Algebra, Lemma Tag 07NM (3).
(blueprint: lem-weil-pbc-power-series-full-coordinates-cohen)

Proof: Obtain completeness, domain structure, dimension n+1 and the maximal-ideal
presentation from `power_series_field_cohen_regular_complete`. Each entry of t lies
in the maximal ideal. Apply `exists_ringHom_of_isAdicComplete` to the coefficient
inclusion and these entries, obtaining a ring endomorphism f fixing constants and
sending the variables to t. It maps the maximal ideal onto itself: constants fix its
coefficient generator, while the images of variables are t. If the completeness
presentation uses a different prime p', the coefficient ideals (p') and (p) are equal
because both are the coefficient maximal ideal; map this equality along C.
Modulo the maximal ideal f is surjective, since any series is congruent to its constant
coefficient (the difference is in the variables ideal by `quotient_first_variables`).
Completeness and `surjective_of_mk_map_comp_surjective` give surjectivity of f.
A nonzero kernel element is a nonzero divisor in this domain, so
`ringKrullDim_succ_le_of_surjective` would give (n+1)+1 <= n+1. This is impossible.
Hence f is bijective. It fixes coefficients, so it gives a coefficient-algebra
equivalence. Rename the variables along hlen to obtain the displayed domain and
variable values. This also covers n=0, when the parameter system consists just of p.
No quotient or witness of an unproved existence theorem is used.
-/
theorem exists_algEquiv_full_parameters_cohen
    (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    (p n : ℕ) (hΛ : IsCohenRing p Λ) (t : List (MvPowerSeries (Fin n) Λ))
    (hparams : IsLocalRing.IsRegularSystemOfParameters (C (p : Λ) :: t))
    (hlen : t.length = n) :
    ∃ e : MvPowerSeries (Fin t.length) Λ ≃ₐ[Λ] MvPowerSeries (Fin n) Λ,
      ∀ i : Fin t.length, e (X i) = t.get i := by
  classical
  let S := MvPowerSeries (Fin n) Λ
  let v : Fin n → S := fun i ↦ t.get (Fin.cast hlen.symm i)
  have hdata := power_series_field_cohen_regular_complete
    (Λ := Λ) n (Or.inr ⟨p, hΛ⟩)
  rcases hdata with ⟨hf, _⟩ | ⟨p', hp', _, hdS, _, hm, _, _, hc, _, hd⟩
  · obtain ⟨_, _, hv, _⟩ := hΛ
    let := hv
    exact False.elim (IsDiscreteValuationRing.not_isField Λ hf)
  have : IsDomain S := hdS
  have : IsAdicComplete (IsLocalRing.maximalIdeal S) S := hc
  have ht (i : Fin n) : v i ∈ IsLocalRing.maximalIdeal S := by
    rw [← hparams.1]
    exact Ideal.subset_span (List.mem_cons_of_mem _ (List.get_mem _ _))
  obtain ⟨f, hfC, hfX, _⟩ := exists_ringHom_of_isAdicComplete
    (IsLocalRing.maximalIdeal S) (C : Λ →+* S) n v ht
  let I := IsLocalRing.maximalIdeal S
  have hrange : Set.range (f ∘ (X : Fin n → S)) = {a | a ∈ t} := by
    ext a
    simp only [Set.mem_range, Function.comp_apply, hfX, List.mem_iff_get]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fin.cast hlen.symm i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨Fin.cast hlen i, by simpa [v] using hi⟩
  have hmax : I = Ideal.span (insert (C (p : Λ)) {a | a ∈ t}) := by
    simpa only [List.mem_cons, Set.ofPred_or, Set.ofPred_eq_eq_singleton,
      Set.singleton_union] using hparams.1.symm
  have hmap : I.map f = I := by
    calc
      I.map f = (Ideal.span (insert (C (p' : Λ))
          (Set.range (X : Fin n → S)))).map f := by rw [← hm]
      _ = Ideal.span (insert (C (p' : Λ)) {a | a ∈ t}) := by
        rw [Ideal.map_span, Set.image_insert_eq, hfC, ← Set.range_comp, hrange]
      _ = I := by
        have hpeq : Ideal.span {(p' : Λ)} = Ideal.span {(p : Λ)} := by
          exact hp'.2.choose_spec.choose_spec.1.symm.trans hΛ.2.choose_spec.choose_spec.1
        have hcpeq : (Ideal.span {C (p' : Λ)} : Ideal S) = Ideal.span {C (p : Λ)} := by
          simpa only [Ideal.map_span, Set.image_singleton] using
            congrArg (Ideal.map (C : Λ →+* S)) hpeq
        rw [Ideal.span_insert, hcpeq, ← Ideal.span_insert, ← hmax]
  have : IsHausdorff (I.map f) S := hmap.symm ▸ inferInstance
  have hsurj : Function.Surjective f := by
    apply surjective_of_mk_map_comp_surjective (I := I)
    intro a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨C (constantCoeff g), ?_⟩
    change Ideal.Quotient.mk (I.map f) (f (C (constantCoeff g))) = _
    rw [hfC, Ideal.Quotient.mk_eq_mk_iff_sub_mem, hmap]
    have hvars : Ideal.span (Set.range (X : Fin n → S)) ≤ I := by
      rw [show I = _ from hm]
      exact Ideal.span_mono (Set.subset_insert _ _)
    apply hvars
    rw [← (quotient_first_variables Λ n n le_rfl).2.2.2.2.1]
    apply RingHom.mem_ker.mpr
    change constantCoeff (C (constantCoeff g) - g : MvPowerSeries (Fin n) Λ) = 0
    simp
  have hinj : Function.Injective f := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro g hg
    by_contra hne
    have hdim := ringKrullDim_succ_le_of_surjective f hsurj
      (mem_nonZeroDivisors_of_ne_zero hne) hg
    rw [hd] at hdim
    have hbad : n + 1 + 1 ≤ n + 1 := by exact_mod_cast hdim
    omega
  let e : S ≃ₐ[Λ] S :=
    AlgEquiv.ofBijective { __ := f, commutes' := hfC } ⟨hinj, hsurj⟩
  refine ⟨(renameEquiv Λ (finCongr hlen)).trans e, ?_⟩
  intro i
  change e (rename (finCongr hlen) (X i)) = _
  rw [rename_X]
  simpa [v, e] using hfX (finCongr hlen i)

end MvPowerSeries
