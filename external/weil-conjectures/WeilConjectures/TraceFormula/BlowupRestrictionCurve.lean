/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TangentConeInitialForms
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.GluedStagesCharts
public import Mathlib.RingTheory.Nakayama

/-!
# The punctured curve `B - t` and its map to `T - D`

Let `T = Spec R` be a local scheme with closed point `t`, and `D = V(f)`, `B = V(g)` curves through
`t` with `V(f) ∩ V(g) = {t}` (for instance if their tangent cones meet only at the origin,
`IsLocalRing.TangentConesMeetAtOrigin.maximalIdeal_le_radical`). The punctured curve
`B - t = Spec (R/g) - {t}` then maps into `T - D = D(f)`; this is the restriction map of the
blowup restriction vanishing (blueprint `lemma-vanishing-restrictions-after-blowing-up--1`).

## Main definitions

- `AlgebraicGeometry.Scheme.puncturedSpec A`: the punctured spectrum of a local ring `A`.
- `AlgebraicGeometry.Scheme.puncturedCurveMap`: the map `B - t ⟶ T - D`.

## Main results

- `IsLocalRing.TangentConesMeetAtOrigin.maximalIdeal_le_radical`: `V(I) ∩ V(J) = {t}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- If the tangent cones of `V(I)` and `V(J)` meet only at the origin, then `V(I) ∩ V(J)` is the
closed point: `I + J` is `𝔪`-primary. -/
lemma TangentConesMeetAtOrigin.maximalIdeal_le_radical {I J : Ideal R}
    (hIJ : TangentConesMeetAtOrigin R I J) : maximalIdeal R ≤ (I ⊔ J).radical := by
  obtain ⟨N, hN⟩ := hIJ
  have hle : maximalIdeal R ^ N ≤ I ⊔ J := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R)
      (IsNoetherian.noetherian _) (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ?_
    refine (hN N le_rfl).trans (sup_le (sup_le ?_ ?_) ?_)
    · exact le_sup_of_le_left (inf_le_left.trans le_sup_left)
    · exact le_sup_of_le_left (inf_le_left.trans le_sup_right)
    · rw [pow_succ', smul_eq_mul]
      exact le_sup_right
  intro a ha
  exact ⟨N, hle (Ideal.pow_mem_pow ha N)⟩

end IsLocalRing

namespace AlgebraicGeometry.Scheme

/-- The punctured spectrum `Spec A - {𝔪}` of a local ring `A`. -/
noncomputable def puncturedSpec (A : Type u) [CommRing A] [IsLocalRing A] :
    (Spec (.of A)).Opens :=
  ⟨{IsLocalRing.closedPoint A}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint A).isOpen_compl⟩

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A quotient of a local ring by an element of the maximal ideal is local. -/
instance isLocalRing_quotient_span_singleton (g : R) [Fact (g ∈ maximalIdeal R)] :
    IsLocalRing (R ⧸ Ideal.span {g}) :=
  have : Nontrivial (R ⧸ Ideal.span {g}) := Ideal.Quotient.nontrivial_iff.2 fun h ↦
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ Ideal.span_le.2
      (Set.singleton_subset_iff.2 (Fact.out : g ∈ maximalIdeal R))))
  .of_surjective' _ Ideal.Quotient.mk_surjective

variable {f g : R} [Fact (g ∈ maximalIdeal R)]

/-- If `V(f) ∩ V(g)` is the closed point, the punctured curve `B - t = Spec (R/g) - {t}` maps into
`T - D = D(f)`. -/
lemma range_puncturedSpec_subset
    (hfg : maximalIdeal R ≤ (Ideal.span {f, g}).radical) :
    Set.range ((puncturedSpec (R ⧸ Ideal.span {g})).ι ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {g})))) ⊆
      Set.range (specBasicOpen (R := .of R) f).ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  set q : PrimeSpectrum R := PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {g})) p.val
    with hq
  change f ∉ q.asIdeal
  intro hf
  have hg : g ∈ q.asIdeal := by
    change Ideal.Quotient.mk (Ideal.span {g}) g ∈ p.val.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self g)]
    exact zero_mem _
  have hspan : Ideal.span {f, g} ≤ q.asIdeal := by
    rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hf, hg⟩
  have hm : maximalIdeal R ≤ q.asIdeal :=
    hfg.trans ((Ideal.radical_mono hspan).trans q.isPrime.radical.le)
  refine p.2 (show p.val = IsLocalRing.closedPoint _ from ?_)
  refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal p.val.isPrime.ne_top) ?_)
  intro a ha
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact hm ((mem_maximalIdeal r).2 fun hu ↦ ((mem_maximalIdeal _).1 ha) (hu.map _))

/-- The map `B - t ⟶ T - D` from the punctured curve `B = V(g)` to the complement of `D = V(f)`,
when `V(f) ∩ V(g)` is the closed point. -/
noncomputable def puncturedCurveMap
    (hfg : maximalIdeal R ≤ (Ideal.span {f, g}).radical) :
    (puncturedSpec (R ⧸ Ideal.span {g})).toScheme ⟶
      (specBasicOpen (R := .of R) f).toScheme :=
  IsOpenImmersion.lift _ _ (range_puncturedSpec_subset hfg)

end AlgebraicGeometry.Scheme
