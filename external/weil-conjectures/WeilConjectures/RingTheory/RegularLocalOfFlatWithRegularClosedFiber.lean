/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Regularity along a flat local map with regular closed fibre

Source: Stacks Project, Algebra, Lemma 031E
(blueprint: lem-weil-pbc-flat-over-regular-with-regular-fibre).
-/

@[expose] public section

universe u v

namespace IsRegularLocalRing

/-- A flat local map of Noetherian local rings with regular source and regular closed fibre
has regular target. Source: Stacks Project, Algebra, Lemma 031E
(blueprint: lem-weil-pbc-flat-over-regular-with-regular-fibre).

Proof:
1. The regular closed-fibre hypothesis already supplies its local and Noetherian
   structures. Locality gives f⁻¹(m_S) = m_R and m_R S ⊆ m_S, and the surjective
   quotient map sends m_S to the closed fibre's maximal ideal.
2. Apply lem-weil-pbc-flat-height-formula (Stacks 00ON) directly at m_R and m_S.
   The height of a local ring's maximal ideal is its Krull dimension, giving
   dim S = dim R + dim(S/m_R S) without an explicit localization isomorphism.
3. Choose minimal finite generating sets for m_R and for the fibre's maximal ideal.
   Lift the latter to a finite set in m_S on which the quotient map is injective.
   The union of these lifts and the images of the base generators generates m_S:
   its quotient image agrees with that of m_S, and it contains the quotient kernel.
   Its cardinality is at most the sum of the two minimal generator counts.
4. Regularity identifies those counts with the two dimensions. The dimension formula
   and IsRegularLocalRing.of_spanFinrank_maximalIdeal_le give regularity of S.
   The finite-set argument also covers either generating set being empty. -/
theorem of_flat_of_regular_closedFiber
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f]
    (hflat : f.Flat)
    (hfibre : IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map f)) :
    IsRegularLocalRing S := by
  classical
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hflat
  have : IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map f) := hfibre
  have hlies : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap f).symm⟩
  have hdim := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)
  have hmap := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map f)) Ideal.Quotient.mk_surjective
  rw [show algebraMap R S = f from rfl, hmap] at hdim
  have hd : ringKrullDim S = ringKrullDim R +
      ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map f) := by
    simpa only [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, WithBot.coe_add]
      using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hdim
  obtain ⟨x, hxcard, hxspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  obtain ⟨y, hycard, hyspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (IsLocalRing.maximalIdeal (S ⧸ (IsLocalRing.maximalIdeal R).map f)).fg_of_isNoetherianRing
  change Ideal.span (x : Set R) = IsLocalRing.maximalIdeal R at hxspan
  change Ideal.span (y : Set (S ⧸ (IsLocalRing.maximalIdeal R).map f)) =
    IsLocalRing.maximalIdeal (S ⧸ (IsLocalRing.maximalIdeal R).map f) at hyspan
  let I := (IsLocalRing.maximalIdeal R).map f
  let q := Ideal.Quotient.mk I
  have hIM : I ≤ IsLocalRing.maximalIdeal S := IsLocalRing.map_maximalIdeal_le f
  have hsurj : Set.SurjOn q (IsLocalRing.maximalIdeal S) y := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hb : q b ∈ (IsLocalRing.maximalIdeal S).map q := by
      rw [hmap]
      exact hyspan ▸ Ideal.subset_span ha
    exact ⟨b, (Ideal.mem_quotient_iff_mem hIM).mp hb, rfl⟩
  obtain ⟨z, hzsub, hzinj, hzimage⟩ :=
    y.exists_subset_injOn_image_eq_of_surjOn (IsLocalRing.maximalIdeal S : Set S) hsurj
  let t := x.image f ∪ z
  have htspan : Ideal.span (t : Set S) = I ⊔ Ideal.span (z : Set S) := by
    simp only [t, Finset.coe_union, Finset.coe_image, Ideal.span_union, ← Ideal.map_span,
      hxspan, I]
  have hIt : I ≤ Ideal.span (t : Set S) := htspan ▸ le_sup_left
  have hqt : (Ideal.span (t : Set S)).map q = (IsLocalRing.maximalIdeal S).map q := by
    rw [htspan, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span]
    rw [← Finset.coe_image, hzimage, hyspan, hmap]
  have htM : Ideal.span (t : Set S) = IsLocalRing.maximalIdeal S := by
    have heq := (Ideal.map_eq_iff_sup_ker_eq_of_surjective q
      Ideal.Quotient.mk_surjective).mp hqt
    simpa only [q, Ideal.mk_ker, sup_eq_left.mpr hIt, sup_eq_left.mpr hIM] using heq
  have hgen : (IsLocalRing.maximalIdeal S).spanFinrank ≤
      (IsLocalRing.maximalIdeal R).spanFinrank +
        (IsLocalRing.maximalIdeal (S ⧸ I)).spanFinrank := by
    rw [← htM]
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite t.finite_toSet)
    rw [Set.ncard_coe_finset]
    calc
      t.card ≤ (x.image f).card + z.card := Finset.card_union_le _ _
      _ ≤ x.card + y.card := by
        apply Nat.add_le_add Finset.card_image_le
        rw [← hzimage, Finset.card_image_of_injOn hzinj]
      _ = _ := by rw [hxcard, hycard]
  apply of_spanFinrank_maximalIdeal_le
  rw [hd, ← spanFinrank_maximalIdeal (R := R),
    ← spanFinrank_maximalIdeal (R := S ⧸ I)]
  exact_mod_cast hgen

end IsRegularLocalRing
