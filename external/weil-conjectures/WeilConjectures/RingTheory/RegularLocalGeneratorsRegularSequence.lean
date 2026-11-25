/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular systems of parameters and regular sequences

Source: Stacks Project, Algebra, Lemma 00NQ and Definition 00KU
(blueprint: lem-weil-pbc-regular-local-generators-regular-sequence).

## Main statements

* `IsRegularLocalRing.isRegular_and_quotients_of_generators`: regularity of a system of
  parameters, its initial quotients, and all its permutations.
* `IsRegularLocalRing.minimal_generators_iff_card_eq_dimension`: the parenthetical
  characterization of minimal generating sets in the node.
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

private theorem initial_quotients
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (rs : List R)
    (hrs : IsLocalRing.IsRegularSystemOfParameters rs) (c : ℕ) (hc : c ≤ d) :
    IsRegularLocalRing (R ⧸ Ideal.ofList (rs.take c)) ∧
      ringKrullDim (R ⧸ Ideal.ofList (rs.take c)) = ((d - c : ℕ) : WithBot ℕ∞) := by
  classical
  have hlen : rs.length = d := by exact_mod_cast hrs.2.trans hd
  let I := Ideal.ofList (rs.take c)
  have hI : I ≤ IsLocalRing.maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro x hx
    exact hrs.1 ▸ Ideal.subset_span (List.mem_of_mem_take hx)
  have hne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hI
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmap : IsLocalRing.maximalIdeal (R ⧸ I) =
      Ideal.ofList ((rs.drop c).map (Ideal.Quotient.mk I)) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective _
      (Ideal.Quotient.mk_surjective (I := I)), ← hrs.1]
    change (Ideal.ofList rs).map _ = _
    conv_lhs => rw [← List.take_append_drop c rs]
    rw [Ideal.ofList_append, Ideal.map_sup,
      Ideal.map_ofList, Ideal.map_ofList]
    have hzero : (rs.take c).map (Ideal.Quotient.mk I) =
        List.replicate (rs.take c).length 0 := by
      apply List.eq_replicate_iff.mpr
      refine ⟨by simp, ?_⟩
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hy)
    rw [hzero]
    have hz : Ideal.ofList (List.replicate (rs.take c).length (0 : R ⧸ I)) = ⊥ := by
      apply le_antisymm _ bot_le
      apply Ideal.span_le.mpr
      intro x hx
      have hx0 : x = 0 := (List.mem_replicate.mp hx).2
      simp [hx0]
    rw [hz, bot_sup_eq]
  have hemb : (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank ≤ d - c := by
    rw [hmap]
    have hb := Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ I)
      ((List.finite_toSet ((rs.drop c).map (Ideal.Quotient.mk I))))
    exact hb.trans (by simpa only [← List.coe_toFinset, Set.ncard_coe_finset,
      List.length_map, List.length_drop, hlen] using
      (List.toFinset_card_le ((rs.drop c).map (Ideal.Quotient.mk I))))
  have hupper : ringKrullDim (R ⧸ I) ≤ ((d - c : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ I)).trans (by exact_mod_cast hemb)
  have hlower : ringKrullDim R ≤ ringKrullDim (R ⧸ I) + (c : WithBot ℕ∞) := by
    have hb := ringKrullDim_le_ringKrullDim_quotient_add_card (rs.take c).toFinset (by
      intro x hx
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact hI (Ideal.subset_span (by simpa using hx)))
    have he : Ideal.span ((rs.take c).toFinset : Set R) = I := by
      apply congrArg Ideal.span
      ext x
      simp
    rw [he] at hb
    change ringKrullDim R ≤ ringKrullDim (R ⧸ I) + _ at hb
    have hcard : (rs.take c).toFinset.card ≤ c :=
      (List.toFinset_card_le _).trans (by simp)
    have hcast : ((rs.take c).toFinset.card : WithBot ℕ∞) ≤ (c : WithBot ℕ∞) := by
      exact_mod_cast hcard
    exact hb.trans (add_le_add le_rfl hcast)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp
    (ne_bot_of_le_ne_bot WithBot.coe_ne_bot
      (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ I)))
  have ha' : a ≤ (d - c : ℕ) := by
    rw [← ha] at hupper
    exact WithBot.coe_le_coe.mp hupper
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n :=
    ⟨a.toNat, (ENat.natCast_toNat
      (ne_top_of_le_ne_top (ENat.natCast_ne_top (d - c)) ha')).symm⟩
  have hn : ringKrullDim (R ⧸ I) = (n : WithBot ℕ∞) := ha.symm
  have hnle : n ≤ d - c := by rw [hn] at hupper; exact_mod_cast hupper
  have hdle : d ≤ n + c := by rw [hd, hn] at hlower; exact_mod_cast hlower
  have heq : n = d - c := by omega
  have hdim : ringKrullDim (R ⧸ I) = ((d - c : ℕ) : WithBot ℕ∞) := by rw [hn, heq]
  exact ⟨.of_spanFinrank_maximalIdeal_le _ (by rw [hdim]; exact_mod_cast hemb), hdim⟩

private theorem regular_sequence_core
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (rs : List R)
    (hrs : IsLocalRing.IsRegularSystemOfParameters rs) :
    RingTheory.Sequence.IsRegular R rs ∧
      (∀ c : ℕ, c ≤ d →
        IsRegularLocalRing (R ⧸ Ideal.ofList (rs.take c)) ∧
          ringKrullDim (R ⧸ Ideal.ofList (rs.take c)) = ((d - c : ℕ) : WithBot ℕ∞)) := by
  have hq := initial_quotients R d hd rs hrs
  refine ⟨?_, hq⟩
  have hlen : rs.length = d := by exact_mod_cast hrs.2.trans hd
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := R) (fun x hx => hrs.1 ▸ Ideal.subset_span hx)).mpr
  constructor
  intro i hi
  let I := Ideal.ofList (rs.take i)
  have hreg : IsRegularLocalRing (R ⧸ I) := (hq i (by omega)).1
  have hx : rs[i] ∉ I := by
    intro hx
    have he : Ideal.ofList (rs.take (i + 1)) = I := by
      rw [List.take_succ_eq_append_getElem hi, Ideal.ofList_append,
        Ideal.ofList_singleton]
      exact sup_eq_left.mpr (Ideal.span_le.mpr (by simpa using hx))
    have hdim := (hq (i + 1) (by omega)).2
    rw [he, (hq i (by omega)).2] at hdim
    have hn : d - i = d - (i + 1) := by exact_mod_cast hdim
    omega
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem I rs[i]).mpr
  intro x hxmul
  have hprod : Ideal.Quotient.mk I rs[i] * Ideal.Quotient.mk I x = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxmul
  have hxne : Ideal.Quotient.mk I rs[i] ≠ 0 :=
    fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((mul_eq_zero.mp hprod).resolve_left hxne)

/-- Stacks Project, Algebra, Lemma 00NQ and Definition 00KU
(blueprint: lem-weil-pbc-regular-local-generators-regular-sequence).
A regular system of parameters (`def-weil-pbc-regular-system-of-parameters`: `d` elements
generating the maximal ideal) is a regular sequence; its first `c` elements cut out a regular
local quotient of dimension `d - c`. Every permutation is again a regular system of parameters
and is regular.

Proof: for the ideal `I` generated by the first `c` parameters, its quotient is local and
Noetherian. Its maximal ideal is generated by the images of the remaining `d - c` parameters,
so its embedding dimension and Krull dimension are at most `d - c`. Krull's height theorem
also gives `d ≤ dim(R/I) + c`; hence its dimension is exactly `d - c`, and the quotient is
regular local by definition. This is the dimension-squeezing argument of Tag 00NQ applied to
all initial segments at once, using the multiple-equation form of Tag 00KW
(`lem-weil-pbc-noetherian-height-quotient-bound`). Each initial quotient is consequently a
domain (`lem-sc-regular-local-domain`). The next parameter has nonzero image in it, since
otherwise adjoining that parameter would not change the ideal, contradicting the strictly
smaller dimension of the next quotient. Multiplication by that image is injective, giving
weak regularity. As all parameters lie in the maximal ideal, Mathlib's local Nakayama
criterion upgrades this to regularity. A permutation preserves the span and length, and
Mathlib's permutation theorem preserves regularity. -/
theorem isRegular_and_quotients_of_generators
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (rs : List R)
    (hrs : IsLocalRing.IsRegularSystemOfParameters rs) :
    RingTheory.Sequence.IsRegular R rs ∧
      (∀ c : ℕ, c ≤ d →
        IsRegularLocalRing (R ⧸ Ideal.ofList (rs.take c)) ∧
          ringKrullDim (R ⧸ Ideal.ofList (rs.take c)) = ((d - c : ℕ) : WithBot ℕ∞)) ∧
      (∀ ys : List R, rs.Perm ys →
        IsLocalRing.IsRegularSystemOfParameters ys ∧ RingTheory.Sequence.IsRegular R ys) := by
  have hmain := regular_sequence_core R d hd rs hrs
  refine ⟨hmain.1, hmain.2, ?_⟩
  intro ys hys
  have hlen : ys.length = rs.length := hys.length_eq.symm
  have hspan : Ideal.span {x | x ∈ ys} = IsLocalRing.maximalIdeal R := by
    rw [← hrs.1]
    apply le_antisymm
    · exact Ideal.span_mono (by intro x hx; exact hys.mem_iff.2 hx)
    · exact Ideal.span_mono (by intro x hx; exact hys.mem_iff.1 hx)
  have hysrs : IsLocalRing.IsRegularSystemOfParameters ys :=
    ⟨hspan, by simpa [hlen] using hrs.2⟩
  exact ⟨hysrs, IsLocalRing.isRegular_of_perm hmain.1 hys⟩

/-- Stacks Project, Algebra, Definition 00KU and Lemma 00NQ
(blueprint: lem-weil-pbc-regular-local-generators-regular-sequence).
Among finite sets generating the maximal ideal of a regular local ring of dimension `d`,
the minimal ones are exactly those of cardinality `d`.

Proof: the dimension bound (`lem-weil-pbc-noetherian-local-dimension-le-generators`)
shows that a proper subset of a set of `d` generators cannot generate the maximal ideal.
Conversely, extract a linearly independent subset of the images of a minimal generating set
in the cotangent space, spanning the same cotangent space. Nakayama
(`lem-weil-pbc-nakayama-local-generators`) says that the lifted subset still generates the
maximal ideal, so minimality makes it the whole set. The cardinality of this cotangent basis
is the embedding dimension, which equals `d` by regularity. -/
theorem minimal_generators_iff_card_eq_dimension
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (s : Finset R)
    (hspan : Ideal.span (s : Set R) = IsLocalRing.maximalIdeal R) :
    (∀ t : Finset R, t ⊂ s → Ideal.span (t : Set R) ≠ IsLocalRing.maximalIdeal R) ↔
      s.card = d := by
  classical
  have hrank : (IsLocalRing.maximalIdeal R).spanFinrank = d := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hd] at h
    exact_mod_cast h
  have hbound (t : Finset R) (ht : Ideal.span (t : Set R) = IsLocalRing.maximalIdeal R) :
      d ≤ t.card := by
    rw [← hrank, ← ht]
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite t.finite_toSet
  constructor
  · intro hminimal
    let m := IsLocalRing.maximalIdeal R
    let t : Set m := {x | (x : R) ∈ s}
    have htfin : t.Finite := s.finite_toSet.preimage Subtype.val_injective.injOn
    have hvalt : Subtype.val '' t = (s : Set R) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        have hxm : x ∈ m := by
          change x ∈ IsLocalRing.maximalIdeal R
          rw [← hspan]
          exact Ideal.subset_span hx
        exact ⟨⟨x, hxm⟩, hx, rfl⟩
    have htspan : Submodule.span R t = ⊤ := by
      apply (Submodule.map_injective_of_injective
        (Submodule.injective_subtype m))
      rw [Submodule.map_top, Submodule.range_subtype, ← Submodule.span_image]
      change Ideal.span (Subtype.val '' t) = m
      rw [hvalt]
      exact hspan
    have hcot : Submodule.span (IsLocalRing.ResidueField R) (m.toCotangent '' t) = ⊤ :=
      IsLocalRing.CotangentSpace.span_image_eq_top_iff.mpr htspan
    obtain ⟨b, hbt, -, htb, hb⟩ := exists_linearIndepOn_extension
      (v := m.toCotangent) (linearIndepOn_empty (IsLocalRing.ResidueField R) _)
      (Set.empty_subset t)
    have hbfin : b.Finite := htfin.subset hbt
    have hbspan : Submodule.span (IsLocalRing.ResidueField R) (m.toCotangent '' b) = ⊤ := by
      rw [eq_top_iff, ← hcot]
      exact Submodule.span_le.mpr htb
    have hbrspan : Submodule.span R b = ⊤ :=
      IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hbspan
    let bs : Finset R := hbfin.toFinset.image Subtype.val
    have hbss : bs ⊆ s := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hbt (hbfin.mem_toFinset.mp hy)
    have hbs : Ideal.span (bs : Set R) = m := by
      change Ideal.span ((hbfin.toFinset.image Subtype.val : Finset R) : Set R) = m
      rw [Finset.coe_image, Set.Finite.coe_toFinset]
      change Submodule.span R (m.subtype '' b) = m
      rw [Submodule.span_image, hbrspan, Submodule.map_top, Submodule.range_subtype]
    have heq : bs = s := by
      by_contra hne
      exact hminimal bs (Finset.ssubset_iff_subset_ne.mpr ⟨hbss, hne⟩) hbs
    have hbcard : bs.card = m.spanFinrank := by
      change (hbfin.toFinset.image Subtype.val).card = m.spanFinrank
      rw [Finset.card_image_of_injective _ Subtype.val_injective,
        ← Set.ncard_eq_toFinset_card b hbfin,
        IsLocalRing.spanFinrank_maximalIdeal_eq_ncard hbfin hb hbspan]
    rw [← heq]
    exact hbcard.trans hrank
  · intro hcard t ht htspan
    have hlt := Finset.card_lt_card ht
    have hle := hbound t htspan
    omega

end IsRegularLocalRing
