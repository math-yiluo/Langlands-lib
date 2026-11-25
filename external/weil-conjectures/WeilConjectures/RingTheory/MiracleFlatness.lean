/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.IsRegularOfDimensionDrop
import WeilConjectures.RingTheory.FlatOverRegular

/-!
# Miracle flatness

Source: Stacks Project, Algebra, Lemma 10.128.1 (Tag 00R4)
(blueprint: lem-weil-pbc-miracle-flatness).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A local homomorphism from a regular Noetherian local ring to a Cohen–Macaulay
Noetherian local ring is flat when target dimension is source dimension plus closed
fibre dimension. The finite dimension `e` records Cohen–Macaulayness by the depth bound.
Source: Stacks Project, Algebra, Lemma 10.128.1 (Tag 00R4)
(blueprint: lem-weil-pbc-miracle-flatness).

Proof: choose a finite generating set of the source maximal ideal of minimum cardinality,
using Mathlib's span rank. Regularity identifies its cardinality with the source dimension.
List these generators as `x`. Since the homomorphism is local, the list `x.map φ` lies in
the target maximal ideal, and its generated ideal is the mapped source maximal ideal.
The assumed dimension formula therefore says that quotienting by this list drops the
target dimension by the length of the list. The Cohen–Macaulay dimension-drop criterion
(Stacks, Tag 00N6) shows that `x.map φ` is regular. Apply flatness over regular parameters
(Stacks, Tag 07DY). This route works also for an empty list and source dimension zero.
-/
theorem flat_of_regular_of_depth_ge {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ] (e : ℕ)
    (hdim : ringKrullDim S = (e : WithBot ℕ∞))
    (hdepth : (e : ℕ∞) ≤ IsLocalRing.depth (R := S) S)
    (hdim_add : ringKrullDim S =
      ringKrullDim R + ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map φ)) :
    φ.Flat := by
  classical
  obtain ⟨s, hs, hspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  let d := s.card
  let x := s.toList
  have hd : ringKrullDim R = (d : WithBot ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hs]
  have hx : x.length = d := by simp [x, d]
  have hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R := by
    simpa [x, Ideal.ofList] using hspan
  have hmap : Ideal.ofList (x.map φ) = (IsLocalRing.maximalIdeal R).map φ := by
    rw [← hgen, Ideal.map_ofList]
  have hmem : ∀ g ∈ x.map φ, g ∈ IsLocalRing.maximalIdeal S := by
    intro g hg
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
    exact map_nonunit φ r (hgen ▸ Ideal.subset_span hr)
  have hdrop : ringKrullDim (S ⧸ Ideal.ofList (x.map φ)) +
      ((x.map φ).length : WithBot ℕ∞) = (e : WithBot ℕ∞) := by
    rw [hmap, List.length_map, hx, ← hd, add_comm, ← hdim_add, hdim]
  have hreg := RingTheory.Sequence.isRegular_of_dimension_drop e hdim hdepth
    (x.map φ) hmem hdrop
  exact flat_of_regular_parameters φ d x hd hx hgen hreg

end RingHom
