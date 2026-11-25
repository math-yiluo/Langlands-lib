/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation subrings and the domination order

Two consequences of the maximality of valuation subrings in the domination order of
local subrings (`ValuationSubring.isMax_toLocalSubring`, Stacks Project Tag 052K) and
of the Chevalley extension theorem (`LocalSubring.exists_le_valuationSubring`, Stacks
Project Tag 00IA):

- `ValuationSubring.comap_eq_of_toLocalSubring_le`: if a valuation subring `B` of a field
  extension `L` of `K` dominates the image of a valuation subring `A ⊆ K`, then
  `K ∩ B = A`, i.e. `B.comap f = A`;
- `ValuationSubring.exists_comap_eq`: every valuation subring `A ⊆ K` extends to a
  valuation subring `B` of any field extension `L` with `K ∩ B = A`.
-/

@[expose] public section

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L]

/-- **Intersection with a dominating valuation ring** (consequence of Stacks Project
Tag 052K): if a valuation subring `B` of a field extension `L` of `K` dominates a
valuation subring `A ⊆ K` — that is, `A ≤ B.comap f` in the domination order of local
subrings of `K` — then `K ∩ B = A`, i.e. `B.comap f = A`.
(Blueprint: `lemma:nagata-valuation-intersection`.) -/
@[stacks 052K]
theorem comap_eq_of_toLocalSubring_le {f : K →+* L} {A : ValuationSubring K}
    {B : ValuationSubring L} (h : A.toLocalSubring ≤ (B.comap f).toLocalSubring) :
    B.comap f = A :=
  ValuationSubring.toLocalSubring_injective (le_antisymm (A.isMax_toLocalSubring h) h)

/-- **Extension of a valuation ring to a field extension** (Stacks Project Tag 00IA):
for every field extension `f : K →+* L` and every valuation subring `A ⊆ K` there is a
valuation subring `B ⊆ L` with `K ∩ B = A`; its fraction field is `L`, as for every
valuation subring of `L`. -/
@[stacks 00IA]
theorem exists_comap_eq (f : K →+* L) (A : ValuationSubring K) :
    ∃ B : ValuationSubring L, B.comap f = A := by
  -- Chevalley extension applied to the image of `A` in `L`
  obtain ⟨B, hsub, hloc⟩ := (A.toLocalSubring.map f).exists_le_valuationSubring
  refine ⟨B, comap_eq_of_toLocalSubring_le
    ⟨fun x hx ↦ hsub (Subring.mem_map.mpr ⟨x, hx, rfl⟩), ⟨fun a ha ↦ ?_⟩⟩⟩
  -- `f` is injective, so `A` is isomorphic to its image, and domination transports
  -- unit-reflection back along that isomorphism
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  have hab : (a : K) * (b : K) = 1 := congrArg Subtype.val hb
  have hunit : IsUnit (Subring.inclusion hsub
      (A.toSubring.equivMapOfInjective f f.injective a)) :=
    isUnit_iff_exists_inv.mpr ⟨⟨f (b : K), b.2⟩, Subtype.ext (by
      simpa [Subring.coe_equivMapOfInjective_apply, ← map_mul] using congrArg f hab)⟩
  have hEa : IsUnit ((A.toSubring.equivMapOfInjective f f.injective).symm
      (A.toSubring.equivMapOfInjective f f.injective a)) :=
    (hloc.map_nonunit _ hunit).map _
  rwa [RingEquiv.symm_apply_apply] at hEa

end ValuationSubring
