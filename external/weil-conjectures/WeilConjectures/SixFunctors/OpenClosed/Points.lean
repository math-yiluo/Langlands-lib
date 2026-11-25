/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Points of a scheme lie on an open or on its closed complement

Let `j : U ⟶ X` be an open immersion and `i : Z ⟶ X` a closed immersion whose range is the
complement of the range of `j`. This file shows that a point of `X` with values in a field
factors through `j` or through `i`, as an actual factorization of morphisms of schemes and not
merely as a statement about images.

This is the geometric input to the joint conservativity of `j^*` and `i^*` on the small étale
site: a geometric point of `X` is a point with values in a separably closed field, and joint
conservativity is proved by evaluating at such points, each of which lives on `U` or on `Z`.

## Main results

- `AlgebraicGeometry.existsUnique_fac_or_fac_of_range_eq_compl` — a morphism from the spectrum
  of a field to `X` factors uniquely through `j` or uniquely through `i`
  (blueprint: `lemma:openclosed-point-factors`).
- `AlgebraicGeometry.disjoint_range_of_range_eq_compl` — the two ranges of a complementary
  pair are disjoint. This is the half of the complementarity condition that the formal part
  of the argument uses.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A point of `X` with values in a field `K` lies either on the open `U` or on its closed
complement `Z`, as a factorization of morphisms of schemes: any `s : Spec K ⟶ X` is either of
the form `t ≫ j` for a unique `t : Spec K ⟶ U`, or of the form `t ≫ i` for a unique
`t : Spec K ⟶ Z`.

The open half is `AlgebraicGeometry.IsOpenImmersion.lift`, unique because an open immersion is
a monomorphism; the closed half is
`AlgebraicGeometry.IsClosedImmersion.existsUnique_fac_of_field`. What carries the closed half
is `AlgebraicGeometry.Scheme.IdealSheafData.le_ker_iff_range_subset_support`, whose hypothesis
on the source is `IsReduced (Spec K)`; the field hypothesis is used beyond that only for
`Subsingleton (Spec K)`, which upgrades "the closed point of `Spec K` lands in the range of
`i`" to "the whole range of `s` lands in the range of `i`".
(blueprint: `lemma:openclosed-point-factors`)
(blueprint: `lem-weil-pbc-geometric-point-open-or-closed`) -/
theorem existsUnique_fac_or_fac_of_range_eq_compl {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ X) :
    (∃! t : Spec (CommRingCat.of K) ⟶ U, t ≫ j = s) ∨
      (∃! t : Spec (CommRingCat.of K) ⟶ Z, t ≫ i = s) := by
  by_cases hs : s.base (IsLocalRing.closedPoint K) ∈ Set.range j.base
  · exact .inl ⟨IsOpenImmersion.lift j s (Scheme.range_base_subset_of_closedPoint_mem s hs),
      IsOpenImmersion.lift_fac _ _ _,
      fun t ht ↦ by rw [← cancel_mono j, ht, IsOpenImmersion.lift_fac]⟩
  · exact .inr (IsClosedImmersion.existsUnique_fac_of_field i s (hij ▸ hs))

/-- **The ranges of a complementary pair are disjoint.** This is the half of the
complementarity condition `Set.range i.base = (Set.range j.base)ᶜ` that the formal part of
the open--closed argument uses; the other half, that the two ranges cover `X`, enters only
through `AlgebraicGeometry.existsUnique_fac_or_fac_of_range_eq_compl`. -/
lemma disjoint_range_of_range_eq_compl {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    Disjoint (Set.range j.base) (Set.range i.base) := by
  rw [hij]
  exact disjoint_compl_right

end AlgebraicGeometry
