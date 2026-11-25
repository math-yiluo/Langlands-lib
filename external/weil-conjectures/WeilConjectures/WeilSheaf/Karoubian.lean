/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import WeilConjectures.CategoryTheory.Idempotents.TStructure
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.WeilSheaf.VerdierDualFinite

/-!
# Weil complexes form an idempotent complete category

The standard t-structure of the derived category of pro-étale Weil sheaves induces a t-structure
on the Weil complexes (`AlgebraicGeometry.WeilComplex.tStructure`): the truncations of a bounded
complex whose cohomology objects are Weil sheaves are again such complexes. It is bounded, since
Weil complexes are bounded, so by the Karoubian bounded-t theorem
(`CategoryTheory.Triangulated.TStructure.isEquivalence_toKaroubi_and_isTriangulated_of_bounded`)
the category of Weil complexes is idempotent complete and its canonical functor into its Karoubi
envelope is an exact equivalence.

The category `AlgebraicGeometry.WeilComplex k₀ l Y` is directly the common-stage `ℚ̄_ℓ`-category
of the blueprint (see `WeilConjectures.WeilSheaf.Category`), so no passage to the colimit over the
finite coefficient fields `E` is needed: the argument the blueprint runs at each finite stage
applies to it as is.

## Main definitions

- `AlgebraicGeometry.WeilComplex.tStructure`: the standard t-structure on Weil complexes.

## Main statements

- `AlgebraicGeometry.WeilComplex.isIdempotentComplete`
- `AlgebraicGeometry.WeilComplex.isEquivalence_toKaroubi_and_isTriangulated`
-/

@[expose] public section

universe u

open CategoryTheory Limits Triangulated

namespace AlgebraicGeometry

namespace WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The standard t-structure on the Weil complexes is bounded. -/
lemma tStructure_bounded (K : WeilComplex k₀ l Y) : (tStructure k₀ l Y).bounded K := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  exact ⟨⟨a, (tStructure_isGE_iff K a).2 ha⟩,
    ⟨b, (tStructure_isLE_iff K b).2 hb⟩⟩

/-- Idempotent completeness of the common-stage Weil category

The triangulated category of Weil complexes on `Y` is idempotent complete: it carries the bounded
t-structure `AlgebraicGeometry.WeilComplex.tStructure`, whose heart is the abelian category of
Weil sheaves, and a triangulated category with a bounded t-structure is Karoubian. -/
instance isIdempotentComplete : IsIdempotentComplete (WeilComplex k₀ l Y) :=
  (tStructure k₀ l Y).isIdempotentComplete_of_bounded (tStructure_bounded k₀ l Y)

/-- Idempotent completeness of the common-stage Weil category

The canonical functor `D^b_{c,W}(Y, ℚ̄_ℓ) ⥤ Kar(D^b_{c,W}(Y, ℚ̄_ℓ))` from the Weil complexes on `Y`
into their Karoubi envelope is an exact equivalence: an equivalence of categories which is a
triangulated functor. -/
theorem isEquivalence_toKaroubi_and_isTriangulated :
    (Idempotents.toKaroubi (WeilComplex k₀ l Y)).IsEquivalence ∧
      (Idempotents.toKaroubi (WeilComplex k₀ l Y)).IsTriangulated :=
  (tStructure k₀ l Y).isEquivalence_toKaroubi_and_isTriangulated_of_bounded
    (tStructure_bounded k₀ l Y)

end WeilComplex

end AlgebraicGeometry
