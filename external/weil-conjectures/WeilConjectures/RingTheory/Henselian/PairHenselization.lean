/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The category of étale neighbourhoods of a pair

For a commutative ring `B` and an ideal `J ⊆ B`, we consider the full subcategory of commutative
`B`-algebras `D` such that `Spec D → Spec B` is étale and `B/J → D/JD` is bijective. These are
the étale neighbourhoods used to construct the henselization of the pair `(B, J)` (Stacks
`0A02`). We show that this category is essentially small: étale algebras are of finite type and
the category of finitely generated `B`-algebras is essentially small.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CommAlgCat

variable {B : Type u} [CommRing B]

/-- The property of a commutative `B`-algebra `D` to be an étale neighbourhood of the pair
`(B, J)`: `Spec D → Spec B` is étale and the canonical map `B/J → D/JD` is bijective. -/
def IsPairEtaleNeighborhood (J : Ideal B) : ObjectProperty (CommAlgCat.{u} B) := fun D ↦
  Etale (Spec.map (CommRingCat.ofHom (algebraMap B D))) ∧
    Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap B D)) (algebraMap B D) Ideal.le_comap_map)

lemma IsPairEtaleNeighborhood.algebraEtale {J : Ideal B} {D : CommAlgCat.{u} B}
    (hD : IsPairEtaleNeighborhood J D) : Algebra.Etale B D := by
  rw [← RingHom.etale_algebraMap]
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hD.1

lemma isPairEtaleNeighborhood_le_finiteType (J : Ideal B) :
    IsPairEtaleNeighborhood J ≤ fun D : CommAlgCat.{u} B ↦ Algebra.FiniteType B D := by
  intro D hD
  have := hD.algebraEtale
  infer_instance

/-- The full category of `B`-algebras `D` with `Spec D → Spec B` étale and `B/J → D/JD`
bijective, with all `B`-algebra maps as morphisms, is essentially small in the universe of `B`:
it embeds fully faithfully into the essentially small category of finitely generated
`B`-algebras. (blueprint: `lem-weil-pbc-pair-henselization-essentially-small`) -/
theorem essentiallySmall_isPairEtaleNeighborhood (J : Ideal B) :
    EssentiallySmall.{u} (IsPairEtaleNeighborhood J).FullSubcategory :=
  essentiallySmall_of_fully_faithful
    (ObjectProperty.ιOfLE (isPairEtaleNeighborhood_le_finiteType J))

end CommAlgCat
