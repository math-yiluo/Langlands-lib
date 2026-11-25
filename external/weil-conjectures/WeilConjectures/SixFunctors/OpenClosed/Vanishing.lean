/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement

/-!
# `j^* i_*` and `i^* j_!` vanish for morphisms with disjoint ranges

Let `j : U ⟶ X` be an open immersion and let `i : Z ⟶ X` be an **arbitrary** morphism whose
range is disjoint from the range of `j`. This file proves that the extension by zero along `j`
and the pushforward along `i` see nothing of each other's side:

- `j^* i_* H` vanishes for every sheaf `H` on the small étale site of `Z`;
- `i^* j_! G` vanishes for every sheaf `G` on the small étale site of `U`.

In the intended application `i` is a closed immersion complementary to `j`, and these two
vanishings are what makes the two ends of the exact sequence `0 → j_! j^* F → F → i_* i^* F → 0`
disjoint: the composite `j_! j^* F → F → i_* i^* F` is zero because already
`Hom(j_! j^* F, i_* i^* F) ≅ Hom(j^* F, j^* i_* i^* F)` is a singleton. Neither statement needs
`i` to be a closed immersion, and the general form is what the rest of the argument uses.

## The argument

Both statements are the ones of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement`, where the second morphism
was an open immersion too, and neither proof used that:

- For `T` étale over `U`, the fibre product `T ×_X Z` is empty, because the ranges of `j` and
  `i` are disjoint (`AlgebraicGeometry.Scheme.Etale.isEmpty_left_pullback_map`, resting on
  `AlgebraicGeometry.Scheme.isEmpty_pullback`, which describes the points of a fibre product of
  schemes without any hypothesis on the two morphisms). Since `(i_* H)(T) = H(T ×_X Z)` and a
  sheaf has terminal sections over an empty scheme, all sections of `j^* i_* H` are terminal,
  hence zero.
- `i^* j_! G` is treated through Hom-sets rather than through sections, `j_!` being a
  sheafification: the two adjunctions `i^* ⊣ i_*` and `j_! ⊣ j^*` give
  `Hom(i^* j_! G, H) ≃ Hom(j_! G, i_* H) ≃ Hom(G, j^* i_* H)`, a singleton by the first point.
  So `i^* j_! G` is initial, hence a zero object.

## Main results

- `AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range`: `j^* i_* H = 0`.
- `AlgebraicGeometry.Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range`:
  `i^* j_! G = 0`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

section Vanishing

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]

open Etale

omit [HasSmallSiteSheafify A] in
/-- Blueprint `lemma-openclosed-vanishing-lowerstar`: **`j^* i_* H` vanishes** when the ranges
of `j` and `i` are disjoint. Its sections over
`T : U.Etale` are `H(T ×_X Z) = H(∅)`, hence terminal, hence zero. This is
`AlgebraicGeometry.Etale.isZero_openImmersionRestriction_lowerStar` transported along
`AlgebraicGeometry.Etale.upperStarIsoOpenImmersionRestriction`. -/
lemma Etale.isZero_upperStar_lowerStar_of_disjoint_range
    (hji : Disjoint (Set.range j.base) (Set.range i.base))
    (H : Sheaf Z.smallEtaleTopology A) :
    IsZero ((j)^*[A].obj ((i)_*[A].obj H)) :=
  (Etale.isZero_openImmersionRestriction_lowerStar A i j hji.symm H).of_iso
    ((Etale.upperStarIsoOpenImmersionRestriction A j).app ((i)_*[A].obj H))

omit [HasSmallSiteSheafify A] in
/-- Blueprint `lemma-openclosed-vanishing-lowershriek`: **`i^* j_! G` vanishes** when the
ranges of `j` and `i` are disjoint. No section of
`i^* j_! G` is ever computed: the adjunctions `i^* ⊣ i_*` and `j_! ⊣ j^*` turn
`Hom(i^* j_! G, H)` into `Hom(G, j^* i_* H)`, which is a singleton by
`AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range`. So `i^* j_! G` is
initial, and an initial object of a category with zero morphisms is a zero object. -/
lemma Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
    (hji : Disjoint (Set.range j.base) (Set.range i.base))
    (G : Sheaf U.smallEtaleTopology A) :
    IsZero ((i)^*[A].obj ((j)_!open[A].obj G)) := by
  refine IsInitial.isZero (IsInitial.ofUnique (h := fun H ↦ ?_))
  have : Unique (G ⟶ (j)^*[A].obj ((i)_*[A].obj H)) :=
    have hz := Etale.isZero_upperStar_lowerStar_of_disjoint_range A j i hji H
    ⟨⟨hz.isTerminal.from G⟩, fun _ ↦ hz.isTerminal.hom_ext _ _⟩
  exact Equiv.unique
    (((Etale.upperStarLowerStarAdjunction A i).homEquiv ((j)_!open[A].obj G) H).trans
      ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).homEquiv G ((i)_*[A].obj H)))

end Vanishing

end AlgebraicGeometry
