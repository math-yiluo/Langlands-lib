/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!

# The extension by zero along an open immersion is fully faithful

For an open immersion `j : U ⟶ X` the lower shriek `j_!` on small étale sites is fully
faithful: the unit of `j_! ⊣ j^*` is an isomorphism, so `j^* j_! F ≅ F` for every sheaf `F`
on `U`. Equivalently, `j_!` embeds the sheaves on `U` as the sheaves on `X` supported on the
image of `j`.

No hypothesis beyond what is needed to define `j_!` is required — in particular no clopen
hypothesis on the range of `j`, and no condition on the coefficient category `A` beyond
`HasInitial A` and sheafification on `X`.

## The proof

`j_! ⊣ j^* ⊣ j_*` is an adjoint triple, and in an adjoint triple the two outer functors are
fully faithful together: the unit of the left adjunction is invertible if and only if the
counit of the right one is
(`CategoryTheory.Adjunction.Triple.isIso_unit_iff_isIso_counit`, packaged for this situation
applied to `AlgebraicGeometry.Etale.openImmersionAdjunctionTriple`). The counit of
`j^* ⊣ j_*` is *already known* to be invertible —
`AlgebraicGeometry.Etale.isIso_openImmersionRestrictionLowerStarAdjunction_counit`, which
holds because `j` is a monomorphism, so the unit of the site-level adjunction
`MorphismProperty.Over.mapPullbackAdj` is an isomorphism.

So the whole statement is a transport across a formal equivalence, and none of the
sheaf-theoretic work one might expect is needed. In particular this route never has to
compare `j^*` of a sheafification with the sheafification of a restriction, which is the
step that makes the direct argument (restrict the presheaf-level Kan extension, then
sheafify) hard: Mathlib has no "`sheafPullback` along a fully faithful cocontinuous functor
is fully faithful", and none is needed here.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekAdjunction_unit`: the unit of
  `j_! ⊣ j^*` is an isomorphism.
- `AlgebraicGeometry.Etale.fullyFaithfulOpenImmersionLowerShriek`, with the corresponding
  `Full` and `Faithful` instances.
- `AlgebraicGeometry.Etale.fullyFaithfulLowerStarOfIsOpenImmersion`: the pushforward `j_*` is
  fully faithful as well, so `j^* j_* F ≅ F`.
- `AlgebraicGeometry.Etale.isIso_openImmersionRestriction_map_lowerShriekAdjunction_counit`:
  `j^*` of the counit of `j_! ⊣ j^*` is an isomorphism at every sheaf. This is the form the
  comparison `j_! ⟶ j_*` consumes; see
  `AlgebraicGeometry.Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar` in
  `WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

open Etale

/-- **The unit of `j_! ⊣ j^*` is an isomorphism for an open immersion `j`**, i.e.
`j^* j_! F ≅ F` naturally in `F`.

In the adjoint triple `j_! ⊣ j^* ⊣ j_*` the unit of the left adjunction is invertible
exactly when the counit of the right one is, and the latter is
`Etale.isIso_openImmersionRestrictionLowerStarAdjunction_counit`. -/
instance Etale.isIso_openImmersionLowerShriekAdjunction_unit :
    IsIso (Etale.openImmersionLowerShriekAdjunction A j).unit :=
  (Etale.openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
    (Etale.isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)

/-- **The extension by zero along an open immersion is fully faithful.** -/
noncomputable def Etale.fullyFaithfulOpenImmersionLowerShriek :
    (j)_!open[A].FullyFaithful :=
  (Etale.openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit

instance Etale.full_openImmersionLowerShriek : (j)_!open[A].Full :=
  (Etale.fullyFaithfulOpenImmersionLowerShriek A j).full

instance Etale.faithful_openImmersionLowerShriek : (j)_!open[A].Faithful :=
  (Etale.fullyFaithfulOpenImmersionLowerShriek A j).faithful

/-- **The pushforward along an open immersion is fully faithful**, the counit of `j^* ⊣ j_*`
being an isomorphism by `Etale.isIso_openImmersionRestrictionLowerStarAdjunction_counit`.
In particular the counit of `Etale.upperStarLowerStarAdjunction` along `j` is an isomorphism,
i.e. `j^* j_* F ≅ F`. -/
noncomputable def Etale.fullyFaithfulLowerStarOfIsOpenImmersion : (j)_*[A].FullyFaithful :=
  (Etale.openImmersionRestrictionLowerStarAdjunction A j).fullyFaithfulROfIsIsoCounit

instance Etale.full_lowerStar_of_isOpenImmersion : (j)_*[A].Full :=
  (Etale.fullyFaithfulLowerStarOfIsOpenImmersion A j).full

instance Etale.faithful_lowerStar_of_isOpenImmersion : (j)_*[A].Faithful :=
  (Etale.fullyFaithfulLowerStarOfIsOpenImmersion A j).faithful

/-- `j^*` of the unit of `j^* ⊣ j_*` is an isomorphism at every sheaf `G` on `X`, for an open
immersion `j`: the triangle identity `j^*(η_G) ≫ ε_{j^* G} = 𝟙` exhibits it as the inverse of
the counit `ε_{j^* G}`, which is an isomorphism since `j_*` is fully faithful. -/
instance Etale.isIso_upperStar_map_upperStarLowerStarAdjunction_unit_of_isOpenImmersion
    (G : Sheaf X.smallEtaleTopology A) :
    IsIso ((j)^*[A].map ((Etale.upperStarLowerStarAdjunction A j).unit.app G)) := by
  rw [← IsIso.inv_eq_of_inv_hom_id
    ((Etale.upperStarLowerStarAdjunction A j).left_triangle_components G)]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- `j^*` of the counit of `j_! ⊣ j^*` is an isomorphism at every sheaf `G` on `X`.

This is the triangle identity read backwards: `η_{j^* G} ≫ j^*(ε_G) = 𝟙`, and `η` is an
isomorphism by `Etale.isIso_openImmersionLowerShriekAdjunction_unit`, so `j^*(ε_G)` is its
inverse. Note that `ε_G` itself is *not* an isomorphism — `j_! j^* G ⟶ G` is the
"restriction to the image of `j`, extended by zero" map, which forgets the sections away
from `j`. -/
instance Etale.isIso_openImmersionRestriction_map_lowerShriekAdjunction_counit
    (G : Sheaf X.smallEtaleTopology A) :
    IsIso ((Etale.openImmersionRestriction A j).map
      ((Etale.openImmersionLowerShriekAdjunction A j).counit.app G)) := by
  have h := (Etale.openImmersionLowerShriekAdjunction A j).right_triangle_components (Y := G)
  rw [← IsIso.inv_eq_of_hom_inv_id h]
  infer_instance

end AlgebraicGeometry
