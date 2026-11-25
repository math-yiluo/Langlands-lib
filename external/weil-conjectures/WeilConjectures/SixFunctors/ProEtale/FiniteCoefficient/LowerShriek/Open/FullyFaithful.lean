/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!

# The extension by zero along an open immersion is fully faithful

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`.

For an open immersion `j : U ⟶ X` the lower shriek `j_!` on small pro-étale sites is fully
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
applied to `AlgebraicGeometry.ProEtale.openImmersionAdjunctionTriple`). The counit of
`j^* ⊣ j_*` is *already known* to be invertible —
`AlgebraicGeometry.ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit`, which
holds because `j` is a monomorphism, so the unit of the site-level adjunction
`MorphismProperty.Over.mapPullbackAdj` is an isomorphism.

So the whole statement is a transport across a formal equivalence, and none of the
sheaf-theoretic work one might expect is needed. In particular this route never has to
compare `j^*` of a sheafification with the sheafification of a restriction, which is the
step that makes the direct argument (restrict the presheaf-level Kan extension, then
sheafify) hard: Mathlib has no "`sheafPullback` along a fully faithful cocontinuous functor
is fully faithful", and none is needed here.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekAdjunction_unit`: the unit of
  `j_! ⊣ j^*` is an isomorphism.
- `AlgebraicGeometry.ProEtale.fullyFaithfulOpenImmersionLowerShriek`, with the corresponding
  `Full` and `Faithful` instances.
- `AlgebraicGeometry.ProEtale.isIso_openImmersionRestriction_map_lowerShriekAdjunction_counit`:
  `j^*` of the counit of `j_! ⊣ j^*` is an isomorphism at every sheaf. This is the form the
  comparison `j_! ⟶ j_*` consumes; see
  `AlgebraicGeometry.ProEtale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar` in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Comparison`.
- `AlgebraicGeometry.ProEtale.presheafToSheafObjIsoOpenImmersionLowerShriek`: a presheaf on `X`
  vanishing away from `U` sheafifies to an extension by zero.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

open ProEtale

/-- **The unit of `j_! ⊣ j^*` is an isomorphism for an open immersion `j`**, i.e.
`j^* j_! F ≅ F` naturally in `F`.

In the adjoint triple `j_! ⊣ j^* ⊣ j_*` the unit of the left adjunction is invertible
exactly when the counit of the right one is, and the latter is
`ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit`. -/
instance ProEtale.isIso_openImmersionLowerShriekAdjunction_unit :
    IsIso (ProEtale.openImmersionLowerShriekAdjunction A j).unit :=
  (ProEtale.openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
    (ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)

/-- **The extension by zero along an open immersion is fully faithful.** -/
noncomputable def ProEtale.fullyFaithfulOpenImmersionLowerShriek :
    (j)_!open[A].FullyFaithful :=
  (ProEtale.openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit

instance ProEtale.full_openImmersionLowerShriek : (j)_!open[A].Full :=
  (ProEtale.fullyFaithfulOpenImmersionLowerShriek A j).full

instance ProEtale.faithful_openImmersionLowerShriek : (j)_!open[A].Faithful :=
  (ProEtale.fullyFaithfulOpenImmersionLowerShriek A j).faithful

set_option backward.isDefEq.respectTransparency false in
/-- `j^*` of the counit of `j_! ⊣ j^*` is an isomorphism at every sheaf `G` on `X`.

This is the triangle identity read backwards: `η_{j^* G} ≫ j^*(ε_G) = 𝟙`, and `η` is an
isomorphism by `ProEtale.isIso_openImmersionLowerShriekAdjunction_unit`, so `j^*(ε_G)` is
its inverse. Note that `ε_G` itself is *not* an isomorphism — `j_! j^* G ⟶ G` is the
"restriction to the image of `j`, extended by zero" map, which forgets the sections away
from `j`. -/
instance ProEtale.isIso_openImmersionRestriction_map_lowerShriekAdjunction_counit
    (G : Sheaf (Scheme.ProEt.topology X) A) :
    IsIso ((ProEtale.openImmersionRestriction A j).map
      ((ProEtale.openImmersionLowerShriekAdjunction A j).counit.app G)) := by
  have h := (ProEtale.openImmersionLowerShriekAdjunction A j).right_triangle_components (Y := G)
  rw [← IsIso.inv_eq_of_hom_inv_id h]
  infer_instance

/-- Sheafifying the presheaf-level extension by zero is the extension by zero of the
sheafification: both are left adjoint to the restriction of sheaves on `X`, viewed as
presheaves on `U`. -/
noncomputable def ProEtale.lanPresheafToSheafIsoOpenImmersionLowerShriek :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.lan ⋙
        presheafToSheaf (Scheme.ProEt.topology X) A ≅
      presheafToSheaf (Scheme.ProEt.topology U) A ⋙ (j)_!open[A] :=
  Adjunction.leftAdjointUniq
    (((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.lanAdjunction A).comp
      (sheafificationAdjunction (Scheme.ProEt.topology X) A))
    ((sheafificationAdjunction (Scheme.ProEt.topology U) A).comp
      (ProEtale.openImmersionLowerShriekAdjunction A j))

/-- A presheaf on `X` vanishing over every weakly étale `X`-scheme not factoring through `U`
sheafifies to the extension by zero of a sheaf on `U`: before sheafification it is the
presheaf-level extension by zero of its restriction to `U`. -/
noncomputable def ProEtale.presheafToSheafObjIsoOpenImmersionLowerShriek
    (R : (Scheme.ProEt X)ᵒᵖ ⥤ A)
    (hR : ∀ W, IsEmpty (CostructuredArrow
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op W) → IsZero (R.obj W)) :
    (presheafToSheaf (Scheme.ProEt.topology X) A).obj R ≅
      (j)_!open[A].obj ((presheafToSheaf (Scheme.ProEt.topology U) A).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op ⋙ R)) :=
  have := Functor.isIso_lanAdjunction_counit_app_of_isZero _
    (SmallSite.mem_essImage_or_isEmpty_costructuredArrow_op_overMap
      (inferInstance : WeaklyEtale j)) R hR
  (presheafToSheaf (Scheme.ProEt.topology X) A).mapIso (asIso
    (((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.lanAdjunction A).counit.app
      R)).symm ≪≫ (ProEtale.lanPresheafToSheafIsoOpenImmersionLowerShriek A j).app _

end AlgebraicGeometry
