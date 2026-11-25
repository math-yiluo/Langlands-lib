/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedOpenImmersion

/-!
# The unit `F ⟶ j_* j^* F` along an open immersion with closed range

For an open immersion `j : U ⟶ X`, the counit `j_! j^* F ⟶ F` of `j_! ⊣ j^*` followed by the
unit `F ⟶ j_* j^* F` of `j^* ⊣ j_*` is the comparison `j_! ⟶ j_*` at `j^* F`. When the range of
`j` is closed, the comparison is an isomorphism, so the unit `F ⟶ j_* j^* F` is a split
epimorphism: sections over `U` extend by zero to `X`.

## Main statements

- `AlgebraicGeometry.ProEtale.isSplitEpi_adicUpperStarLowerStarAdjunction_unit_app`: the unit
  `F ⟶ j_* j^* F` is a split epimorphism for an open immersion `j` with closed range.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The counit `j_! j^* F ⟶ F` of `j_! ⊣ j^*` followed by the unit `F ⟶ j_* j^* F` of
`j^* ⊣ j_*` is the comparison `j_! ⟶ j_*` at `j^* F`: both have transpose the inverse of the
counit `j^* j_* j^* F ⟶ j^* F` under `j_! ⊣ j^*`. -/
lemma adicOpenImmersionLowerShriekAdjunction_counit_app_comp_unit_app (F : AdicSheaf l X) :
    (adicOpenImmersionLowerShriekAdjunction l j).counit.app F ≫
        (adicUpperStarLowerStarAdjunction l j).unit.app F =
      (adicOpenImmersionLowerShriekToLowerStar l j).app ((j)^*ᵃ[l].obj F) := by
  apply ((adicOpenImmersionLowerShriekAdjunction l j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar,
    Functor.map_comp, (adicOpenImmersionLowerShriekAdjunction l j).right_triangle_components_assoc]
  exact IsIso.eq_inv_of_inv_hom_id
    ((adicUpperStarLowerStarAdjunction l j).left_triangle_components F)

/-- **The unit `F ⟶ j_* j^* F` is a split epimorphism for an open immersion `j` with closed
range**: a section is the inverse of the comparison `j_! ⟶ j_*`
(`AlgebraicGeometry.ProEtale.isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range`)
followed by the counit `j_! j^* F ⟶ F`. -/
theorem isSplitEpi_adicUpperStarLowerStarAdjunction_unit_app
    (hj : IsClosed (Set.range j.base)) (F : AdicSheaf l X) :
    IsSplitEpi ((adicUpperStarLowerStarAdjunction l j).unit.app F) :=
  have := isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range l j hj
  ⟨⟨{ section_ := inv ((adicOpenImmersionLowerShriekToLowerStar l j).app ((j)^*ᵃ[l].obj F)) ≫
        (adicOpenImmersionLowerShriekAdjunction l j).counit.app F
      id := by
        rw [Category.assoc, adicOpenImmersionLowerShriekAdjunction_counit_app_comp_unit_app,
          IsIso.inv_hom_id] }⟩⟩

end AlgebraicGeometry.ProEtale
