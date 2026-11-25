/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Localization

/-!
# The direct image of Weil complexes along a closed immersion

For a closed immersion `i : Z ⟶ X` of `k₀`-schemes, with `X` locally of finite type over `k₀`,
the derived pushforward `Ri_*` of pro-étale Weil sheaves carries Weil complexes to Weil
complexes without appeal to the finiteness theorem: `ī_*` is exact and preserves constructible
`ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.boundedConstructibleAdicClosedLowerStar`). This
gives the functor `AlgebraicGeometry.WeilComplex.derivedLowerStarOfIsClosedImmersion`, which is
`AlgebraicGeometry.WeilComplex.derivedLowerStar i` (whose definition uses the finiteness
theorem), and the closed half of the open–closed recollement of Weil complexes,
`AlgebraicGeometry.WeilComplex.exists_isIso_app_of_isZero_upperStar_of_isClosedImmersion`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
/-- The derived pushforward of a Weil complex along a closed immersion is a Weil complex: its
underlying complex is `Rī_*` of the underlying complex
(`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso`), which lies
in `Dᵇc` as `ī_*` is exact and preserves constructible sheaves (`AlgebraicGeometry.ProEtale.`
`boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj_of_isClosedImmersion`).
This does not use the finiteness theorem. -/
theorem WeilComplex.objectProperty_rightDerivedLowerStar_of_isClosedImmersion
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) (hK : WeilComplex.objectProperty k₀ l Z K) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.lowerStar k₀ l i).rightDerivedFunctor.obj K) := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  rw [WeilComplex.objectProperty_iff] at hK ⊢
  exact (ProEtale.DerivedCategory.boundedConstructibleAdic l _).prop_of_iso
    ((IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app K).symm
    (ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj_of_isClosedImmersion
      _ hK)

/-- The derived pushforward `Ri_*` of Weil complexes along a closed immersion `i`: the total
right derived functor of the pushforward of pro-étale Weil sheaves, restricted to Weil complexes
(`AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedLowerStar_of_isClosedImmersion`).
Unlike `AlgebraicGeometry.WeilComplex.derivedLowerStar`, its definition does not use the
finiteness theorem. -/
noncomputable def WeilComplex.derivedLowerStarOfIsClosedImmersion :
    WeilComplex k₀ l Z ⥤ WeilComplex k₀ l X :=
  (WeilComplex.objectProperty k₀ l Z).liftFullSubcategory (WeilComplex.objectProperty k₀ l X)
    (ProEtaleWeilSheaf.lowerStar k₀ l i).rightDerivedFunctor
    (WeilComplex.objectProperty_rightDerivedLowerStar_of_isClosedImmersion i)

/-- `AlgebraicGeometry.WeilComplex.derivedLowerStarOfIsClosedImmersion` is the general derived
pushforward `AlgebraicGeometry.WeilComplex.derivedLowerStar`: both are the restriction of
`Ri_*`. -/
noncomputable def WeilComplex.derivedLowerStarIsoDerivedLowerStarOfIsClosedImmersion
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) i ≅
      WeilComplex.derivedLowerStarOfIsClosedImmersion i :=
  Iso.refl _

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--8` and
`proposition-extension-zero-restriction-closed-subscheme` (open–closed recollement), for Weil
complexes. Let `i : Z ⟶ X` be a closed immersion of `k₀`-schemes of finite type and `j : U ⟶ X` the
complementary open immersion. There is a natural transformation `K ⟶ Ri_* i^* K` (the closed
unit) which is an isomorphism at every `K` with `j^* K = 0`: in the recollement triangle
`j_! j^* K ⟶ K ⟶ Ri_* i^* K ⟶`, the first term vanishes. Here `Ri_*` is
`AlgebraicGeometry.WeilComplex.derivedLowerStarOfIsClosedImmersion`.

The closed unit is the unit of `i^* ⊣ Ri_*`
(`AlgebraicGeometry.ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction`); it is invertible at
`K` with `j^* K = 0` by
`DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero`, using that
`i_*` is exact, `j^* i_* = 0` and that `i^*`, `j^*` jointly detect zero objects. The open
immersion `j` is quasi-compact since `X` is Noetherian. -/
theorem WeilComplex.exists_isIso_app_of_isZero_upperStar_of_isClosedImmersion {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (hij : Set.range j = (Set.range i)ᶜ)
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ η : 𝟭 (WeilComplex k₀ l X) ⟶
        WeilComplex.upperStar i ⋙ WeilComplex.derivedLowerStarOfIsClosedImmersion (k₀ := k₀)
          (l := l) i,
      ∀ K : WeilComplex k₀ l X, IsZero ((WeilComplex.upperStar j).obj K) → IsIso (η.app K) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have hij' : IsCompl (Set.range i.base) (Set.range j.base) := by
    have h : Set.range j.base = (Set.range i.base)ᶜ := hij
    rw [h]
    exact isCompl_compl
  let adj := ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l i
  refine ⟨{ app K := ObjectProperty.homMk (adj.unit.app K.obj)
            naturality _ _ f := ObjectProperty.hom_ext _ (adj.unit.naturality f.hom) },
    fun K hK ↦ ?_⟩
  have := ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl (k₀ := k₀) (l := l)
    i j hij'
  have hiso : IsIso (adj.unit.app K.obj) :=
    DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero
      (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i)
      (ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj i j hij')
      (ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij')
      ((ObjectProperty.ι _).map_isZero hK)
  have : IsIso ((ObjectProperty.ι (WeilComplex.objectProperty k₀ l X)).map
      (ObjectProperty.homMk (adj.unit.app K.obj) :
        (show WeilComplex k₀ l X from K) ⟶ (WeilComplex.derivedLowerStarOfIsClosedImmersion i).obj
          ((WeilComplex.upperStar i).obj K))) := hiso
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

end AlgebraicGeometry
