/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelationsGeneral
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Pullback along a weakly étale morphism preserves flat sheaves of modules

For an arbitrary (not necessarily Noetherian) commutative ring `Λ` and a weakly étale morphism
`g : W ⟶ X`, the pullback `g^*` of pro-étale sheaves of `Λ`-modules preserves flat objects.
Indeed, `g^*` is restriction along the localization functor `W.ProEt ⥤ X.ProEt`
(`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), which is cocontinuous, and
restriction along a cocontinuous functor preserves locally trivial relations
(`CategoryTheory.Presheaf.HasLocallyTrivialRelations.comp`); these characterize flatness over
any commutative ring (`CategoryTheory.Sheaf.flat_iff_hasLocallyTrivialRelations'`).

## Main results

- `AlgebraicGeometry.ProEtale.flat_upperStar_obj_of_weaklyEtale`: `g^*` sends flat sheaves of
  `Λ`-modules to flat ones.
- `AlgebraicGeometry.ProEtale.preservesFlat_upperStar_of_weaklyEtale`: the same, stated with
  `CategoryTheory.Functor.PreservesFlat`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {W X : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g]

-- the instances `WEqualsLocallyBijective` and `HasSheafCompose` on the small pro-étale sites
-- take long to synthesize
/-- **Pullback along a weakly étale morphism preserves flat sheaves of modules**, over an
arbitrary commutative ring `Λ`: `g^*` is restriction along the cocontinuous localization
functor, which preserves locally trivial relations. -/
theorem flat_upperStar_obj_of_weaklyEtale
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (hF : ObjectProperty.flat F) :
    ObjectProperty.flat (((g)^*[ModuleCat.{u + 1} Λ]).obj F) := by
  have := Scheme.ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale g)
  have h := ((Sheaf.flat_iff_hasLocallyTrivialRelations' F).1 hF).comp
    (J := Scheme.ProEt.topology W)
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g))
  refine ObjectProperty.prop_of_iso _
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) g inferInstance).app F).symm ?_
  exact (Sheaf.flat_iff_hasLocallyTrivialRelations' _).2 h

/-- **Pullback along a weakly étale morphism preserves flat sheaves of modules**, over an
arbitrary commutative ring `Λ`. -/
theorem preservesFlat_upperStar_of_weaklyEtale : ((g)^*[ModuleCat.{u + 1} Λ]).PreservesFlat :=
  ⟨flat_upperStar_obj_of_weaklyEtale g⟩

end AlgebraicGeometry.ProEtale
