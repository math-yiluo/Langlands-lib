/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMate
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# The coefficient comparisons for `Rf_*`, `Rf_!` and `Rf^!` along `𝒪_E ⟶ E`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`k` a field of characteristic `p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write
`T_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` for the extension of scalars `E_X ⊗ᴸ_{𝒪_{E,X}} -` on bounded
constructible complexes (`ProEtale.boundedConstructibleExtendScalars`). This file proves the
clauses of blueprint `proposition-six-operations-change-coefficients` on `Rf_*`, `Rf_!` and `f^!`
for the coefficient change `𝒪_E ⟶ E`:

* **(Push)** (blueprint `lemma-change-coefficients-direct-image`): the comparison
  `γ : Rg_*^{𝒪_E} ⋙ T_Y ⟶ T_Z ⋙ Rg_*^E`, the composite of the unit of `g^* ⊣ Rg_*`, the pullback
  comparison (`ProEtale.CondensedRing.boundedConstructibleUpperStarExtendScalarsIso`) and the
  counit, that is, the mate of the pullback comparison
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarExtendScalars`), is an isomorphism
  (`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarExtendScalars`);
* **(Shriek)** (blueprint `lemma-change-coefficients-compact-support`):
`j_!^{𝒪_E} ⋙ T_X ≅ T_U ⋙ j_!^E`
  for an open immersion `j`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso`) and
  `Rf_!^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!^E` for every `f`, along the chosen compactification
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekExtendScalarsIso`);
* **(Exceptional)** (blueprint `lemma-change-coefficients-exceptional-inverse-image`): the exchange
  `β : Rf^!_{𝒪_E} ⋙ T_X ⟶ T_Y ⋙ Rf^!_E`, the mate of the inverse of (Shriek)
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekExtendScalars`), is an isomorphism
  (`ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekExtendScalars`).

Both isomorphism statements hold because `T_X` is the rationalization of `Dᵇc(X)⟦𝒪_E⟧`: it is a
localization functor at the morphisms whose mapping cone is killed by a power of `ℓ`
(`ProEtale.isLocalization_boundedConstructibleExtendScalars`, blueprint
`proposition-inverting-ell`), and the mate of an isomorphism of left adjoints along
two rationalizations is an isomorphism
(`CategoryTheory.Rationalization.isIso_mateEquiv_of_isLocalization`): on `Hom` groups it is the
localization at `ℓ` of the adjunction bijection.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### Zero morphisms -/

section Zero

variable (X : Scheme.{u})

/-- The extension of scalars `T_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` preserves zero morphisms, as the
derived extension of scalars, a left adjoint, does. -/
instance : (boundedConstructibleExtendScalars X ℓ E).PreservesZeroMorphisms := by
  have := (Mod.derivedExtendMapDerivedCategoryAdjunction
    (padicIntegersToPadicSubfield X ℓ E)).left_adjoint_additive
  have : (boundedConstructibleExtendScalars X ℓ E).Additive := by
    unfold boundedConstructibleExtendScalars
    infer_instance
  exact Functor.preservesZeroMorphisms_of_additive _

end Zero

/-! ### (Push) -/

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y)

/-- **(Push)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E` (blueprint
`lemma-change-coefficients-direct-image`): the comparison `γ : Rg_*^{𝒪_E} ⋙ T_Y ⟶ T_Z ⋙ Rg_*^E`, the
mate of the inverse of the pullback comparison under the adjunctions `g^* ⊣ Rg_*`, that is, the
unit of `g^* ⊣ Rg_*`, the pullback comparison and the counit. -/
noncomputable def boundedConstructibleLowerStarExtendScalars :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 g ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ⟶
      boundedConstructibleExtendScalars Z.left ℓ E ⋙
        ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g :=
  mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E.1 g)
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E g)
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E g).inv

/-- **(Push) is an isomorphism** for `𝒪_E ⟶ E` (blueprint `lemma-change-coefficients-direct-image`
(1)): the extension of scalars is a rationalization on both sides, and `γ` is the mate of the
pullback comparison. -/
theorem isIso_boundedConstructibleLowerStarExtendScalars :
    IsIso (boundedConstructibleLowerStarExtendScalars ℓ E g) := by
  have := noetherianSpace_left_of_over Y
  have := noetherianSpace_left_of_over Z
  exact Rationalization.isIso_mateEquiv_of_isLocalization (M := Submonoid.powers (ℓ : ℤ))
    (boundedConstructibleExtendScalars Y.left ℓ E) (boundedConstructibleExtendScalars Z.left ℓ E)
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E.1 g)
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E g)
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E g)

/-- **(Push)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E`:
`Rg_*^{𝒪_E} ⋙ T_Y ≅ T_Z ⋙ Rg_*^E`. -/
noncomputable def boundedConstructibleLowerStarExtendScalarsIso :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 g ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ≅
      boundedConstructibleExtendScalars Z.left ℓ E ⋙
        ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g :=
  haveI := isIso_boundedConstructibleLowerStarExtendScalars ℓ E g
  asIso (boundedConstructibleLowerStarExtendScalars ℓ E g)

end LowerStar

/-! ### (Shriek) for an open immersion -/

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- **(Shriek)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E` and an open
immersion `j`: `j_!^{𝒪_E} ⋙ T_X ≅ T_U ⋙ j_!^E`, the restriction of
`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.1) ℓ j ⋙
        boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars U.left ℓ E ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E.1) ℓ j :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleExtendScalarsCompatibility X.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedOpenImmersionShriekIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) j.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleExtendScalarsCompatibility U.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j).symm ≪≫
      (Functor.associator _ _ _).symm)

end OpenImmersion

/-! ### (Shriek) and the exchange for `f^!` -/

section Shriek

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **(Shriek)** on bounded constructible complexes along a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, for the inclusion `𝒪_E ⟶ E`:
`Rf_!(c)^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!(c)^E`, composed of (Shriek) for the open immersion `i` and
(Push) for the proper `g`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationExtendScalarsIso
    {f : X ⟶ Y} (c : Compactification f.left) :
    PadicIntegersRingObj.boundedConstructibleLowerShriekOfCompactification ℓ E.1 c ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ℓ E
          c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarExtendScalarsIso ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E c.overI) _ ≪≫
    Functor.associator _ _ _

variable (f : X ⟶ Y)

/-- **(Shriek)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E` (blueprint
`lemma-change-coefficients-compact-support`): `Rf_!^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!^E`, along the chosen
compactification. -/
noncomputable def boundedConstructibleLowerShriekExtendScalarsIso :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f :=
  boundedConstructibleLowerShriekOfCompactificationExtendScalarsIso ℓ E
    (compactificationOverField f)

/-- **The exchange for `f^!`**, for the inclusion `𝒪_E ⟶ E` (blueprint
`lemma-change-coefficients-exceptional-inverse-image`): the canonical natural transformation
`β : Rf^!_{𝒪_E} ⋙ T_X ⟶ T_Y ⋙ Rf^!_E`, the mate of the inverse of (Shriek)
(`boundedConstructibleLowerShriekExtendScalarsIso`) under the adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekExtendScalars :
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f ⋙
        boundedConstructibleExtendScalars X.left ℓ E ⟶
      boundedConstructibleExtendScalars Y.left ℓ E ⋙
        ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f :=
  mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).inv

/-- The exchange for `f^!` as the mate of a two-square. -/
lemma boundedConstructibleUpperShriekExtendScalars_eq_mateEquiv :
    boundedConstructibleUpperShriekExtendScalars ℓ E f =
      (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
        (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
        (TwoSquare.mk _ _ _ _
          (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).inv)) :=
  rfl

/-- **The exchange for `f^!` is an isomorphism** for `𝒪_E ⟶ E` (blueprint
`lemma-change-coefficients-exceptional-inverse-image`): the extension of scalars is a
rationalization on both sides, and `β` is the mate of the isomorphism (Shriek). -/
theorem isIso_boundedConstructibleUpperShriekExtendScalars :
    IsIso (boundedConstructibleUpperShriekExtendScalars ℓ E f) := by
  have := noetherianSpace_left_of_over X
  have := noetherianSpace_left_of_over Y
  exact Rationalization.isIso_mateEquiv_of_isLocalization (M := Submonoid.powers (ℓ : ℤ))
    (boundedConstructibleExtendScalars X.left ℓ E) (boundedConstructibleExtendScalars Y.left ℓ E)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f)

/-- The exchange for `f^!` as an isomorphism `Rf^!_{𝒪_E} ⋙ T_X ≅ T_Y ⋙ Rf^!_E`. -/
noncomputable def boundedConstructibleUpperShriekExtendScalarsIso :
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f ⋙
        boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars Y.left ℓ E ⋙
        ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f :=
  haveI := isIso_boundedConstructibleUpperShriekExtendScalars ℓ E f
  asIso (boundedConstructibleUpperShriekExtendScalars ℓ E f)

end Shriek

end AlgebraicGeometry.ProEtale.CondensedRing
