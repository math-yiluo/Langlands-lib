/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

import WeilConjectures.AlgebraicGeometry.ProEtaleInternalPullbackKFlat

/-!

# Derived upper star and lower star on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback and pushforward on the derived categories `D(Mod_{Λ_X})` of module objects over
`Λ_X = p_X^* Λ` are *not* given definitions of their own: as in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`, they are the
*total* derived functors, i.e. the generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory` applied to the underived functors `(f)^*⟦Λ⟧`
and `(f)_*⟦Λ⟧` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:

| derived functor | notation | meaning |
| --- | --- | --- |
| `Rf_* : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_Y})` | `R((f)_*⟦Λ⟧)` | `(f)_*⟦Λ⟧.rightDerivedFunctor` |
| `Rf_* : D⁺(Mod_{Λ_X}) ⥤ D⁺(Mod_{Λ_Y})` | `R+((f)_*⟦Λ⟧)` | `rightDerivedFunctorPlus` |
| `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` | `L((f)^*⟦Λ⟧)` | `(f)^*⟦Λ⟧.leftDerivedFunctor` |
| `f^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` | `D((f)^*⟦Λ⟧)` | `(f)^*⟦Λ⟧.mapDerivedCategory` |
| `f^* : D⁺(Mod_{Λ_Y}) ⥤ D⁺(Mod_{Λ_X})` | `D+((f)^*⟦Λ⟧)` | `mapDerivedCategoryPlus` |

The derived pushforward is computed on K-injective resolutions in `Mod_{Λ_X}`, and the
derived pullback is the total left derived functor of `f^* = Λ_X ⊗_{f^* Λ_Y} f^*(-)`,
computed on K-flat resolutions in `Mod_{Λ_Y}`, that is
```
Lf^* M = Λ_X ⊗ᴸ_{f^* Λ_Y} f^* M,
```
the derived extension of scalars along `α_f` of the exact pullback `f^* M`; this is the
pullback of Bhatt–Scholze, Remark 6.8.15. The pullback `f^*` on module objects is exact, the
coefficient morphism `α_f` being an isomorphism
(`ProEtale.CondensedRing.preservesFiniteLimits_upperStar`, see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`), so,
as for étale sheaves, `Lf^*` is canonically the levelwise functor `D((f)^*⟦Λ⟧)`
(`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`), and on the bounded
below derived categories the pullback is the levelwise functor `D+((f)^*⟦Λ⟧)`, left adjoint to
`R+((f)_*⟦Λ⟧)` (`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunctionPlus`).

The two displayed formulas are theorems about the total derived functors, not definitions:

* `ProEtale.CondensedRing.rightDerivedLowerStarIso`:
  `R((f)_*⟦Λ⟧) ≅ R(mapMod(f_*)) ⋙ D(Res_{η_f})`. The restriction of scalars along
  `η_f : Λ_Y ⟶ f_* Λ_X` is exact, so right deriving the composite
  `(f)_*⟦Λ⟧ = mapMod(f_*) ⋙ Res_{η_f}` amounts to right deriving `mapMod(f_*)` and restricting
  scalars levelwise (`Functor.rightDerivedFunctorCompMapDerivedCategoryIso`).
* `ProEtale.CondensedRing.leftDerivedUpperStarIso`:
  `L((f)^*⟦Λ⟧) ≅ D(mapMod(f^*)) ⋙ L(Ext_{α_f})`. The exact functor `mapMod(f^*)` preserves
  K-flat complexes, so left deriving the composite `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` amounts
  to applying `mapMod(f^*)` levelwise and left deriving the extension of scalars, both being
  computed on the same K-flat resolution in `Mod_{Λ_Y}`
  (`Functor.leftDerivedFunctorCompMapDerivedCategoryIso`).

## Main results

- `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`: the derived adjunction
  `L((f)^*⟦Λ⟧) ⊣ R((f)_*⟦Λ⟧)`, induced by the adjunction `f^* ⊣ f_*` on module objects, and
  `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunctionPlus`: its bounded below
  version `D+((f)^*⟦Λ⟧) ⊣ R+((f)_*⟦Λ⟧)`.

- `ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`: the derived pullback
  `L((f)^*⟦Λ⟧)` is the levelwise functor `D((f)^*⟦Λ⟧)`.

- `ProEtale.CondensedRing.leftDerivedUpperStarComp`: the composition isomorphism
  `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, obtained from the underived
  `ProEtale.CondensedRing.upperStarComp` through the levelwise functors.

- `ProEtale.CondensedRing.rightDerivedLowerStarIso` and
  `ProEtale.CondensedRing.leftDerivedUpperStarIso`: the computations of `Rf_*` and `Lf^*`
  described above.

## K-flatness input

- `ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_upperStar`: `mapMod(f^*)` sends
  K-flat complexes of `Λ_Y`-modules to K-flat complexes of `f^* Λ_Y`-modules; this is
  `ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_proEtale` of
  `WeilConjectures.AlgebraicGeometry.ProEtaleInternalPullbackKFlat`, proved stalkwise at enough
  pro-étale points. Indeed
  `f^*` is strong monoidal, exact and commutes with colimits, so it commutes with the relative
  tensor product of complexes of module objects and preserves acyclicity. From it follows that
  the pullback `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` on module objects preserves
  quasi-isomorphisms between K-flat complexes
  (`ProEtale.CondensedRing.preservesKFlatQuasiIso_upperStar`), which is the functor-specific
  input of the K-flat machinery making `L((f)^*⟦Λ⟧)` meaningful; the other ingredient is that
  extension of scalars preserves quasi-isomorphisms between K-flat complexes
  (`Mod.preservesKFlatQuasiIso`, proved in
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`).

The remaining sorries are those of the module-object formalism
(`WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`,
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`), of the pro-étale
sheaf categories (`AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf`) and of `Ab`
(`AddCommGrpCat.hasFunctorialFlatResolution`).

-/

@[expose] public section
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local irreducible] Mod.monoidalClosed Mod.monoidalCategory
  Mod.monoidalCategoryStruct upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

attribute [local instance 20000] preservesKFlatComplexes_mapMod_proEtale

section CachedInstances

set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency.types false

private noncomputable instance cachedSheafColimits (T : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  ⟨fun _ _ ↦ Sheaf.instHasColimitsOfShape⟩

private noncomputable instance cachedSheafBigColimits (T : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1} (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  IsGrothendieckAbelian.hasColimits _

private noncomputable instance cachedCoequalizers (T : Scheme.{u}) :
    HasCoequalizers (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.instHasColimitsOfShape

private instance cachedModulePreadditive (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    MonoidalPreadditive (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

private instance cachedTensorLeft (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
  infer_instance

private instance cachedTensorRight (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
  infer_instance

private instance cachedGood12 (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P Q R₁ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q R₁ := by
  infer_instance

private instance cachedGood23 (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P Q R₁ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q R₁ := by
  infer_instance

private instance cachedFour (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P Q R₁ S₁ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasTensor₄ObjExt P Q R₁ S₁ := by
  infer_instance

private instance cachedModuleFlatResolution (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

private instance cachedExactSequential (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    HasExactColimitsOfShape ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

private instance cachedTensorLeftSequential (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) := by
  infer_instance

private instance cachedTensorRightSequential (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) := by
  infer_instance

end CachedInstances

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The derived pushforward -/

section DerivedLowerStar

/-- The total right derived functor `Rf_* : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_Y})` of the
pushforward `f_*` on module objects over `Λ`, on the unbounded derived categories,
computed on K-injective resolutions.

It is not a definition of its own: it is the generic `Functor.rightDerivedFunctor`, written
`R(-)`, applied to the underived pushforward `(f)_*⟦Λ⟧`. -/
noncomputable example :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  R((f)_*⟦Λ⟧)

/-- The right derived functor `Rf_* : D⁺(Mod_{Λ_X}) ⥤ D⁺(Mod_{Λ_Y})` of the pushforward
`f_*` on module objects, on the *bounded below* derived categories: the generic
`Functor.rightDerivedFunctorPlus`, written `R+(-)`, applied to `(f)_*⟦Λ⟧`. -/
noncomputable example :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  R+((f)_*⟦Λ⟧)

/-- The derived pushforward on module objects is the total right derived functor of
`mapMod(f_*) : Mod_{Λ_X} ⥤ Mod_{f_* Λ_X}` followed by the levelwise restriction of scalars
along `η_f : Λ_Y ⟶ f_* Λ_X`: the restriction of scalars is exact, so right deriving the
composite `(f)_*⟦Λ⟧ = mapMod(f_*) ⋙ Res_{η_f}` amounts to right deriving `mapMod(f_*)` and
restricting scalars levelwise. -/
noncomputable def rightDerivedLowerStarIso :
    R((f)_*⟦Λ⟧) ≅
      R((f)_*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)) ⋙
        D(Mod.comap (condensedPushforwardHom Λ f)) :=
  Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    ((f)_*[Ab.{u + 1}].mapMod (condensedRingObj Λ X))
    (Mod.comap (condensedPushforwardHom Λ f))

end DerivedLowerStar

/-! ### The derived pullback -/

section DerivedUpperStar

instance preservesHomology_mapMod_upperStar :
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).PreservesHomology := {}

set_option maxSynthPendingDepth 10 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Blueprint `lem-sfb-module-mapmod-pullback-kflat`: the pullback
`mapMod(f^*) : Mod_{Λ_Y} ⥤ Mod_{f^* Λ_Y}` sends K-flat complexes to K-flat complexes. See the
module docstring for the argument. -/
instance preservesKFlatComplexes_mapMod_upperStar :
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).PreservesKFlatComplexes := by
  exact preservesKFlatComplexes_mapMod_proEtale f (condensedRingObj Λ Y)

/-- The pullback `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` on module objects over `Λ` preserves
quasi-isomorphisms between K-flat complexes: `mapMod(f^*)` is exact and preserves K-flat
complexes, and the extension of scalars preserves quasi-isomorphisms between K-flat
complexes. This is the functor-specific input of the K-flat left derivability structure. -/
instance preservesKFlatQuasiIso_upperStar : (f)^*⟦Λ⟧.PreservesKFlatQuasiIso :=
  Functor.preservesKFlatQuasiIso_comp
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
    (Mod.extendScalars (condensedPullbackHom Λ f))

/-- The total left derived functor `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` of the pullback
`f^*` on module objects over `Λ`, on the unbounded derived categories, computed on K-flat
resolutions: `Lf^* M = Λ_X ⊗ᴸ_{f^* Λ_Y} f^* M`.

It is not a definition of its own: it is the generic `Functor.leftDerivedFunctor`, written
`L(-)`, applied to the underived pullback `(f)^*⟦Λ⟧`. -/
noncomputable example :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) :=
  L((f)^*⟦Λ⟧)

/-- The derived pullback on module objects is the levelwise pullback
`D(mapMod(f^*)) : D(Mod_{Λ_Y}) ⥤ D(Mod_{f^* Λ_Y})` followed by the derived extension of
scalars `Λ_X ⊗ᴸ_{f^* Λ_Y} -` along `α_f`: `mapMod(f^*)` is exact and preserves K-flat
complexes, so left deriving the composite `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` amounts to
applying `mapMod(f^*)` levelwise and left deriving the extension of scalars. -/
noncomputable def leftDerivedUpperStarIso :
    L((f)^*⟦Λ⟧) ≅
      D((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)) ⋙
        L(Mod.extendScalars (condensedPullbackHom Λ f)) :=
  Functor.leftDerivedFunctorCompMapDerivedCategoryIso
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
    (Mod.extendScalars (condensedPullbackHom Λ f))

/-- The derived pullback on module objects is the levelwise functor: since `f^*` on module
objects is exact (`ProEtale.CondensedRing.preservesFiniteLimits_upperStar`), its total left
derived functor `L((f)^*⟦Λ⟧)`, computed via K-flat resolutions, is canonically isomorphic to the
functor `D((f)^*⟦Λ⟧)` induced by applying `f^*` levelwise. This is
`Functor.leftDerivedFunctorIsoMapDerivedCategory` at `f^*`. -/
noncomputable def leftDerivedUpperStarIsoMapDerivedCategory :
    L((f)^*⟦Λ⟧) ≅ D((f)^*⟦Λ⟧) :=
  (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of derived pullbacks on module
objects over `Λ`, obtained from the underived composition isomorphism
`ProEtale.CondensedRing.upperStarComp` and the compatibility of left derivation with
`mapDerivedCategory` for exact functors. -/
noncomputable def leftDerivedUpperStarComp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    L((f ≫ g)^*⟦Λ⟧) ≅ L((g)^*⟦Λ⟧) ⋙ L((f)^*⟦Λ⟧) :=
  Functor.leftDerivedFunctorNatIso _ (upperStarComp Λ f g) ≪≫
    Functor.leftDerivedFunctorCompIso (g)^*⟦Λ⟧ (f)^*⟦Λ⟧

end DerivedUpperStar

/-! ### The derived adjunction `Lf^* ⊣ Rf_*` -/

section Adjunction

/-- The derived adjunction `Lf^* ⊣ Rf_*` between the total derived functors of the pullback
and the pushforward on module objects over `Λ`, induced by the adjunction `f^* ⊣ f_*` of
`ProEtale.CondensedRing.upperStarLowerStarAdjunction`: the left adjoint is derived via the
K-flat left derivability structure on `D(Mod_{Λ_Y})` and the right adjoint via the
K-injective right derivability structure on `D(Mod_{Λ_X})`. -/
noncomputable def derivedUpperStarLowerStarAdjunction : L((f)^*⟦Λ⟧) ⊣ R((f)_*⟦Λ⟧) :=
  (upperStarLowerStarAdjunction Λ f).derivedAdjunction

instance : L((f)^*⟦Λ⟧).IsLeftAdjoint := (derivedUpperStarLowerStarAdjunction Λ f).isLeftAdjoint

instance : R((f)_*⟦Λ⟧).IsRightAdjoint := (derivedUpperStarLowerStarAdjunction Λ f).isRightAdjoint

/-- The bounded below version of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`:
since the pullback `f^*` on module objects is exact, its derived functor on the bounded below
derived categories is the levelwise functor `D+((f)^*⟦Λ⟧)`, and it is left adjoint to the right
derived functor `R+((f)_*⟦Λ⟧)` of the pushforward on the bounded below derived categories. -/
noncomputable def derivedUpperStarLowerStarAdjunctionPlus :
    D+((f)^*⟦Λ⟧) ⊣ R+((f)_*⟦Λ⟧) :=
  (upperStarLowerStarAdjunction Λ f).derivedAdjunctionPlus

end Adjunction

end AlgebraicGeometry.ProEtale.CondensedRing
