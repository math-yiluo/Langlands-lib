/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-!

# Compatibility of the six functors with a change of condensed coefficient rings

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, i.e. of commutative ring objects
of abelian sheaves on `*_proét`. For a scheme `X`, its pullback along `p_X` is a morphism of ring
objects `a_X : Λ_X ⟶ Λ'_X` (`ProEtale.coefficientMap`), inducing the *derived extension of
scalars*
```
T^X = Λ'_X ⊗ᴸ_{Λ_X} - = L(Ext_{a_X}) : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ'_X}).
```
This file constructs the *canonical comparison transformations* between these and the derived
functors `Lf^*`, `Rf_*`, `Rf_!` on module objects of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject`, for a morphism of schemes `f : X ⟶ Y`.
Following Corollary `cor:coeff-functor` of `WeilConjectures/RefactorInstruction.tex`, the
coefficient changes `a_X` are compatible with the canonical coefficient morphisms: the squares
```
  f^* Λ_Y --f^* a_Y--> f^* Λ'_Y              Λ_Y ----a_Y----> Λ'_Y
     |                     |                   |                |
    α_f                   α_f                 η_f              η_f
     ↓                     ↓                   ↓                ↓
    Λ_X -------a_X------> Λ'_X              f_* Λ_X --f_* a_X--> f_* Λ'_X
```
commute (`ProEtale.map_coefficientMap_comp_condensedPullbackHom`,
`ProEtale.condensedPushforwardHom_comp_map_coefficientMap`): the first is the naturality in `Λ`
of the comparison `f^* ∘ p_Y^* ≅ p_X^*`, and the second follows by adjunction. From these
squares, by the mate and conjugate constructions of
`WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`:

* **restriction of scalars commutes with the pushforward**, strictly
  (`ProEtale.CondensedRing.comapLowerStarIso`): both composites are `mapMod(f_*)` followed by
  the restriction of scalars along the common composite of the square; and in the derived
  categories (`ProEtale.CondensedRing.derivedComapLowerStarIso`), when `Λ'_X` is flat over
  `Λ_X`, so that the restriction of scalars preserves K-injective complexes;
* **(Pull)** `Lf^*_Λ ⋙ T^X ≅ T^Y ⋙ Lf^*_Λ'` (`ProEtale.CondensedRing.derivedPullIso`, and the
  underived `ProEtale.CondensedRing.pullIso`): the *conjugates* of the previous isomorphisms
  along `Lf^* ⊣ Rf_*` and `L(Ext) ⊣ D(Res)`, hence isomorphisms on all unbounded objects;
* **(Push)** `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'` (`ProEtale.CondensedRing.derivedPushHom`, and the
  underived `ProEtale.CondensedRing.pushHom`): the *mates* of the previous isomorphisms. They
  are not isomorphisms in general;
* **restriction of scalars commutes with the pullback**
  (`ProEtale.CondensedRing.comapUpperStarIso`), since every `α_f` is an isomorphism, and with
  the extension by zero along an open immersion `j`
  (`ProEtale.CondensedRing.comapOpenImmersionLowerShriekIso`). Hence the comparison
  `j_!^Λ ⋙ T^X ≅ T^U ⋙ j_!^Λ'` is an *isomorphism*, being the conjugate of the former along
  `j_! ⊣ j^*` (`ProEtale.CondensedRing.openImmersionShriekIso`, and its derived version
  `ProEtale.CondensedRing.derivedOpenImmersionShriekIso`);
* **(Shriek)** `Rf_!^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!^Λ'`
  (`ProEtale.CondensedRing.derivedLowerShriekHom`), for `Rf_! = Di_! ⋙ Rg_*` attached to the
  chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the derived (Push) for the proper `g`
  followed by the derived (Shriek) isomorphism for the open immersion `i`. It is an
  isomorphism whenever (Push) is one for `g`
  (`ProEtale.CondensedRing.isIso_derivedLowerShriekHom`).

The compatibilities with the derived tensor product, the derived hom and `Rf^!` are not
treated: they require the strong monoidality of the extension of scalars, respectively
perfectness or duality hypotheses, which are not formalized.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The coefficient changes `a_X` and the coefficient morphisms -/

section CoefficientMap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [MonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- The coefficient change `a_X = p_X^* a : Λ_X ⟶ Λ'_X` on `X_proét` induced by a morphism
`a : Λ ⟶ Λ'` of condensed rings. It is a morphism of ring objects, `p_X^*` being monoidal. -/
noncomputable abbrev coefficientMap (X : Scheme.{u}) :
    condensedRingObj Λ X ⟶ condensedRingObj Λ' X :=
  (upperStarFromPoint X).map a

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
lemma coefficientMap_id (X : Scheme.{u}) : coefficientMap (𝟙 Λ) X = 𝟙 _ :=
  (upperStarFromPoint X).map_id Λ

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
lemma coefficientMap_comp {Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    (b : Λ' ⟶ Λ'') (X : Scheme.{u}) :
    coefficientMap (a ≫ b) X = coefficientMap a X ≫ coefficientMap b X :=
  (upperStarFromPoint X).map_comp a b

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
/-- The coefficient morphisms `α_f : f^* Λ_Y ⟶ Λ_X` are natural in the condensed ring:
`f^* a_Y ≫ α_f = α_f ≫ a_X`. This is the naturality in `Λ` of the comparison
`f^* ∘ p_Y^* ≅ p_X^*`. -/
@[reassoc]
lemma map_coefficientMap_comp_condensedPullbackHom :
    (f)^*[Ab.{u + 1}].map (coefficientMap a Y) ≫ condensedPullbackHom Λ' f =
      condensedPullbackHom Λ f ≫ coefficientMap a X :=
  (upperStarFromPointComp f).hom.naturality a

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
/-- The coefficient morphisms `η_f : Λ_Y ⟶ f_* Λ_X` are natural in the condensed ring:
`η_f ≫ f_* a_X = a_Y ≫ η_f`. This follows from the naturality of `α_f` and of the unit of
`f^* ⊣ f_*`. -/
@[reassoc]
lemma condensedPushforwardHom_comp_map_coefficientMap :
    condensedPushforwardHom Λ f ≫ (f)_*[Ab.{u + 1}].map (coefficientMap a X) =
      coefficientMap a Y ≫ condensedPushforwardHom Λ' f := by
  rw [← unitAlgHom_comp_map_condensedPullbackHom, ← unitAlgHom_comp_map_condensedPullbackHom,
    Category.assoc, ← Functor.map_comp, ← map_coefficientMap_comp_condensedPullbackHom,
    Functor.map_comp]
  exact ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.naturality_assoc _ _).symm

end CoefficientMap

namespace CondensedRing

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-! ### Pushforward and pullback -/

section UpperLowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction of scalars commutes with the pushforward:
`f_*^Λ' ⋙ Res_{a_Y} ≅ Res_{a_X} ⋙ f_*^Λ`, both being `mapMod(f_*)` followed by the restriction
of scalars along the common composite of the square `a_Y ≫ η_f = η_f ≫ f_* a_X`. -/
noncomputable def comapLowerStarIso :
    (f)_*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a Y) ≅ Mod.comap (coefficientMap a X) ⋙ (f)_*⟦Λ⟧ :=
  Mod.comapMapModComapIso (f)_*[Ab.{u + 1}] (coefficientMap a X) (coefficientMap a Y)
    (condensedPushforwardHom Λ f) (condensedPushforwardHom Λ' f)
    (condensedPushforwardHom_comp_map_coefficientMap a f).symm

/-- **(Pull)**, underived: `f^*_Λ ⋙ Ext_{a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'`, the conjugate of
`comapLowerStarIso` along `f^* ⊣ f_*` and `Ext ⊣ Res`. -/
noncomputable def pullIso :
    (f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X) ≅
      Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧ :=
  Adjunction.pullIsoOfComapIso (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ' f)
    (comapLowerStarIso a f)

/-- **(Push)**, underived: the canonical comparison `f_*^Λ ⋙ Ext_{a_Y} ⟶ Ext_{a_X} ⋙ f_*^Λ'`,
the mate of `comapLowerStarIso` along `Ext ⊣ Res`. -/
noncomputable def pushHom :
    (f)_*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a Y) ⟶
      Mod.extendScalars (coefficientMap a X) ⋙ (f)_*⟦Λ'⟧ :=
  Adjunction.pushHomOfComapIso (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a Y)) (comapLowerStarIso a f)

/-- For every `f`, restriction of scalars commutes with the pullback:
`f^*_Λ' ⋙ Res_{a_X} ≅ Res_{a_Y} ⋙ f^*_Λ`, since the coefficient morphisms `α_f` are
isomorphisms. -/
noncomputable def comapUpperStarIso :
    (f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X) ≅ Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y))
      (Mod.extendScalarsComapIsoOfIsIso ((f)^*[Ab.{u + 1}].map (coefficientMap a Y))
        (coefficientMap a X) (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
        (map_coefficientMap_comp_condensedPullbackHom a f).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((f)^*[Ab.{u + 1}].mapModComapIso (coefficientMap a Y)).symm
      (Mod.extendScalars (condensedPullbackHom Λ f)) ≪≫
    Functor.associator _ _ _

/-- Restriction of scalars commutes with the levelwise derived pullback:
`Df^*_Λ' ⋙ D(Res_{a_X}) ≅ D(Res_{a_Y}) ⋙ Df^*_Λ`. -/
noncomputable def derivedComapUpperStarIso :
    D((f)^*⟦Λ'⟧) ⋙ D(Mod.comap (coefficientMap a X)) ≅
      D(Mod.comap (coefficientMap a Y)) ⋙ D((f)^*⟦Λ⟧) :=
  (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso (comapUpperStarIso a f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end UpperLowerStar

/-! ### Derived pushforward and pullback, for a flat coefficient change -/

section Derived

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

instance preservesHomology_extendScalars_coefficientMap (X : Scheme.{u}) :
    (Mod.extendScalars (coefficientMap a X)).PreservesHomology := {}

/-- The restriction of scalars along a flat coefficient change `a_X : Λ_X ⟶ Λ'_X` preserves
K-injective complexes, its left adjoint being exact. -/
instance preservesKInjectiveComplexes_comap_coefficientMap (X : Scheme.{u}) :
    (Mod.comap (coefficientMap a X) :
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) ⥤
        Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
      ).PreservesKInjectiveComplexes :=
  (Mod.extendRestrictAdjunction (coefficientMap a X)).preservesKInjectiveComplexes

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction of scalars commutes with the derived pushforward:
`Rf_*^Λ' ⋙ D(Res_{a_Y}) ≅ D(Res_{a_X}) ⋙ Rf_*^Λ`. The restriction of scalars is exact and, `Λ'_X`
being flat over `Λ_X`, preserves K-injective complexes, so both sides are the right derived
functor of the two equal composites of `comapLowerStarIso`. -/
noncomputable def derivedComapLowerStarIso :
    R((f)_*⟦Λ'⟧) ⋙ D(Mod.comap (coefficientMap a Y)) ≅
      D(Mod.comap (coefficientMap a X)) ⋙ R((f)_*⟦Λ⟧) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (f)_*⟦Λ'⟧
      (Mod.comap (coefficientMap a Y))).symm ≪≫
    Functor.rightDerivedFunctorNatIso (comapLowerStarIso a f) ≪≫
    Functor.rightDerivedFunctorCompIso (Mod.comap (coefficientMap a X)) (f)_*⟦Λ⟧ ≪≫
    Functor.isoWhiskerRight
      (Mod.comap (coefficientMap a X)).rightDerivedFunctorIsoMapDerivedCategory R((f)_*⟦Λ⟧)

/-- **(Pull)**: `Lf^*_Λ ⋙ T^X ≅ T^Y ⋙ Lf^*_Λ'`, the conjugate of `derivedComapLowerStarIso` along
the derived adjunctions. It is an isomorphism on all unbounded objects. -/
noncomputable def derivedPullIso :
    L((f)^*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a Y)) ⋙ L((f)^*⟦Λ'⟧) :=
  Adjunction.pullIsoOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ' f)
    (derivedComapLowerStarIso a f)

/-- **(Push)**: the canonical comparison `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'`, the mate of
`derivedComapLowerStarIso` along `L(Ext) ⊣ D(Res)`. It is not an isomorphism in general. -/
noncomputable def derivedPushHom :
    R((f)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R((f)_*⟦Λ'⟧) :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedComapLowerStarIso a f)

end Derived

/-! ### Extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restriction of scalars commutes with the extension by zero along an open immersion:
`j_!^Λ' ⋙ Res_{a_X} ≅ Res_{a_U} ⋙ j_!^Λ`, by the naturality of the projection formula and the
square of the coefficient morphisms `α_j`. -/
noncomputable def comapOpenImmersionLowerShriekIso :
    (j)_!open⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X) ≅
      Mod.comap (coefficientMap a U) ⋙ (j)_!open⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mod.comap (condensedPullbackHom Λ' j))
      ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1}
        j).projectionFormula.mapModLeftComapIso (coefficientMap a X)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Mod.comapComp _ _).symm ≪≫
      Mod.comapCongr (map_coefficientMap_comp_condensedPullbackHom a j) ≪≫
      Mod.comapComp _ _) _ ≪≫
    Functor.associator _ _ _

/-- **(Shriek) for an open immersion**, underived: `j_!^Λ ⋙ Ext_{a_X} ≅ Ext_{a_U} ⋙ j_!^Λ'`, the
conjugate of `comapUpperStarIso` along `j_! ⊣ j^*` and `Ext ⊣ Res`. -/
noncomputable def openImmersionShriekIso :
    (j)_!open⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X) ≅
      Mod.extendScalars (coefficientMap a U) ⋙ (j)_!open⟦Λ'⟧ :=
  (conjugateIsoEquiv ((Mod.extendRestrictAdjunction (coefficientMap a U)).comp
    (openImmersionLowerShriekUpperStarAdjunction Λ' j))
    ((openImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (Mod.extendRestrictAdjunction (coefficientMap a X)))).symm
    (comapUpperStarIso a j)

/-- **(Shriek) for an open immersion**: `Dj_!^Λ ⋙ T^X ≅ T^U ⋙ Dj_!^Λ'`, the conjugate of
`derivedComapUpperStarIso` along the derived adjunctions `Dj_! ⊣ Dj^*` and
`L(Ext) ⊣ D(Res)`. It is an isomorphism on all unbounded objects. -/
noncomputable def derivedOpenImmersionShriekIso :
    D((j)_!open⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a U)) ⋙ D((j)_!open⟦Λ'⟧) :=
  (conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))).symm
    (derivedComapUpperStarIso a j)

end OpenImmersion

/-! ### Derived lower shriek -/

section LowerShriek

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- **(Shriek)**: the canonical comparison `Rf_!^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!^Λ'` for
`Rf_! = Di_! ⋙ Rg_*` attached to the chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the
derived (Push) comparison for the proper `g` followed by the derived (Shriek) isomorphism for
the open immersion `i`. -/
noncomputable def derivedLowerShriekHom :
    R(f)_!⟦Λ⟧ ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R(f)_!⟦Λ'⟧ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D(((HasCompactification.compactification f).i)_!open⟦Λ⟧)
      (derivedPushHom a (HasCompactification.compactification f).g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionShriekIso a (HasCompactification.compactification f).i).hom
      R(((HasCompactification.compactification f).g)_*⟦Λ'⟧) ≫
    (Functor.associator _ _ _).hom

/-- **(Shriek)** is an isomorphism whenever (Push) is one for the proper part `g` of the chosen
compactification: its open immersion contributes a formal isomorphism. -/
instance isIso_derivedLowerShriekHom
    [IsIso (derivedPushHom a (HasCompactification.compactification f).g)] :
    IsIso (derivedLowerShriekHom a f) := by
  unfold derivedLowerShriekHom
  infer_instance

end LowerShriek

end CondensedRing

end AlgebraicGeometry.ProEtale
