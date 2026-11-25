/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!

# (Pull) for an arbitrary change of condensed coefficient rings

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. The comparison **(Pull)** `ProEtale.CondensedRing.derivedPullIso` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` is constructed as a
conjugate along the derived adjunctions, which needs the restriction of scalars along `a_X` to
preserve K-injective complexes, i.e. `Λ'_X` to be flat over `Λ_X`. This file constructs the
isomorphism
```
Lf^*_Λ ⋙ (Λ'_X ⊗ᴸ_{Λ_X} -) ≅ (Λ'_Y ⊗ᴸ_{Λ_Y} -) ⋙ Lf^*_Λ'
```
for *every* coefficient change `a`, flat or not
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`), on the left adjoint side. This
applies for instance to the reductions `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`, which are not flat.

The construction uses that the pullback `f^*_Λ = Ext_{α_f} ∘ mapMod(f^*)` on module objects is
exact, so that both `Lf^*` are levelwise:

* `Lf^*_Λ ⋙ L(Ext_{a_X}) ≅ D(mapMod(f^*)) ⋙ L(Ext_{α_f}) ⋙ L(Ext_{a_X})`
  (`ProEtale.CondensedRing.leftDerivedUpperStarIso`);
* `L(Ext_{α_f}) ⋙ L(Ext_{a_X}) ≅ L(Ext_{α_f ≫ a_X})`, the transitivity of the derived extension
  of scalars (`Mod.derivedExtendScalarsCompIso`);
* `D(mapMod(f^*)) ⋙ L(Ext_{α_f ≫ a_X}) ≅ L(mapMod(f^*) ⋙ Ext_{α_f ≫ a_X})`, since `mapMod(f^*)`
  is exact and preserves K-flat complexes
  (`Functor.leftDerivedFunctorCompMapDerivedCategoryIso`);
* `mapMod(f^*) ⋙ Ext_{α_f ≫ a_X} ≅ f^*_Λ ⋙ Ext_{a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'`, the underived
  (Pull) `ProEtale.CondensedRing.pullIso`, and left deriving it;
* `L(Ext_{a_Y} ⋙ f^*_Λ') ≅ L(Ext_{a_Y}) ⋙ D(f^*_Λ')`, the exact functor `f^*_Λ'` being applied
  levelwise (`Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The underived (Pull) isomorphism, rewritten with the extension of scalars along the
composite `α_f ≫ a_X`: `mapMod(f^*) ⋙ Ext_{α_f ≫ a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'`. -/
noncomputable def mapModUpperStarExtendScalarsIso :
    (f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y) ⋙
        Mod.extendScalars (condensedPullbackHom Λ f ≫ coefficientMap a X) ≅
      Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧ :=
  Functor.isoWhiskerLeft ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsComp (condensedPullbackHom Λ f) (coefficientMap a X)) ≪≫
    (Functor.associator _ _ _).symm ≪≫ pullIso a f

/-- `mapMod(f^*) ⋙ Ext_{α_f ≫ a_X}` preserves quasi-isomorphisms between K-flat complexes:
`mapMod(f^*)` is exact and preserves K-flat complexes. -/
instance preservesKFlatQuasiIso_mapMod_upperStar_comp_extendScalars :
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y) ⋙
        Mod.extendScalars (condensedPullbackHom Λ f ≫ coefficientMap a X)).PreservesKFlatQuasiIso :=
  Functor.preservesKFlatQuasiIso_comp _ _

/-- **(Pull)** for an arbitrary coefficient change `a : Λ ⟶ Λ'`:
`Lf^*_Λ ⋙ (Λ'_X ⊗ᴸ_{Λ_X} -) ≅ (Λ'_Y ⊗ᴸ_{Λ_Y} -) ⋙ Lf^*_Λ'`. Unlike
`ProEtale.CondensedRing.derivedPullIso`, no flatness of `Λ'_X` over `Λ_X` is needed: the
pullbacks are exact and both sides are computed by left deriving the underived (Pull)
isomorphism `ProEtale.CondensedRing.pullIso`; see the module docstring. -/
noncomputable def derivedUpperStarExtendScalarsIso :
    L((f)^*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a Y)) ⋙ L((f)^*⟦Λ'⟧) :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIso Λ f) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.derivedExtendScalarsCompIso (condensedPullbackHom Λ f)
      (coefficientMap a X) _ rfl).symm ≪≫
    (Functor.leftDerivedFunctorCompMapDerivedCategoryIso
      ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
      (Mod.extendScalars (condensedPullbackHom Λ f ≫ coefficientMap a X))).symm ≪≫
    Functor.leftDerivedFunctorIsoOfIso (mapModUpperStarExtendScalarsIso a f) ≪≫
    Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso
      (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm

end AlgebraicGeometry.ProEtale.CondensedRing
