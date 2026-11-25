/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube

/-!
# The change-of-coefficients map for `Rf_!` along an arbitrary coefficient change

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, and write
`T^X = L(Ext_{a_X})` for the derived extension of scalars along `a_X`. For a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f : X ⟶ Y`, the derived lower shriek `Rf_!(c) = Di_! ⋙ Rg_*` on the
unbounded derived categories of module objects receives a canonical comparison
```
Rf_!(c)^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!(c)^Λ'
```
(`ProEtale.CondensedRing.derivedLowerShriekHomOfCompactification`): the (Push) comparison for the
proper `g` (`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`, the mate of the inverse
of the (Pull) isomorphism `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso` under the
derived adjunctions `Lg^* ⊣ Rg_*`), whiskered by `Di_!`, followed by `Rg_*` of the (Shriek)
isomorphism for the open immersion `i` (`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`).

No flatness of `a` is needed, so this covers the reduction `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`
(`Profinite.padicIntegersRingObjToIntegersModPow`) as well as the flat coefficient changes. For a
flat `a` and the chosen compactification, `ProEtale.CondensedRing.derivedLowerShriekHom` is the
analogous comparison built from `ProEtale.CondensedRing.derivedPushHom`.

The comparison is an isomorphism as soon as (Push) is one for `g`
(`ProEtale.CondensedRing.isIso_derivedLowerShriekHomOfCompactification`); whether this holds on
bounded constructible complexes is the subject of the change-of-coefficients lemmas for direct
images and compactly supported direct images.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- **The change-of-coefficients map for `Rf_!`** along an arbitrary coefficient change `a`, for
the derived lower shriek `Rf_!(c) = Di_! ⋙ Rg_*` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`: the comparison `Rf_!(c)^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!(c)^Λ'` is the
(Push) comparison `derivedUpperStarExtendScalarsPushHom a g` for the proper `g`, whiskered by
`Di_!`, followed by `Rg_*` of the (Shriek) isomorphism `derivedOpenImmersionShriekIso a i` for the
open immersion `i`. -/
noncomputable def derivedLowerShriekHomOfCompactification :
    Rf_!(c)⟦Λ⟧ ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ Rf_!(c)⟦Λ'⟧ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open⟦Λ⟧) (derivedUpperStarExtendScalarsPushHom a c.g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedOpenImmersionShriekIso a c.i).hom R((c.g)_*⟦Λ'⟧) ≫
    (Functor.associator _ _ _).hom

/-- The change-of-coefficients map for `Rf_!(c)` is an isomorphism whenever (Push) is one for the
proper part `g` of the compactification: the open immersion contributes a formal isomorphism. -/
instance isIso_derivedLowerShriekHomOfCompactification
    [IsIso (derivedUpperStarExtendScalarsPushHom a c.g)] :
    IsIso (derivedLowerShriekHomOfCompactification a c) := by
  unfold derivedLowerShriekHomOfCompactification
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
