/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!

# The underived (Pull) is a mate

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. The underived (Pull) `ProEtale.CondensedRing.pullIso a f : f^*_Λ ⋙ Ext_{a_X} ≅
Ext_{a_Y} ⋙ f^*_Λ'` is defined as the conjugate of the commutation `comapLowerStarIso` of the
restriction of scalars with the pushforwards. This file shows that it is also the mate, under the
extension-restriction adjunctions, of the inverse of the commutation `comapUpperStarIso` of the
restriction of scalars with the pullbacks (`ProEtale.CondensedRing.mateEquiv_pullIso_hom`), i.e.
that (Pull) is compatible with the units of `Ext ⊣ Res`
(`ProEtale.CondensedRing.upperStar_map_unit_comp_comapUpperStarIso_inv_app`).

The key input is that `comapUpperStarIso` and `comapLowerStarIso` are mates under `f^* ⊣ f_*`
(`ProEtale.CondensedRing.isMateSquare_comapUpperStarIso_comapLowerStarIso`); the statement then
follows from the iterated mate correspondence `iterated_mateEquiv_conjugateEquiv`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The underived (Pull) is the mate of the commutation of restriction of scalars with the
pullbacks**: under `Ext_{a_Y} ⊣ Res_{a_Y}` and `Ext_{a_X} ⊣ Res_{a_X}`, the mate of
`pullIso a f : f^*_Λ ⋙ Ext_{a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'` is the inverse of
`comapUpperStarIso a f`. -/
theorem mateEquiv_pullIso_hom :
    mateEquiv (Mod.extendRestrictAdjunction (coefficientMap a Y))
      (Mod.extendRestrictAdjunction (coefficientMap a X)) (pullIso a f).hom =
      (comapUpperStarIso a f).inv := by
  apply (mateEquiv (upperStarLowerStarAdjunction Λ' f)
    (upperStarLowerStarAdjunction Λ f)).injective
  erw [(Adjunction.isMateSquare_iff _ _ _ _).1
    (isMateSquare_comapUpperStarIso_comapLowerStarIso a f)]
  refine (iterated_mateEquiv_conjugateEquiv _ _ _ _ _).trans ?_
  rw [pullIso, Adjunction.pullIsoOfComapIso, conjugateIsoEquiv_symm_apply_hom,
    Equiv.apply_symm_apply]

/-- **The underived (Pull) is compatible with the units of `Ext ⊣ Res`**: for a
`Λ_Y`-module `M`, the pullback of the unit `M ⟶ Res (Ext M)`, followed by the commutation of
`Res` with the pullbacks, is the unit at `f^* M` followed by `Res` of (Pull). -/
@[reassoc]
theorem upperStar_map_unit_comp_comapUpperStarIso_inv_app
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)^*⟦Λ⟧.map ((Mod.extendRestrictAdjunction (coefficientMap a Y)).unit.app M) ≫
        (comapUpperStarIso a f).inv.app ((Mod.extendScalars (coefficientMap a Y)).obj M) =
      (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app ((f)^*⟦Λ⟧.obj M) ≫
        (Mod.comap (coefficientMap a X)).map ((pullIso a f).hom.app M) := by
  rw [← mateEquiv_pullIso_hom]
  exact unit_mateEquiv _ _ _ M

end AlgebraicGeometry.ProEtale.CondensedRing
