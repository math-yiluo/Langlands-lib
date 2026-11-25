/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.OpenClosed

/-!
# Base change of `j_!` and `i_*` on module sheaves over a sheaf of rings: supports

Let `B` be a sheaf of `R`-algebras on `X_proét`, `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j : U ⟶ X`, `g : X' ⟶ X` a morphism and `i' : Z' ⟶ X'`,
`j' : U' ⟶ X'` the base changes. For the `g^* B`-module sheaves obtained by pulling back:

* `g^* j_! N` is the extension by zero of its restriction to `U'`: the counit
  `j'_! j'^* g^* j_! N ⟶ g^* j_! N` is an isomorphism of `g^* B`-module sheaves
  (`ProEtale.RingSheaf.isIso_counit_app_upperStar_obj_openImmersionLowerShriek_obj`);
* `g^* i_* G` is the pushforward of its restriction to `Z'`: the unit
  `g^* i_* G ⟶ i'_* i'^* g^* i_* G` is an isomorphism of `g^* B`-module sheaves
  (`ProEtale.RingSheaf.isIso_unit_app_upperStar_obj_lowerStar_obj`).

Together with the identifications of the underlying sheaves of the restrictions
(`j'^* g^* j_! N ≅ g_U^* N`, `i'^* g^* i_* G ≅ g_Z^* G`, see
`AlgebraicGeometry.ProEtale.upperStarLowerStarClosedBaseChangeIso`) this is the module-level
content of part (4) of blueprint `proposition-extension-zero-restriction-closed-subscheme`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

variable {R : Type (u + 1)} [CommRing R] {Z U X Z' U' X' : Scheme.{u}}
  (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [MonObj B]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (g : X' ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i'] (j' : U' ⟶ X') [IsOpenImmersion j']
  [QuasiCompact j'] (gZ : Z' ⟶ Z) (gU : U' ⟶ U)
  (hij : IsCompl (Set.range i.base) (Set.range j.base))
  (hij' : IsCompl (Set.range i'.base) (Set.range j'.base))

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (4), for `j_!`: the
pullback `g^* j_! N` of an extension by zero of module sheaves is the extension by zero of its
restriction to `U' = g⁻¹ U`, i.e. the counit `j'_! j'^* g^* j_! N ⟶ g^* j_! N` is an isomorphism
of `g^* B`-module sheaves. -/
theorem isIso_counit_app_upperStar_obj_openImmersionLowerShriek_obj (hi : i' ≫ g = gZ ≫ i)
    (N : Mod (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))
      ((j)^*[ModuleCat.{u + 1} R].obj B)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction ((g)^*[ModuleCat.{u + 1} R].obj B)
      i' j' hij').counit.app
        ((upperStar B g).obj ((openImmersionLowerShriek B i j hij).obj N))) := by
  set adj := ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j'
  set M := (g)^*[ModuleCat.{u + 1} R].obj ((j)_!open[ModuleCat.{u + 1} R].obj N.X)
  have : IsIso (adj.counit.app M) := by
    have : IsIso ((i')^*[ModuleCat.{u + 1} R].map (adj.counit.app M)) :=
      ⟨⟨0, (isZero_upperStar_openImmersionLowerShriek _ j' i'
          (Set.disjoint_iff_inter_eq_empty.1 hij'.disjoint.symm) _).eq_of_src _ _,
        (isZero_upperStar_upperStar_openImmersionLowerShriek i j g i' gZ hij hi
          N.X).eq_of_src _ _⟩⟩
    exact isIso_of_isIso_upperStar_of_isCompl i' j' hij' _
  have : IsIso ((Mod.forget _).map
      ((openImmersionLowerShriekUpperStarAdjunction ((g)^*[ModuleCat.{u + 1} R].obj B)
        i' j' hij').counit.app
        ((upperStar B g).obj ((openImmersionLowerShriek B i j hij).obj N)))) := by
    rw [Mod.forget_map, openImmersionLowerShriekUpperStarAdjunction_counit_app_hom]
    exact this
  exact isIso_of_reflects_iso _ (Mod.forget _)

omit [IsClosedImmersion i] [QuasiCompact j] in
include hij hij' in
/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (4), for `i_*`: the
pullback `g^* i_* G` of a pushforward of module sheaves along `i` is the pushforward of its
restriction to `Z' = g⁻¹ Z`, i.e. the unit `g^* i_* G ⟶ i'_* i'^* g^* i_* G` is an isomorphism of
`g^* B`-module sheaves. -/
theorem isIso_unit_app_upperStar_obj_lowerStar_obj (hj : j' ≫ g = gU ≫ j)
    (G : Mod (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R))
      ((i)^*[ModuleCat.{u + 1} R].obj B)) :
    IsIso ((upperStarLowerStarAdjunction ((g)^*[ModuleCat.{u + 1} R].obj B) i').unit.app
      ((upperStar B g).obj ((lowerStar B i).obj G))) := by
  have := ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl i' j' hij' _
    (isZero_upperStar_upperStar_lowerStar i j g j' gU hij hj G.X)
  have : IsIso ((Mod.forget _).map
      ((upperStarLowerStarAdjunction ((g)^*[ModuleCat.{u + 1} R].obj B) i').unit.app
        ((upperStar B g).obj ((lowerStar B i).obj G)))) := by
    rw [Mod.forget_map, upperStarLowerStarAdjunction_unit_app_hom]
    exact this
  exact isIso_of_reflects_iso _ (Mod.forget _)

end AlgebraicGeometry.ProEtale.RingSheaf
