/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreePullbackCube
public import WeilConjectures.WeilSheaf.SmoothPurityScalarCompositionNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsComp

/-! # Geometric pullback and ordinary coefficient composition -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
  (c : Λ ⟶ Λ'') [IsMonHom c] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The canonical pullback comparison commutes with composition of ordinary
coefficient extensions. This uses the precise composition iso in Tate reduction. -/
lemma pullIso_inv_app_comp_extendScalarsCompIsoOfEq (hc : a ≫ b = c)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (Mod.extendScalars (coefficientMap b X)).map ((pullIso a g).inv.app M) ≫
        (Mod.extendScalarsCompIsoOfEq (coefficientMap_comp_eq a b c hc X)).hom.app
          ((g)^*⟦Λ⟧.obj M) =
      (pullIso b g).hom.app ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫
        (g)^*⟦Λ''⟧.map
          ((Mod.extendScalarsCompIsoOfEq (coefficientMap_comp_eq a b c hc Y)).hom.app M) ≫
        (pullIso c g).inv.app M := by
  apply purity_free_pullback_cube
    (upperStarLowerStarAdjunction Λ g)
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (Mod.extendRestrictAdjunction (coefficientMap a X))
    (upperStarLowerStarAdjunction Λ' g)
    (Mod.extendRestrictAdjunction (coefficientMap b Y))
    (Mod.extendRestrictAdjunction (coefficientMap b X))
    (Mod.extendRestrictAdjunction (coefficientMap c Y))
    (Mod.extendRestrictAdjunction (coefficientMap c X))
    (upperStarLowerStarAdjunction Λ'' g)
    (pullIso a g).symm (pullIso c g).symm _ _ (pullIso b g)
  intro N
  rw [Mod.purity_conjugate_extendScalarsCompIsoOfEq,
    Mod.purity_conjugate_extendScalarsCompIsoOfEq,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_iso_symm]
  simp only [pullIso, Adjunction.pullIsoOfComapIso, Equiv.apply_symm_apply]
  change (g)_*⟦Λ⟧.map ((comapCoefficientMapCompIso a b c hc X).inv.app N) ≫
      (comapLowerStarIso a g).inv.app ((Mod.comap (coefficientMap b X)).obj N) =
    (comapLowerStarIso c g).inv.app N ≫
      (comapCoefficientMapCompIso a b c hc Y).inv.app ((g)_*⟦Λ''⟧.obj N) ≫
      (Mod.comap (coefficientMap a Y)).map ((comapLowerStarIso b g).hom.app N)
  apply (cancel_epi ((comapLowerStarIso c g).hom.app N)).mp
  rw [Iso.hom_inv_id_app_assoc, comapLowerStarIso_hom_app_of_comp_eq a b c g hc]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.comp_obj]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry.ProEtale.CondensedRing
