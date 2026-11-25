/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal

/-! # Coefficient composition for the ordinary restriction/pullback comparison -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
  (c : Λ ⟶ Λ'') [IsMonHom c] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction of scalars commutes with pullback coherently for a composite coefficient
change. The proof uses the actual scalar-extension unit of the geometric pullback. -/
theorem comapUpperStarIso_inv_app_of_coefficient_comp (hc : a ≫ b = c)
    (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ'' Y)) :
    (f)^*⟦Λ⟧.map ((comapCoefficientMapCompIso a b c hc Y).inv.app N) ≫
        (comapUpperStarIso a f).inv.app ((Mod.comap (coefficientMap b Y)).obj N) ≫
        (Mod.comap (coefficientMap a X)).map ((comapUpperStarIso b f).inv.app N) =
      (comapUpperStarIso c f).inv.app N ≫
        (comapCoefficientMapCompIso a b c hc X).inv.app ((f)^*⟦Λ''⟧.obj N) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', Mod.comap_map_hom]
  apply (cancel_epi (upperStarUnitHom Λ f
    ((Mod.comap (coefficientMap c Y)).obj N))).mp
  rw [upperStarUnitHom_map_hom_assoc]
  simp only [comapCoefficientMapCompIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Mod.comp_hom', Mod.comapCongr_inv_app_hom,
    Mod.comapComp_hom_app_hom, Functor.comp_obj]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]
  have ha := upperStarUnitHom_comapUpperStarIso_inv_app_hom a f
    ((Mod.comap (coefficientMap b Y)).obj N)
  have hb := upperStarUnitHom_comapUpperStarIso_inv_app_hom b f N
  have hc' := upperStarUnitHom_comapUpperStarIso_inv_app_hom c f N
  have hab := congrArg (fun t ↦ t ≫ ((comapUpperStarIso b f).inv.app N).hom) ha
  exact (Category.assoc _ _ _).symm.trans (hab.trans (hb.trans hc'.symm))

end AlgebraicGeometry.ProEtale.CondensedRing
