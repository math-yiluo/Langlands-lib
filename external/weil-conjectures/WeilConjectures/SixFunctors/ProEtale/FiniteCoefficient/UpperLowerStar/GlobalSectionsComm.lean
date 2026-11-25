/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Global sections of pushforwards along commuting squares

Let `g : Z ⟶ W`, `h_W : W ⟶ W` and `h_Z : Z ⟶ Z` with `h_Z ≫ g = g ≫ h_W`. The identifications
`Γ(W, g_* -) ≅ Γ(Z, -)` (`AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso`) are
compatible with the isomorphism `g_* ⋙ (h_W)_* ≅ (h_Z)_* ⋙ g_*` of the square
(`AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso_comm`): all the maps involved are
restrictions of sections between terminal objects of the pro-étale site of `Z`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {Z W : Scheme.{u}}

lemma globalSectionsLowerStarIso_hom_app_eq_sections (g : Z ⟶ W) (M : Sheaf (ProEt.topology Z) A) :
    (globalSectionsLowerStarIso A g).hom.app M =
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId W)).hom.app ((g)_*[A].obj M) ≫
        M.obj.map (overPullbackObjMkIdIso g).inv.op ≫
          (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Z)).inv.app M := by
  simp [globalSectionsLowerStarIso]

lemma globalSectionsLowerStarIso_inv_app_eq_sections (g : Z ⟶ W) (M : Sheaf (ProEt.topology Z) A) :
    (globalSectionsLowerStarIso A g).inv.app M =
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Z)).hom.app M ≫
        M.obj.map (overPullbackObjMkIdIso g).hom.op ≫
          (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId W)).inv.app ((g)_*[A].obj M) := by
  simp [globalSectionsLowerStarIso]

lemma sheafΓ_map_eq_sections {X : Scheme.{u}} {M N : Sheaf (ProEt.topology X) A} (φ : M ⟶ N) :
    (Sheaf.Γ _ A).map φ =
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId X)).hom.app M ≫
        φ.hom.app (op (Scheme.ProEt.mk (𝟙 X))) ≫
          (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId X)).inv.app N := by
  rw [← cancel_mono ((Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId X)).hom.app N)]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId X)).hom.naturality φ

variable {Z' W' : Scheme.{u}}

/-- **Global sections along a commuting square.** For `h_Z ≫ g' = g ≫ h_W`, the identification
`Γ(W', g'_* (h_Z)_* M) ≅ Γ(W', (h_W)_* g_* M)` of the square is compatible with the
identifications of global sections of pushforwards. -/
lemma globalSectionsLowerStarIso_comm (g : Z ⟶ W) (g' : Z' ⟶ W') (hW : W ⟶ W') (hZ : Z ⟶ Z')
    (comm : hZ ≫ g' = g ≫ hW) (M : Sheaf (ProEt.topology Z) A) :
    (globalSectionsLowerStarIso A g).inv.app M ≫
        (globalSectionsLowerStarIso A hW).inv.app ((g)_*[A].obj M) ≫
          (Sheaf.Γ _ A).map ((lowerStarComp A g hW).hom.app M ≫
            (lowerStarCongr A comm.symm).hom.app M ≫ (lowerStarComp A hZ g').inv.app M) ≫
            (globalSectionsLowerStarIso A g').hom.app ((hZ)_*[A].obj M) =
      (globalSectionsLowerStarIso A hZ).inv.app M := by
  rw [globalSectionsLowerStarIso_inv_app_eq_sections,
    globalSectionsLowerStarIso_inv_app_eq_sections,
    globalSectionsLowerStarIso_inv_app_eq_sections,
    globalSectionsLowerStarIso_hom_app_eq_sections, sheafΓ_map_eq_sections]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStarComp_hom_app_hom_app,
    lowerStarCongr_hom_app_hom_app, lowerStarComp_inv_app_hom_app, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp]
  congr 1
  exact Quiver.Hom.unop_inj ((ProEt.isTerminalMkId Z).hom_ext _ _)

/-- `AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso_comm`, followed by a morphism
`s : (h_Z)_* M ⟶ M` pushed forward along `g'`. -/
lemma globalSectionsLowerStarIso_comm_map (g : Z ⟶ W) (g' : Z ⟶ W') (hW : W ⟶ W')
    (hZ : Z ⟶ Z) (comm : hZ ≫ g' = g ≫ hW) (M : Sheaf (ProEt.topology Z) A)
    (s : (hZ)_*[A].obj M ⟶ M) :
    (globalSectionsLowerStarIso A g).inv.app M ≫
        (globalSectionsLowerStarIso A hW).inv.app ((g)_*[A].obj M) ≫
          (Sheaf.Γ _ A).map ((lowerStarComp A g hW).hom.app M ≫
            (lowerStarCongr A comm.symm).hom.app M ≫ (lowerStarComp A hZ g').inv.app M ≫
              (g')_*[A].map s) ≫
            (globalSectionsLowerStarIso A g').hom.app M =
      (globalSectionsLowerStarIso A hZ).inv.app M ≫ (Sheaf.Γ _ A).map s := by
  have hnat := (globalSectionsLowerStarIso A g').hom.naturality s
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  have hcomm := globalSectionsLowerStarIso_comm A g g' hW hZ comm M
  simp only [Functor.map_comp, Category.assoc] at hcomm ⊢
  rw [hnat, reassoc_of% hcomm]

end ProEtale

end AlgebraicGeometry
