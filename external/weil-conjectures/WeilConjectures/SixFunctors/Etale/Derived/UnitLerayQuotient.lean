/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-!
# The derived unit on global sections, computed on complexes

For a morphism of schemes `f : Y ⟶ X` and a complex `K` of étale sheaves on `X`, the derived
global sections of the unit `K ⟶ Rf_* f^* K`, followed by the Leray isomorphism
`RΓ(X, Rf_* -) ≅ RΓ(Y, -)`, is computed, after precomposition with the canonical map
`Γ(X, K) ⟶ RΓ(X, K)`, by the morphism of complexes `Γ(X, K) ⟶ Γ(Y, f^* K)` given degreewise by
the pullback of global sections `AlgebraicGeometry.Etale.globalSectionsUpperStarMap`
(`AlgebraicGeometry.Etale.rightDerivedGlobalSections_map_unit_quotient`).

This generalizes to an arbitrary coefficient category the corresponding computation for abelian
groups in `WeilConjectures.AlgebraicGeometry.DerivedSectionSingleUnit`.

## Main definitions

- `AlgebraicGeometry.Etale.globalSectionsUpperStarNatTrans`: the pullback of global sections
  as a natural transformation `Γ(X, -) ⟶ f^* ⋙ Γ(Y, -)`.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The pullback of global sections `Γ(X, G) ⟶ Γ(Y, f^* G)` along `f : Y ⟶ X`, as a natural
transformation: the unit `G ⟶ f_* f^* G` followed by `Γ(X, f_* -) ≅ Γ(Y, -)`. -/
noncomputable def globalSectionsUpperStarNatTrans {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Sheaf.Γ X.smallEtaleTopology A ⟶ (f)^*[A] ⋙ Sheaf.Γ Y.smallEtaleTopology A :=
  Functor.whiskerRight (upperStarLowerStarAdjunction A f).unit (Sheaf.Γ X.smallEtaleTopology A) ≫
    Functor.whiskerLeft (f)^*[A] (lowerStarCompGlobalSectionsIso A f).hom

/-- The components of `AlgebraicGeometry.Etale.globalSectionsUpperStarNatTrans` are the
pullbacks of global sections. -/
lemma globalSectionsUpperStarNatTrans_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Sheaf X.smallEtaleTopology A) :
    (globalSectionsUpperStarNatTrans A f).app M = globalSectionsUpperStarMap A f M := by
  dsimp only [globalSectionsUpperStarNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, lowerStarCompGlobalSectionsIso, Functor.isoWhiskerLeft_hom,
    Iso.trans_hom, Iso.symm_hom]
  erw [← Category.assoc, (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    A terminalIsTerminal).hom.naturality
      ((upperStarLowerStarAdjunction A f).unit.app M)]
  simp [globalSectionsUpperStarMap, lowerStarCompSheafSectionsTerminalIso]

/-- The Leray comparison carries the composite derived unit to the unit on `Y`. -/
lemma rightDerivedFunctorCompUnit_lowerStar_leray {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Functor.rightDerivedFunctorCompUnit ((f)_*[A]) (Sheaf.Γ X.smallEtaleTopology A) ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom =
    Functor.whiskerRight
        (NatTrans.mapHomotopyCategory (lowerStarCompGlobalSectionsIso A f).hom (.up ℤ))
        DerivedCategory.Qh ≫
      (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorUnit := by
  let F := (f)_*[A]
  let G := Sheaf.Γ X.smallEtaleTopology A
  have hcomp : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [← hcomp, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [rightDerivedLowerStarCompRightDerivedGlobalSectionsIso,
    Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
  dsimp only [F, G]
  rw [Iso.hom_inv_id_assoc]
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso (Sheaf Y.smallEtaleTopology A) (.up ℤ)) _

/-- The derived global sections of the derived unit, followed by the Leray isomorphism, on an
object of the homotopy category. -/
lemma rightDerivedGlobalSections_map_unit_homotopyCategory {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorUnit.app K ≫
        (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.map
          ((upperStarLowerStarAdjunction A f).mapDerivedCategoryRightDerivedAdjunction.unit.app
            (DerivedCategory.Qh.obj K)) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.app
            (((f)^*[A]).mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
        (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctor.map
          (((f)^*[A]).mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map
        (((Sheaf.Γ X.smallEtaleTopology A).mapHomotopyCategory (.up ℤ)).map
            (((upperStarLowerStarAdjunction A f).mapHomotopyCategory (.up ℤ)).unit.app K) ≫
          (NatTrans.mapHomotopyCategory (lowerStarCompGlobalSectionsIso A f).hom (.up ℤ)).app
            ((((f)^*[A]).mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorUnit.app
          ((((f)^*[A]).mapHomotopyCategory (.up ℤ)).obj K) := by
  let L := (f)^*[A]
  let F := (f)_*[A]
  let G := Sheaf.Γ X.smallEtaleTopology A
  let a := upperStarLowerStarAdjunction A f
  let T := (L.mapHomotopyCategory (.up ℤ)).obj K
  have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    F.rightDerivedFunctorUnit K
  have hn := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app K)
  have hg := G.rightDerivedFunctorUnit.naturality
    ((a.mapHomotopyCategory (.up ℤ)).unit.app K)
  have hc := NatTrans.congr_app (rightDerivedFunctorCompUnit_lowerStar_leray A f) T
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  dsimp only [Functor.comp_map] at hn hg
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hc
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hc
  erw [hi, DerivedCategory.Qh.map_id, Category.id_comp] at hc
  erw [← hn]
  erw [← Functor.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hg, hc, ← DerivedCategory.Qh.map_comp_assoc]

/-- **The derived unit on global sections, on a complex.** For a complex `K` of étale sheaves
on `X`, the derived global sections of the unit `K ⟶ Rf_* f^* K` followed by the Leray
isomorphism and `RΓ(Y, f^* K) ≅ RΓ(Y, f^* K)` is, after precomposition with
`Γ(X, K) ⟶ RΓ(X, K)`, the morphism of complexes `Γ(X, K) ⟶ Γ(Y, f^* K)` given degreewise by the
pullback of global sections, followed by `Γ(Y, f^* K) ⟶ RΓ(Y, f^* K)`. -/
lemma rightDerivedGlobalSections_map_unit_quotient {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj K) ≫
        (rightDerivedGlobalSections A X).map
          ((mapDerivedUpperStarLowerStarAdjunction A f).unit.app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.app
            (((f)^*[A]).mapDerivedCategory.obj
              (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) ≫
        (rightDerivedGlobalSections A Y).map
          (((f)^*[A]).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ _).obj K)) =
      (DerivedCategory.quotientCompQhIso A).hom.app
          (((Sheaf.Γ X.smallEtaleTopology A).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (globalSectionsUpperStarNatTrans A f) (.up ℤ)).app K) ≫
        (DerivedCategory.quotientCompQhIso A).inv.app
          (((Sheaf.Γ Y.smallEtaleTopology A).mapHomologicalComplex (.up ℤ)).obj
            (((f)^*[A]).mapHomologicalComplex (.up ℤ) |>.obj K)) ≫
        (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj (((f)^*[A]).mapHomologicalComplex _ |>.obj K)) := by
  refine (rightDerivedGlobalSections_map_unit_homotopyCategory A f _).trans ?_
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  erw [Iso.hom_inv_id_app_assoc]
  congr 1

end AlgebraicGeometry.Etale
