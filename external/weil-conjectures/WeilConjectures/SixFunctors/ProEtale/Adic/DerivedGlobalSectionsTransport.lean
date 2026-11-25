/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# Transport of derived global sections of `ℚ̄_ℓ` along isomorphisms of schemes

An isomorphism `e : Z ≅ W` of schemes induces an isomorphism
`RΓ(Z, ℚ̄_ℓ) ≅ RΓ(W, ℚ̄_ℓ)` of derived global sections of the constant `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.derivedGlobalSectionsUnitIso`): the pushforward `e_*` is an exact
equivalence, `Γ(W, e_* M) ≅ Γ(Z, M)`, and `e_* ℚ̄_ℓ,Z ≅ ℚ̄_ℓ,W`. This transport is compatible with
composition (`AlgebraicGeometry.ProEtale.derivedGlobalSectionsUnitIso_trans`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The global sections `Γ(Z, -)` of sheaves of modules over the constant `ℓ`-adic sheaf. -/
noncomputable abbrev adicGlobalSections (Z : Scheme.{u}) : AdicSheaf l Z ⥤ WeilCoefficients.{u} l :=
  AdicSheaf.forget Z ⋙ Sheaf.Γ _ _

instance (Z : Scheme.{u}) : (adicGlobalSections l Z).Additive := by
  unfold adicGlobalSections
  infer_instance

/-- The invariance `Γ(W, g_* M) ≅ Γ(Z, M)` of global sections under pushforward, for sheaves of
modules over the constant `ℓ`-adic sheaves. -/
noncomputable def adicLowerStarCompGlobalSectionsIso {Z W : Scheme.{u}} (g : Z ⟶ W) :
    (g)_*ᵃ[l] ⋙ adicGlobalSections l W ≅ adicGlobalSections l Z :=
  Functor.isoWhiskerLeft (AdicSheaf.forget Z) (globalSectionsLowerStarIso _ g)

/-- The invariance of global sections under pushforward is compatible with composition. -/
lemma adicLowerStarCompGlobalSectionsIso_hom_app_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (M : AdicSheaf l T) :
    (adicLowerStarCompGlobalSectionsIso l (h₁ ≫ h₂)).hom.app M =
      (adicGlobalSections l R).map ((adicLowerStarComp l h₁ h₂).inv.app M) ≫
        (adicLowerStarCompGlobalSectionsIso l h₂).hom.app ((h₁)_*ᵃ[l].obj M) ≫
        (adicLowerStarCompGlobalSectionsIso l h₁).hom.app M := by
  change (globalSectionsLowerStarIso _ (h₁ ≫ h₂)).hom.app M.X =
    (Sheaf.Γ _ _).map ((lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).inv.app M.X) ≫
      (globalSectionsLowerStarIso _ h₂).hom.app _ ≫ (globalSectionsLowerStarIso _ h₁).hom.app M.X
  rw [← globalSectionsLowerStarIso_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The invariance of global sections under pushforward along equal morphisms. -/
lemma adicLowerStarCompGlobalSectionsIso_hom_app_congr {Z W : Scheme.{u}} {g g' : Z ⟶ W}
    (h : g = g') (M : AdicSheaf l Z) :
    (adicGlobalSections l W).map ((adicLowerStarCongr l h).hom.app M) ≫
        (adicLowerStarCompGlobalSectionsIso l g').hom.app M =
      (adicLowerStarCompGlobalSectionsIso l g).hom.app M :=
  globalSectionsLowerStarIso_congr _ h M.X

/-- The invariance of global sections under pushforward is compatible with the identification of
the pushforwards along the two sides `a ≫ b = c ≫ d` of a commutative square. -/
lemma adicLowerStarCompGlobalSectionsIso_inv_app_comm {Z₁ Z₂ Z₃ Z₄ : Scheme.{u}} (a : Z₁ ⟶ Z₂)
    (b : Z₂ ⟶ Z₄) (c : Z₁ ⟶ Z₃) (d : Z₃ ⟶ Z₄) (hc : a ≫ b = c ≫ d) (M : AdicSheaf l Z₁) :
    (adicLowerStarCompGlobalSectionsIso l b).inv.app ((a)_*ᵃ[l].obj M) ≫
        (adicGlobalSections l Z₄).map ((adicLowerStarComp l a b ≪≫ adicLowerStarCongr l hc ≪≫
          (adicLowerStarComp l c d).symm).hom.app M) ≫
        (adicLowerStarCompGlobalSectionsIso l d).hom.app ((c)_*ᵃ[l].obj M) =
      (adicLowerStarCompGlobalSectionsIso l a).hom.app M ≫
        (adicLowerStarCompGlobalSectionsIso l c).inv.app M := by
  have h₁ := adicLowerStarCompGlobalSectionsIso_hom_app_comp l a b M
  have h₂ := adicLowerStarCompGlobalSectionsIso_hom_app_comp l c d M
  have h₃ := adicLowerStarCompGlobalSectionsIso_hom_app_congr l hc M
  rw [← cancel_mono ((adicLowerStarCompGlobalSectionsIso l c).hom.app M)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rw [← h₂, h₃]
  rw [← cancel_epi ((adicLowerStarCompGlobalSectionsIso l b).hom.app ((a)_*ᵃ[l].obj M)),
    Iso.hom_inv_id_app_assoc]
  rw [h₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The identifications `e_* ℚ̄_ℓ ≅ ℚ̄_ℓ` along isomorphisms are compatible with composition. -/
lemma adicLowerStar_map_adicLowerStarUnitIso_hom {X Y Z : Scheme.{u}} (e : X ≅ Y) (e' : Y ≅ Z) :
    (e'.hom)_*ᵃ[l].map (adicLowerStarUnitIso l e).hom ≫ (adicLowerStarUnitIso l e').hom =
      (adicLowerStarComp l e.hom e'.hom).hom.app _ ≫ (adicLowerStarUnitIso l (e ≪≫ e')).hom := by
  refine Mod.hom_ext _ _ ?_
  change (e'.hom)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l e).hom ≫
      (adicConstantSheafLowerStarIso l e').hom =
    (lowerStarComp (WeilCoefficients.{u} l) e.hom e'.hom).hom.app _ ≫
      (adicConstantSheafLowerStarIso l (e ≪≫ e')).hom
  have key : (adicConstantSheafLowerStarIso l e').inv ≫
      (e'.hom)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l e).inv ≫
      (lowerStarComp (WeilCoefficients.{u} l) e.hom e'.hom).hom.app _ =
      (adicConstantSheafLowerStarIso l (e ≪≫ e')).inv :=
    adicConstantSheafToLowerStar_comp l e.hom e'.hom
  rw [← cancel_epi ((adicConstantSheafLowerStarIso l e').inv ≫
    (e'.hom)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l e).inv)]
  simp only [Category.assoc]
  rw [reassoc_of% key, Iso.inv_hom_id, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

/-- The derived global sections `RΓ(Z, ℚ̄_ℓ)` of the constant `ℓ`-adic sheaf. -/
noncomputable abbrev derivedGlobalSectionsUnit (Z : Scheme.{u}) :
    DerivedCategory (WeilCoefficients.{u} l) :=
  (adicGlobalSections l Z).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l Z))

/-- **Transport of derived global sections along an isomorphism**: an isomorphism `e : Z ≅ W`
induces `RΓ(Z, ℚ̄_ℓ) ≅ RΓ(W, e_* ℚ̄_ℓ) ≅ RΓ(W, ℚ̄_ℓ)`. -/
noncomputable def derivedGlobalSectionsUnitIso {Z W : Scheme.{u}} (e : Z ≅ W) :
    derivedGlobalSectionsUnit l Z ≅ derivedGlobalSectionsUnit l W :=
  (Functor.rightDerivedFunctorIsoMapDerivedCategoryComp
      (adicLowerStarCompGlobalSectionsIso l e.hom)).app _ ≪≫
    (adicGlobalSections l W).rightDerivedFunctor.mapIso
      (((e.hom)_*ᵃ[l].mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (adicLowerStarUnitIso l e))

/-- The transport of derived global sections is compatible with composition. -/
lemma derivedGlobalSectionsUnitIso_trans {X Y Z : Scheme.{u}} (e : X ≅ Y) (e' : Y ≅ Z) :
    derivedGlobalSectionsUnitIso l (e ≪≫ e') =
      derivedGlobalSectionsUnitIso l e ≪≫ derivedGlobalSectionsUnitIso l e' := by
  have hA := Functor.rightDerivedFunctorIsoMapDerivedCategoryComp_hom_app_comp
    (adicLowerStarCompGlobalSectionsIso l e.hom) (adicLowerStarCompGlobalSectionsIso l e'.hom)
    (adicLowerStarCompGlobalSectionsIso l (e.hom ≫ e'.hom)) (adicLowerStarComp l e.hom e'.hom)
    (adicLowerStarCompGlobalSectionsIso_hom_app_comp l e.hom e'.hom)
    ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l X))
  have hS := Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor (e.hom)_*ᵃ[l]
    (e'.hom)_*ᵃ[l] (e.hom ≫ e'.hom)_*ᵃ[l] (adicLowerStarComp l e.hom e'.hom).symm
    (AdicSheaf.unit l X)
  have hU := adicLowerStar_map_adicLowerStarUnitIso_hom l e e'
  have key : ((e.hom ≫ e'.hom)_*ᵃ[l].mapDerivedCategorySingleFunctor 0).hom.app
        (AdicSheaf.unit l X) ≫
      (DerivedCategory.singleFunctor _ 0).map (adicLowerStarUnitIso l (e ≪≫ e')).hom =
      ((Functor.mapDerivedCategoryNatIso (adicLowerStarComp l e.hom e'.hom).symm).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l X)) ≫
        (Functor.mapDerivedCategoryCompIso (e.hom)_*ᵃ[l] (e'.hom)_*ᵃ[l]).inv.app
          ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l X))) ≫
      (e'.hom)_*ᵃ[l].mapDerivedCategory.map
          (((e.hom)_*ᵃ[l].mapDerivedCategorySingleFunctor 0).hom.app (AdicSheaf.unit l X) ≫
            (DerivedCategory.singleFunctor _ 0).map (adicLowerStarUnitIso l e).hom) ≫
        ((e'.hom)_*ᵃ[l].mapDerivedCategorySingleFunctor 0).hom.app (AdicSheaf.unit l Y) ≫
          (DerivedCategory.singleFunctor _ 0).map (adicLowerStarUnitIso l e').hom := by
    simp only [Functor.map_comp, Category.assoc]
    erw [((e'.hom)_*ᵃ[l].mapDerivedCategorySingleFunctor 0).hom.naturality_assoc]
    rw [reassoc_of% hS]
    simp only [Functor.comp_map, ← Functor.map_comp]
    congr 1
    rw [hU, Iso.symm_hom, Iso.inv_hom_id_app_assoc]
  ext
  simp only [derivedGlobalSectionsUnitIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  erw [(Functor.rightDerivedFunctorIsoMapDerivedCategoryComp
    (adicLowerStarCompGlobalSectionsIso l e'.hom)).hom.naturality_assoc]
  erw [reassoc_of% hA]
  congr 1
  rw [key]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]

/-- The transport of derived global sections along the identity is the identity. -/
@[simp]
lemma derivedGlobalSectionsUnitIso_refl (Z : Scheme.{u}) :
    derivedGlobalSectionsUnitIso l (Iso.refl Z) = Iso.refl _ := by
  have h := congrArg Iso.hom (derivedGlobalSectionsUnitIso_trans l (Iso.refl Z) (Iso.refl Z))
  rw [Iso.refl_trans, Iso.trans_hom] at h
  ext
  rw [← cancel_epi (derivedGlobalSectionsUnitIso l (Iso.refl Z)).hom, ← h, Iso.refl_hom,
    Category.comp_id]

end AlgebraicGeometry.ProEtale
