/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-!
# Composition of derived direct images on the pro-étale site

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, the total right derived direct images on
the unbounded derived categories of pro-étale sheaves satisfy

`c_{f,g} : Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`

(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp`), and these isomorphisms are unital
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_id_left`,
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_id_right`) and associative
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_assoc`). This is the finite-level clause
of blueprint `lem-weil-derived-direct-image-composition`: `f_*` is right adjoint to the exact
pullback `f^*`, so it preserves K-injective complexes, and the composition theorem for total
right derived functors (`CategoryTheory.Functor.rightDerivedFunctorCompIso'`) applies to the
underived composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*`
(`AlgebraicGeometry.ProEtale.lowerStarComp`). Identity and associativity hold because they
hold for the underived composition isomorphisms.

The first part of the file proves the corresponding coherence statements for the composition
isomorphisms of general total right derived functors on unbounded derived categories, the
unbounded counterparts of those of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`.

## Main definitions

- `CategoryTheory.Functor.rightDerivedFunctorIdIso`: `R(𝟭 C) ≅ 𝟭`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarFactor`: `Rb_* ⋙ Rc_* ≅ Ra_*` for
  `b ≫ c = a`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp`: `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarId`: `R(𝟙 X)_* ≅ 𝟭`.

## Main statements

- `CategoryTheory.Functor.rightDerivedFunctorCompIso'_assoc`
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarFactor_assoc`
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_id_left` and
  `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_id_right`
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u' u

open CategoryTheory Category Limits Abelian

open scoped CategoryTheory.Functor

namespace CategoryTheory

namespace Functor

section NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]

/-- The natural transformation `Functor.rightDerivedFunctorNatTrans τ` is characterized by its
compatibility with the units of the two right derived functors. -/
@[reassoc]
lemma rightDerivedFunctorNatTrans_app {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫
        (rightDerivedFunctorNatTrans τ).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K) ≫
        G.rightDerivedFunctorUnit.app K := by
  simp [rightDerivedFunctorNatTrans]

end NatTrans

section Composition

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The components of the composite unit `Functor.rightDerivedFunctorCompUnit`. -/
@[reassoc]
lemma rightDerivedFunctorCompUnit_app (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (rightDerivedFunctorCompUnit F G).app K =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
  have h := (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom_inv_id_app K
  rw [mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
  simp only [rightDerivedFunctorCompUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id]
  erw [h, Functor.map_id, Category.id_comp]

variable [F.PreservesKInjectiveComplexes]

/-- The composition isomorphism `Functor.rightDerivedFunctorCompIso` is characterized by its
compatibility with the units. -/
@[reassoc]
lemma rightDerivedFunctorCompIso_fac :
    (F ⋙ G).rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedFunctorCompIso F G).hom =
      rightDerivedFunctorCompUnit F G := by
  simp [rightDerivedFunctorCompIso]

/-- The pointwise form of `Functor.rightDerivedFunctorCompIso_fac`. -/
@[reassoc]
lemma rightDerivedFunctorCompIso_fac_app (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (F ⋙ G).rightDerivedFunctorUnit.app K ≫
        (rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K) =
      (rightDerivedFunctorCompUnit F G).app K :=
  NatTrans.congr_app (rightDerivedFunctorCompIso_fac F G) K

/-- The composition isomorphism `Functor.rightDerivedFunctorCompIso'` attached to
`e : F ⋙ G ≅ H` is characterized by its compatibility with the units. -/
@[reassoc]
lemma rightDerivedFunctorCompIso'_fac {H : C ⥤ E} [H.Additive] (e : F ⋙ G ≅ H) :
    rightDerivedFunctorCompUnit F G ≫ Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedFunctorCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ H.rightDerivedFunctorUnit := by
  rw [← rightDerivedFunctorCompIso_fac F G, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  exact rightDerivedNatTrans_fac _ _ _ _ (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _

/-- The pointwise form of `Functor.rightDerivedFunctorCompIso'_fac`. -/
@[reassoc]
lemma rightDerivedFunctorCompIso'_fac_app {H : C ⥤ E} [H.Additive] (e : F ⋙ G ≅ H)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) ≫
          (rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) ≫
        H.rightDerivedFunctorUnit.app K := by
  have := NatTrans.congr_app (rightDerivedFunctorCompIso'_fac F G e) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    rightDerivedFunctorCompUnit_app, Category.assoc] at this
  exact this

end Composition

section Identity

variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [HasDerivedCategory C]
  [HasKInjectiveResolutions C]

/-- The unit exhibiting the identity functor of `DerivedCategory C` as a right derived functor
of `(𝟭 C).mapHomotopyCategory ⋙ Qh`. It is an isomorphism. -/
noncomputable def rightDerivedFunctorIdUnit :
    (𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory C) :=
  Functor.whiskerRight (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh ≫
    DerivedCategory.Qh.leftUnitor.hom ≫ DerivedCategory.Qh.rightUnitor.inv

omit [HasKInjectiveResolutions C] in
@[simp]
lemma rightDerivedFunctorIdUnit_app (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (rightDerivedFunctorIdUnit C).app K = 𝟙 _ := by
  simp only [rightDerivedFunctorIdUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, comp_id,
    mapHomotopyCategoryIdIso_hom_app_eq_id]
  exact (Category.comp_id _).trans (DerivedCategory.Qh.map_id K)

omit [HasKInjectiveResolutions C] in
instance : IsIso (rightDerivedFunctorIdUnit C) := by
  dsimp only [rightDerivedFunctorIdUnit]
  infer_instance

omit [HasKInjectiveResolutions C] in
instance isRightDerivedFunctor_id_rightDerivedFunctorIdUnit :
    (𝟭 (DerivedCategory C)).IsRightDerivedFunctor (rightDerivedFunctorIdUnit C)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_inverts _ _ (asIso (rightDerivedFunctorIdUnit C)).symm

/-- **The identity functor is its own total right derived functor**: the canonical comparison
`R(𝟭 C) ≅ 𝟭` is an isomorphism. -/
noncomputable def rightDerivedFunctorIdIso :
    (𝟭 C).rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  rightDerivedUnique (𝟭 C).rightDerivedFunctor (𝟭 (DerivedCategory C))
    (𝟭 C).rightDerivedFunctorUnit (rightDerivedFunctorIdUnit C)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The characterization of `Functor.rightDerivedFunctorIdIso`. -/
@[reassoc]
lemma rightDerivedFunctorIdIso_fac_app (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (𝟭 C).rightDerivedFunctorUnit.app K ≫
        (rightDerivedFunctorIdIso C).hom.app (DerivedCategory.Qh.obj K) = 𝟙 _ := by
  have : (𝟭 C).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (rightDerivedFunctorIdIso C).hom =
        rightDerivedFunctorIdUnit C := by
    simp [rightDerivedFunctorIdIso]
  simpa using NatTrans.congr_app this K

end Identity

section Coherence

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {E' : Type*}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']
  [HasKInjectiveResolutions C]

/-- **The right unit law** for `Functor.rightDerivedFunctorCompIso'`: if `e₀ : G ≅ 𝟭`, the
composition isomorphism attached to `F ⋙ G ≅ F ⋙ 𝟭 = F` is `RF ⋙ RG ≅ RF ⋙ R𝟭 ≅ RF`. -/
lemma rightDerivedFunctorCompIso'_hom_of_iso_id_right [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ D) [F.Additive] [G.Additive] [F.PreservesKInjectiveComplexes]
    (e₀ : G ≅ 𝟭 D) :
    (rightDerivedFunctorCompIso' F G (Functor.isoWhiskerLeft F e₀ ≪≫ F.rightUnitor)).hom =
      Functor.whiskerLeft F.rightDerivedFunctor
          (rightDerivedFunctorNatIso e₀ ≪≫ rightDerivedFunctorIdIso D).hom ≫
        F.rightDerivedFunctor.rightUnitor.hom := by
  refine rightDerived_ext (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ _ _ ?_
  ext K : 2
  have h₁ := NatTrans.congr_app (rightDerivedFunctorCompIso'_fac F G
    (Functor.isoWhiskerLeft F e₀ ≪≫ F.rightUnitor)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₁
  have hnat := (rightDerivedFunctorNatIso e₀ ≪≫ rightDerivedFunctorIdIso D).hom.naturality
    (F.rightDerivedFunctorUnit.app K)
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerLeft_app, h₁,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id]
  rw [rightDerivedFunctorCompUnit_app, Category.assoc]
  erw [hnat]
  rw [← Category.assoc]
  congr 1
  rw [Iso.trans_hom (rightDerivedFunctorNatIso e₀), NatTrans.comp_app, ← Category.assoc]
  erw [rightDerivedFunctorNatTrans_app e₀.hom ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)]
  rw [Category.assoc]
  erw [rightDerivedFunctorIdIso_fac_app, Category.comp_id]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.mapHomotopyCategory_app]
  congr 1
  ext n
  exact Category.comp_id _

/-- **The left unit law** for `Functor.rightDerivedFunctorCompIso'`: if `e₀ : G ≅ 𝟭`, the
composition isomorphism attached to `G ⋙ F ≅ 𝟭 ⋙ F = F` is `RG ⋙ RF ≅ R𝟭 ⋙ RF ≅ RF`. -/
lemma rightDerivedFunctorCompIso'_hom_of_iso_id_left (G : C ⥤ C) (F : C ⥤ D)
    [F.Additive] [G.Additive] [G.PreservesKInjectiveComplexes] (e₀ : G ≅ 𝟭 C) :
    (rightDerivedFunctorCompIso' G F (Functor.isoWhiskerRight e₀ F ≪≫ F.leftUnitor)).hom =
      Functor.whiskerRight (rightDerivedFunctorNatIso e₀ ≪≫ rightDerivedFunctorIdIso C).hom
          F.rightDerivedFunctor ≫
        F.rightDerivedFunctor.leftUnitor.hom := by
  refine rightDerived_ext (G.rightDerivedFunctor ⋙ F.rightDerivedFunctor)
    (rightDerivedFunctorCompUnit G F) (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ _ _ ?_
  ext K : 2
  have h₁ := NatTrans.congr_app (rightDerivedFunctorCompIso'_fac G F
    (Functor.isoWhiskerRight e₀ F ≪≫ F.leftUnitor)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₁
  have hnat := F.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory e₀.hom (ComplexShape.up ℤ)).app K)
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerLeft_app, h₁,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  erw [Category.comp_id]
  rw [rightDerivedFunctorCompUnit_app, Category.assoc, ← Functor.map_comp,
    Iso.trans_hom (rightDerivedFunctorNatIso e₀), NatTrans.comp_app, ← Category.assoc]
  erw [rightDerivedFunctorNatTrans_app e₀.hom K]
  rw [Category.assoc]
  erw [rightDerivedFunctorIdIso_fac_app, Category.comp_id]
  erw [← hnat]
  congr 1
  rw [Functor.comp_map]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.mapHomotopyCategory_app]
  erw [Functor.mapHomotopyCategory_map]
  congr 1
  ext n
  exact Category.comp_id _

/-- **The associativity law for `Functor.rightDerivedFunctorCompIso'`**: given
isomorphisms `e₁ : F ⋙ G ≅ FG`, `e₂ : G ⋙ H ≅ GH`, `e₃ : FG ⋙ H ≅ FGH` and
`e₄ : F ⋙ GH ≅ FGH` compatible in the evident sense, the two ways of comparing
`RF ⋙ RG ⋙ RH` with `RFGH` agree. -/
lemma rightDerivedFunctorCompIso'_assoc [HasKInjectiveResolutions D] [HasKInjectiveResolutions E]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') (FG : C ⥤ E) (GH : D ⥤ E') (FGH : C ⥤ E')
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive] [FGH.Additive]
    [F.PreservesKInjectiveComplexes] [G.PreservesKInjectiveComplexes]
    [FG.PreservesKInjectiveComplexes]
    (e₁ : F ⋙ G ≅ FG) (e₂ : G ⋙ H ≅ GH) (e₃ : FG ⋙ H ≅ FGH) (e₄ : F ⋙ GH ≅ FGH)
    (hcompat : whiskerRight e₁.hom H ≫ e₃.hom = whiskerLeft F e₂.hom ≫ e₄.hom) :
    whiskerRight (rightDerivedFunctorCompIso' F G e₁).hom H.rightDerivedFunctor ≫
        (rightDerivedFunctorCompIso' FG H e₃).hom =
      whiskerLeft F.rightDerivedFunctor
          (rightDerivedFunctorCompIso' G H e₂).hom ≫
        (rightDerivedFunctorCompIso' F GH e₄).hom := by
  rw [← cancel_epi (whiskerRight (rightDerivedFunctorCompIso F G).hom
    H.rightDerivedFunctor)]
  refine rightDerived_ext ((F ⋙ G).rightDerivedFunctor ⋙ H.rightDerivedFunctor)
    (rightDerivedFunctorCompUnit (F ⋙ G) H) (HomotopyCategory.quasiIso C (.up ℤ)) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, comp_obj]
  have hCI'₁ : (rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K) ≫
      (rightDerivedFunctorCompIso' F G e₁).hom.app (DerivedCategory.Qh.obj K) =
      (rightDerivedFunctorNatTrans e₁.hom).app (DerivedCategory.Qh.obj K) := by
    have hd : (rightDerivedFunctorCompIso' F G e₁).hom =
        (rightDerivedFunctorCompIso F G).inv ≫
          rightDerivedFunctorNatTrans e₁.hom := rfl
    rw [hd, NatTrans.comp_app, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hunit := rightDerivedFunctorCompUnit_app (F ⋙ G) H K
  have hfac3 : (rightDerivedFunctorCompUnit FG H).app K ≫
      (rightDerivedFunctorCompIso' FG H e₃).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₃.hom (.up ℤ)).app K) ≫
        FGH.rightDerivedFunctorUnit.app K :=
    NatTrans.congr_app (rightDerivedFunctorCompIso'_fac FG H e₃) K
  have hfac2 : (rightDerivedFunctorCompUnit G H).app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (rightDerivedFunctorCompIso' G H e₂).hom.app
        (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₂.hom (.up ℤ)).app
          ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        GH.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) :=
    NatTrans.congr_app (rightDerivedFunctorCompIso'_fac G H e₂)
      ((F.mapHomotopyCategory (.up ℤ)).obj K)
  have hfac4 : (rightDerivedFunctorCompUnit F GH).app K ≫
      (rightDerivedFunctorCompIso' F GH e₄).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₄.hom (.up ℤ)).app K) ≫
        FGH.rightDerivedFunctorUnit.app K :=
    NatTrans.congr_app (rightDerivedFunctorCompIso'_fac F GH e₄) K
  trans DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
      (whiskerRight e₁.hom H ≫ e₃.hom) (.up ℤ)).app K) ≫ FGH.rightDerivedFunctorUnit.app K
  · have hnatH := H.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory e₁.hom (.up ℤ)).app K)
    simp only [comp_obj, comp_map] at hnatH
    have hbridge : (H.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory e₁.hom (.up ℤ)).app K) =
        (NatTrans.mapHomotopyCategory (whiskerRight e₁.hom H) (.up ℤ)).app K := rfl
    rw [← Functor.map_comp_assoc, hCI'₁, hunit, Category.assoc,
      ← Functor.map_comp_assoc, rightDerivedFunctorNatTrans_app, Functor.map_comp,
      Category.assoc, ← reassoc_of% hnatH, ← rightDerivedFunctorCompUnit_app_assoc FG H K,
      hfac3, hbridge,
      ← Functor.map_comp_assoc, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategory_comp]
  · rw [hcompat]
    have hnatCI2 := (rightDerivedFunctorCompIso' G H e₂).hom.naturality
      (F.rightDerivedFunctorUnit.app K)
    simp only [comp_obj, comp_map] at hnatCI2
    have hbridge2 : (NatTrans.mapHomotopyCategory e₂.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj K) =
        (NatTrans.mapHomotopyCategory (whiskerLeft F e₂.hom) (.up ℤ)).app K := rfl
    have hGH : H.rightDerivedFunctorUnit.app (((F ⋙ G).mapHomotopyCategory (.up ℤ)).obj K) ≫
        H.rightDerivedFunctor.map
          (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) =
        (rightDerivedFunctorCompUnit G H).app ((F.mapHomotopyCategory (.up ℤ)).obj K) :=
      (rightDerivedFunctorCompUnit_app G H ((F.mapHomotopyCategory (.up ℤ)).obj K)).symm
    rw [hunit, Category.assoc, ← Functor.map_comp_assoc,
      rightDerivedFunctorCompIso_fac_app, rightDerivedFunctorCompUnit_app,
      Functor.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hGH, reassoc_of% hnatCI2, reassoc_of% hfac2,
      ← rightDerivedFunctorCompUnit_app_assoc F GH K,
      hfac4, hbridge2,
      ← Functor.map_comp_assoc, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategory_comp]



end Coherence

end Functor

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Underived

variable {X Y Z W : Scheme.{u}}

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The left unit law for the composition isomorphisms of the pro-étale pushforwards. -/
lemma lowerStarFactor_id_left (h : Y ⟶ X) :
    lowerStarFactor A (Category.id_comp h) =
      Functor.isoWhiskerRight (lowerStarId A Y) (h)_*[A] ≪≫ ((h)_*[A]).leftUnitor := by
  ext M b
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    lowerStarFactor_hom_app_hom_app, lowerStar_map_hom_app', lowerStarId_hom_app_hom_app]
  rw [MorphismProperty.Over.pullbackComp_id_left]
  simp only [MorphismProperty.Over.pullbackCongr_refl, Iso.trans_hom, Iso.refl_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Category.id_comp]
  exact (Category.comp_id _).symm

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The right unit law for the composition isomorphisms of the pro-étale pushforwards. -/
lemma lowerStarFactor_id_right (h : Z ⟶ Y) :
    lowerStarFactor A (Category.comp_id h) =
      Functor.isoWhiskerLeft (h)_*[A] (lowerStarId A Y) ≪≫ ((h)_*[A]).rightUnitor := by
  ext M b
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    lowerStarFactor_hom_app_hom_app, lowerStarId_hom_app_hom_app, lowerStar_obj_obj_map']
  rw [MorphismProperty.Over.pullbackComp_id_right]
  simp only [MorphismProperty.Over.pullbackCongr_refl, Iso.trans_hom, Iso.refl_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Category.id_comp]
  exact (Category.comp_id _).symm

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism along `rfl : b ≫ c = b ≫ c` is `lowerStarComp`. -/
lemma lowerStarFactor_rfl (b : Z ⟶ Y) (c : Y ⟶ X) :
    lowerStarFactor A (rfl : b ≫ c = b ≫ c) = lowerStarComp A b c := by
  rw [← lowerStarComp_trans_lowerStarCongr, lowerStarCongr_rfl, Iso.trans_refl]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The associativity law for the composition isomorphisms of the pro-étale pushforwards, with
all composites named. -/
lemma lowerStarFactor_assoc (f : W ⟶ Z) (g : Z ⟶ Y) (h : Y ⟶ X) {fg : W ⟶ Y} {gh : Z ⟶ X}
    {fgh : W ⟶ X} (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh) (e₃ : fg ≫ h = fgh)
    (e₄ : f ≫ gh = fgh) :
    Functor.whiskerRight (lowerStarFactor A e₁).hom (h)_*[A] ≫ (lowerStarFactor A e₃).hom =
      Functor.whiskerLeft (f)_*[A] (lowerStarFactor A e₂).hom ≫
        (lowerStarFactor A e₄).hom := by
  subst e₁ e₂ e₃
  have key := congrArg Iso.hom (legacy_lowerStarComp_assoc A f g h)
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom] at key
  rw [lowerStarFactor_rfl, lowerStarFactor_rfl, lowerStarFactor_rfl,
    ← lowerStarComp_trans_lowerStarCongr]
  ext M : 2
  have := NatTrans.congr_app key M
  simp only [NatTrans.comp_app, Functor.associator_hom_app, Category.id_comp,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] at this
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, reassoc_of% this]
  simp [lowerStarCongr]

end Underived

section Derived

instance preservesKInjectiveComplexes_lowerStar {Y X : Scheme.{u}} (g : Y ⟶ X) :
    ((g)_*[A]).PreservesKInjectiveComplexes :=
  (ProEtale.upperStarLowerStarAdjunction A g).preservesKInjectiveComplexes

variable {X Y Z W : Scheme.{u}}

/-- The composition isomorphism `Rb_* ⋙ Rc_* ≅ Ra_*` of the total right derived pro-étale
pushforwards along a factorisation `b ≫ c = a`. -/
noncomputable def rightDerivedLowerStarFactor {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X}
    (e : b ≫ c = a) : R((b)_*[A]) ⋙ R((c)_*[A]) ≅ R((a)_*[A]) :=
  Functor.rightDerivedFunctorCompIso' (b)_*[A] (c)_*[A] (lowerStarFactor A e)

/-- Blueprint `lem-weil-derived-direct-image-composition`: Composition of derived direct images,
the finite-level clause on the pro-étale site. For `f : X ⟶ Y` and `g : Y ⟶ Z`, the canonical
isomorphism `c_{g,f} : Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of functors
`D(X_proét) ⥤ D(Z_proét)`: `f_*` preserves K-injective complexes, being right adjoint to the
exact `f^*`, so the composite of the derived functors is the derived functor of
`f_* ⋙ g_* ≅ (f ≫ g)_*`. It is natural, unital (`rightDerivedLowerStarComp_id_left`,
`rightDerivedLowerStarComp_id_right`) and associative (`rightDerivedLowerStarComp_assoc`). -/
noncomputable def rightDerivedLowerStarComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    R((f)_*[A]) ⋙ R((g)_*[A]) ≅ R((f ≫ g)_*[A]) :=
  Functor.rightDerivedFunctorCompIso' (f)_*[A] (g)_*[A] (lowerStarComp A f g)

lemma rightDerivedLowerStarComp_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightDerivedLowerStarComp A f g = rightDerivedLowerStarFactor A (rfl : f ≫ g = f ≫ g) := by
  rw [rightDerivedLowerStarFactor, lowerStarFactor_rfl, rightDerivedLowerStarComp]

variable (X) in
/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` of the total right derived pro-étale pushforward,
induced by `AlgebraicGeometry.ProEtale.lowerStarId`. -/
noncomputable def rightDerivedLowerStarId : R((𝟙 X)_*[A]) ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso (lowerStarId A X) ≪≫ Functor.rightDerivedFunctorIdIso _

/-- **The left unit law** of blueprint `lem-weil-derived-direct-image-composition`: the
composition isomorphism for `𝟙 Y ≫ g = g` is `R(𝟙)_* ≅ 𝟭` followed by the left unitor. -/
theorem rightDerivedLowerStarFactor_id_left (g : Y ⟶ X) :
    (rightDerivedLowerStarFactor A (Category.id_comp g)).hom =
      Functor.whiskerRight (rightDerivedLowerStarId A Y).hom R((g)_*[A]) ≫
        (R((g)_*[A])).leftUnitor.hom := by
  rw [rightDerivedLowerStarFactor, lowerStarFactor_id_left]
  exact Functor.rightDerivedFunctorCompIso'_hom_of_iso_id_left _ _ _

/-- **The right unit law** of blueprint `lem-weil-derived-direct-image-composition`: the
composition isomorphism for `f ≫ 𝟙 Y = f` is `R(𝟙)_* ≅ 𝟭` followed by the right unitor. -/
theorem rightDerivedLowerStarFactor_id_right (f : Z ⟶ Y) :
    (rightDerivedLowerStarFactor A (Category.comp_id f)).hom =
      Functor.whiskerLeft R((f)_*[A]) (rightDerivedLowerStarId A Y).hom ≫
        (R((f)_*[A])).rightUnitor.hom := by
  rw [rightDerivedLowerStarFactor, lowerStarFactor_id_right]
  exact Functor.rightDerivedFunctorCompIso'_hom_of_iso_id_right _ _ _

/-- **The associativity law** of blueprint `lem-weil-derived-direct-image-composition`: the two
isomorphisms `Rf_* ⋙ Rg_* ⋙ Rh_* ≅ R(f ≫ g ≫ h)_*` built from the composition isomorphisms
agree. -/
theorem rightDerivedLowerStarFactor_assoc (f : W ⟶ Z) (g : Z ⟶ Y) (h : Y ⟶ X) {fg : W ⟶ Y}
    {gh : Z ⟶ X} {fgh : W ⟶ X} (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh) (e₃ : fg ≫ h = fgh)
    (e₄ : f ≫ gh = fgh) :
    Functor.whiskerRight (rightDerivedLowerStarFactor A e₁).hom R((h)_*[A]) ≫
        (rightDerivedLowerStarFactor A e₃).hom =
      Functor.whiskerLeft R((f)_*[A]) (rightDerivedLowerStarFactor A e₂).hom ≫
        (rightDerivedLowerStarFactor A e₄).hom :=
  Functor.rightDerivedFunctorCompIso'_assoc _ _ _ _ _ _ _ _ _ _
    (lowerStarFactor_assoc A f g h e₁ e₂ e₃ e₄)

/-- The left unit law for `rightDerivedLowerStarComp`. -/
theorem rightDerivedLowerStarComp_id_left (g : Y ⟶ X) :
    (rightDerivedLowerStarComp A (𝟙 Y) g).hom ≫ eqToHom (by rw [Category.id_comp]) =
      Functor.whiskerRight (rightDerivedLowerStarId A Y).hom R((g)_*[A]) ≫
        (R((g)_*[A])).leftUnitor.hom := by
  rw [← rightDerivedLowerStarFactor_id_left, rightDerivedLowerStarComp_eq]
  generalize_proofs h₁ h₂
  have : ∀ {a : Y ⟶ X} (e : 𝟙 Y ≫ g = a),
      (rightDerivedLowerStarFactor A (rfl : 𝟙 Y ≫ g = 𝟙 Y ≫ g)).hom ≫
        eqToHom (by rw [e]) = (rightDerivedLowerStarFactor A e).hom := by
    rintro _ rfl
    simp
  exact this _

/-- The right unit law for `rightDerivedLowerStarComp`. -/
theorem rightDerivedLowerStarComp_id_right (f : Z ⟶ Y) :
    (rightDerivedLowerStarComp A f (𝟙 Y)).hom ≫ eqToHom (by rw [Category.comp_id]) =
      Functor.whiskerLeft R((f)_*[A]) (rightDerivedLowerStarId A Y).hom ≫
        (R((f)_*[A])).rightUnitor.hom := by
  rw [← rightDerivedLowerStarFactor_id_right, rightDerivedLowerStarComp_eq]
  have : ∀ {a : Z ⟶ Y} (e : f ≫ 𝟙 Y = a),
      (rightDerivedLowerStarFactor A (rfl : f ≫ 𝟙 Y = f ≫ 𝟙 Y)).hom ≫
        eqToHom (by rw [e]) = (rightDerivedLowerStarFactor A e).hom := by
    rintro _ rfl
    simp
  exact this _

/-- The associativity law for `rightDerivedLowerStarComp`. -/
theorem rightDerivedLowerStarComp_assoc (f : W ⟶ Z) (g : Z ⟶ Y) (h : Y ⟶ X) :
    Functor.whiskerRight (rightDerivedLowerStarComp A f g).hom R((h)_*[A]) ≫
        (rightDerivedLowerStarComp A (f ≫ g) h).hom =
      Functor.whiskerLeft R((f)_*[A]) (rightDerivedLowerStarComp A g h).hom ≫
        (rightDerivedLowerStarComp A f (g ≫ h)).hom ≫
          eqToHom (by rw [Category.assoc]) := by
  simp only [rightDerivedLowerStarComp_eq]
  rw [rightDerivedLowerStarFactor_assoc A f g h rfl rfl rfl (Category.assoc f g h).symm]
  have : ∀ {a : W ⟶ X} (e : f ≫ g ≫ h = a),
      (rightDerivedLowerStarFactor A (rfl : f ≫ g ≫ h = f ≫ g ≫ h)).hom ≫
        eqToHom (by rw [e]) = (rightDerivedLowerStarFactor A e).hom := by
    rintro _ rfl
    simp
  rw [this]

end Derived

end AlgebraicGeometry.ProEtale
