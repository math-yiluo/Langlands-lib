/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# Unit laws for the derived pullback

The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` (`AlgebraicGeometry.Etale.leftDerivedUpperStarId`) and
the composition isomorphisms `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) satisfy the two unit laws. Both are
checked on the image of the homotopy category, where they are the unit laws
`AlgebraicGeometry.Etale.upperStarComp_id_left` and `AlgebraicGeometry.Etale.upperStarComp_id_right`
of the underived pullbacks, read through the counits of the derived pullbacks.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStarId`: `L(𝟙 X)^* ≅ 𝟭`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarCompSectionIso`: `Lp^* ⋙ Ls^* ≅ 𝟭` for
  `s ≫ p = 𝟙`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_id_left_hom_app`
- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_id_right_hom_app`
- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_comp_compSectionIso`: restricting along a
  section commutes with base change.
- `AlgebraicGeometry.Etale.sectionRestrictionIso`: reading a local trivialization at a section.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

open _root_.DerivedCategory

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback on étale sheaves. -/
noncomputable def leftDerivedUpperStarId (X : Scheme.{u}) : L((𝟙 X)^*[A]) ≅ 𝟭 _ :=
  -- the derived functor of `Etale.upperStarId`, followed by `L(𝟭) ≅ D(𝟭) ≅ 𝟭`
  Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId A X) ≪≫
    (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- For a section `s` of `p`, pulling back along `p` and then along `s` is the identity:
`Lp^* ⋙ Ls^* ≅ L(s ≫ p)^* = L(𝟙)^* ≅ 𝟭`. -/
noncomputable def leftDerivedUpperStarCompSectionIso {X Y : Scheme.{u}} (s : Y ⟶ X) (p : X ⟶ Y)
    (h : s ≫ p = 𝟙 Y) : L((p)^*[A]) ⋙ L((s)^*[A]) ≅ 𝟭 _ :=
  (leftDerivedUpperStarComp A s p (𝟙 Y) h.symm).symm ≪≫ leftDerivedUpperStarId A Y

variable {X : Scheme.{u}}

/-- On the image `Qh P` of a complex, the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` is the identity
isomorphism of the underived pullback, through the counit of the derived pullback. -/
lemma leftDerivedUpperStarId_hom_app_Qh_obj
    (P : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (leftDerivedUpperStarId A X).hom.app (Qh.obj P) =
      (𝟙 X)^*[A].leftDerivedFunctorCounit.app P ≫
        Qh.map ((NatTrans.mapHomotopyCategory (Etale.upperStarId A X).hom (.up ℤ)).app P ≫
          (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app P) := by
  have hfac := NatTrans.congr_app
    (𝟙 X)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac P
  have hnat := Functor.mapDerivedCategoryNatIso_fach (Etale.upperStarId A X) P
  have hid := NatTrans.congr_app (congrArg Iso.hom
    (Functor.mapDerivedCategoryIdIso_factorsh (Sheaf X.smallEtaleTopology A))) P
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hfac hid
  simp only [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hfac, Category.assoc, Functor.map_comp]
  congr 1
  have hid' : (Functor.mapDerivedCategoryIdIso (Sheaf X.smallEtaleTopology A)).hom.app (Qh.obj P) =
      (𝟭 (Sheaf X.smallEtaleTopology A)).mapDerivedCategoryFactorsh.hom.app P ≫
        Qh.map ((Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app P) := by
    erw [Category.comp_id, Category.comp_id] at hid
    exact hid
  rw [hid', reassoc_of% hnat]

variable {Y : Scheme.{u}}

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The right unit law for the composition isomorphisms of the underived pullbacks, on the
homotopy category. -/
lemma mapHomotopyCategoryCompHom_upperStarComp_id_right (h : Y ⟶ X)
    (P : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    Functor.mapHomotopyCategoryCompHom (𝟙 X)^*[A] (h)^*[A] (h)^*[A]
        (upperStarComp A h (𝟙 X) h (Category.comp_id h).symm) P ≫
      ((h)^*[A].mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (Etale.upperStarId A X).hom (.up ℤ)).app P ≫
          (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app P) = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj,
    Functor.mapHomotopyCategoryIdIso_hom_app]
  have hnt : (NatTrans.mapHomotopyCategory (Etale.upperStarId A X).hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (Etale.upperStarId A X).hom (.up ℤ)).app K) := rfl
  rw [hnt, ← Functor.map_comp, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  have hK : (𝟙 X)^*[A].mapHomologicalComplexCompHom (h)^*[A] (h)^*[A]
        (upperStarComp A h (𝟙 X) h (Category.comp_id h).symm) K ≫
      ((h)^*[A].mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (Etale.upperStarId A X).hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app K) = 𝟙 _ := by
    ext n : 1
    simp only [Functor.mapHomologicalComplexCompHom, Etale.upperStarComp_id_right]
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      Functor.mapHomologicalComplex_map_f, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
      HomologicalComplex.id_f, Category.id_comp, Category.assoc]
    erw [Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
    exact (h)^*[A].map_id _
  rw [hK]
  exact (HomotopyCategory.quotient _ (.up ℤ)).map_id _

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The left unit law for the composition isomorphisms of the underived pullbacks, on the
homotopy category. -/
lemma mapHomotopyCategoryCompHom_upperStarComp_id_left (p : Y ⟶ X)
    (P : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    Functor.mapHomotopyCategoryCompHom (p)^*[A] (𝟙 Y)^*[A] (p)^*[A]
        (upperStarComp A (𝟙 Y) p p (Category.id_comp p).symm) P ≫
      (NatTrans.mapHomotopyCategory (Etale.upperStarId A Y).hom (.up ℤ)).app
          (((p)^*[A].mapHomotopyCategory (.up ℤ)).obj P) ≫
        (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app
          (((p)^*[A].mapHomotopyCategory (.up ℤ)).obj P) = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj]
  erw [Functor.mapHomotopyCategoryIdIso_hom_app]
  have hnt : (NatTrans.mapHomotopyCategory (Etale.upperStarId A Y).hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (((p)^*[A].mapHomologicalComplex (.up ℤ)).obj K)) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (Etale.upperStarId A Y).hom (.up ℤ)).app
          (((p)^*[A].mapHomologicalComplex (.up ℤ)).obj K)) := rfl
  erw [hnt, ← Functor.map_comp]
  have hK : (p)^*[A].mapHomologicalComplexCompHom (𝟙 Y)^*[A] (p)^*[A]
        (upperStarComp A (𝟙 Y) p p (Category.id_comp p).symm) K ≫
      (NatTrans.mapHomologicalComplex (Etale.upperStarId A Y).hom (.up ℤ)).app
          (((p)^*[A].mapHomologicalComplex (.up ℤ)).obj K) ≫
        (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app
          (((p)^*[A].mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := by
    ext n : 1
    simp only [Functor.mapHomologicalComplexCompHom, Etale.upperStarComp_id_left]
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app,
      HomologicalComplex.id_f, Category.id_comp, Category.assoc]
    erw [Category.id_comp, Iso.inv_hom_id_app_assoc]
    rfl
  refine (congrArg (HomotopyCategory.quotient _ (.up ℤ)).map hK).trans ?_
  exact (HomotopyCategory.quotient _ (.up ℤ)).map_id _

/-- **The right unit law** for the composition isomorphisms of the derived pullbacks:
`L(h ≫ 𝟙)^* ≅ L(𝟙)^* ⋙ Lh^*` followed by `L(𝟙)^* ≅ 𝟭` is the identity. -/
@[reassoc]
lemma leftDerivedUpperStarComp_id_right_hom_app (h : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A h (𝟙 X) h (Category.comp_id h).symm).hom.app K ≫
      L((h)^*[A]).map ((leftDerivedUpperStarId A X).hom.app K) = 𝟙 _ := by
  suffices H : (leftDerivedUpperStarComp A h (𝟙 X) h (Category.comp_id h).symm).hom ≫
      Functor.whiskerRight (leftDerivedUpperStarId A X).hom L((h)^*[A]) =
        (Functor.leftUnitor _).inv from NatTrans.congr_app H K
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app]
  rw [← cancel_mono ((h)^*[A].leftDerivedFunctorCounit.app P),
    leftDerivedUpperStarId_hom_app_Qh_obj, Functor.map_comp, Category.assoc, Category.assoc]
  erw [counit_naturality A h]
  rw [leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit_assoc,
    ← Functor.map_comp, mapHomotopyCategoryCompHom_upperStarComp_id_right]
  erw [Qh.map_id, Category.comp_id, Category.id_comp]

/-- **The left unit law** for the composition isomorphisms of the derived pullbacks:
`L(𝟙 ≫ p)^* ≅ Lp^* ⋙ L(𝟙)^*` followed by `L(𝟙)^* ≅ 𝟭` is the identity. -/
@[reassoc]
lemma leftDerivedUpperStarComp_id_left_hom_app (p : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A (𝟙 Y) p p (Category.id_comp p).symm).hom.app K ≫
      (leftDerivedUpperStarId A Y).hom.app (L((p)^*[A]).obj K) = 𝟙 _ := by
  suffices H : (leftDerivedUpperStarComp A (𝟙 Y) p p (Category.id_comp p).symm).hom ≫
      Functor.whiskerLeft L((p)^*[A]) (leftDerivedUpperStarId A Y).hom =
        (Functor.rightUnitor _).inv from NatTrans.congr_app H K
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app]
  have hn := (leftDerivedUpperStarId A Y).hom.naturality ((p)^*[A].leftDerivedFunctorCounit.app P)
  simp only [Functor.id_map, Functor.comp_obj] at hn
  rw [← cancel_mono ((p)^*[A].leftDerivedFunctorCounit.app P), Category.assoc, ← hn,
    leftDerivedUpperStarId_hom_app_Qh_obj,
    leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit_assoc]
  rw [← Functor.map_comp, mapHomotopyCategoryCompHom_upperStarComp_id_left, Qh.map_id,
    Category.comp_id,
    Category.id_comp]


/-- **Sections commute with base change.** Let `a : P ⟶ B` have a section `i`, let `a' : P' ⟶ B'`
have a section `i'`, and let `v : P' ⟶ P` lie over `u : B' ⟶ B` and carry `i'` to `i`. Then the
two identifications `Li'^* Lv^* La^* C ≅ Lu^* C` — through `Lv^* La^* ≅ La'^* Lu^*` and
`Li'^* La'^* ≅ 𝟭`, or through `Li'^* Lv^* ≅ Lu^* Li^*` and `Li^* La^* ≅ 𝟭` — agree, i.e. the
square
```
Li'^* Lv^* La^* C --(Lv^* La^* ≅ La'^* Lu^*)--> Li'^* La'^* Lu^* C
        |                                               |
(Li'^* Lv^* ≅ Lu^* Li^*)                         (Li'^* La'^* ≅ 𝟭)
        v                                               v
Lu^* Li^* La^* C ------------(Li^* La^* ≅ 𝟭)-----------> Lu^* C
```
commutes. -/
lemma leftDerivedUpperStar_map_comp_compSectionIso {B B' P P' : Scheme.{u}} (u : B' ⟶ B)
    (a : P ⟶ B) (a' : P' ⟶ B') (v : P' ⟶ P) (i : B ⟶ P) (i' : B' ⟶ P')
    (hv : v ≫ a = a' ≫ u) (hi : i' ≫ v = u ≫ i) (h : i ≫ a = 𝟙 B) (h' : i' ≫ a' = 𝟙 B')
    (C : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A)) :
    L((i')^*[A]).map ((leftDerivedUpperStarComp A v a).inv.app C ≫
          (leftDerivedUpperStarComp A a' u (v ≫ a) hv).hom.app C) ≫
        (leftDerivedUpperStarCompSectionIso A i' a' h').hom.app _ =
      ((leftDerivedUpperStarComp A i' v).inv.app _ ≫
          (leftDerivedUpperStarComp A u i (i' ≫ v) hi).hom.app _) ≫
        L((u)^*[A]).map ((leftDerivedUpperStarCompSectionIso A i a h).hom.app C) := by
  have hu : u = i' ≫ v ≫ a := by rw [hv, ← Category.assoc, h', Category.id_comp]
  -- the three associativity squares and the two unit laws
  have A1 := leftDerivedUpperStarComp_assoc'_app A i' a' u (𝟙 B') (v ≫ a) u h'.symm hv
    (Category.id_comp u).symm C
  have A2 := leftDerivedUpperStarComp_assoc'_app A i' v a (i' ≫ v) (v ≫ a) u rfl rfl
    (by rw [hu, Category.assoc]) C
  have A3 := leftDerivedUpperStarComp_assoc'_app A u i a (i' ≫ v) (𝟙 B) u hi h.symm
    (by rw [hu, Category.assoc]) C
  have UL := leftDerivedUpperStarComp_id_left_hom_app A u C
  have UR := leftDerivedUpperStarComp_id_right_hom_app A u C
  rw [← cancel_epi ((leftDerivedUpperStarComp A i' (v ≫ a) u hu).hom.app C ≫
    L((i')^*[A]).map ((leftDerivedUpperStarComp A v a).hom.app C))]
  simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp,
    reassoc_of% A1, Iso.hom_inv_id_app_assoc, UL, reassoc_of% A2, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% A3, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, UR]

section SectionRestriction

variable {B B' P P' : Scheme.{u}} (u : B' ⟶ B) {a : P ⟶ B} {a' : P' ⟶ B'} (v : P' ⟶ P)
  {i : B ⟶ P} {i' : B' ⟶ P'} (hi : i' ≫ v = u ≫ i) (h' : i' ≫ a' = 𝟙 B')

/-- *Reading a local trivialization at a section.* Let `v : P' ⟶ P` lie over `u : B' ⟶ B`, let
`i, i'` be sections of `a : P ⟶ B` and `a' : P' ⟶ B'` with `i' ≫ v = u ≫ i`, and let
`F ∈ D(P)` be trivialized over `P'` as `e : Lv^* F ≅ La'^* C₀`. An identification
`θ : Li^* F ≅ C` of the fibre of `F` along `i` gives `Lu^* C ≅ C₀`: restrict `e` along `i'`. -/
noncomputable def sectionRestrictionIso {F : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A)}
    {C : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A)}
    {C₀ : _root_.DerivedCategory (Sheaf B'.smallEtaleTopology A)} (θ : L((i)^*[A]).obj F ≅ C)
    (e : L((v)^*[A]).obj F ≅ L((a')^*[A]).obj C₀) : L((u)^*[A]).obj C ≅ C₀ :=
  (((leftDerivedUpperStarComp A i' v).app F).symm ≪≫
      (leftDerivedUpperStarComp A u i (i' ≫ v) hi).app F ≪≫ L((u)^*[A]).mapIso θ).symm ≪≫
    L((i')^*[A]).mapIso e ≪≫ (leftDerivedUpperStarCompSectionIso A i' a' h').app C₀

variable {F : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A)}
  {C : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A)}
  {C₀ : _root_.DerivedCategory (Sheaf B'.smallEtaleTopology A)}

lemma sectionRestrictionIso_trans_left {C' : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A)}
    (θ : L((i)^*[A]).obj F ≅ C) (ψ : C ≅ C') (e : L((v)^*[A]).obj F ≅ L((a')^*[A]).obj C₀) :
    sectionRestrictionIso A u v hi h' (θ ≪≫ ψ) e =
      L((u)^*[A]).mapIso ψ.symm ≪≫ sectionRestrictionIso A u v hi h' θ e := by
  ext
  simp [sectionRestrictionIso]

lemma sectionRestrictionIso_trans_right
    {C₁ : _root_.DerivedCategory (Sheaf B'.smallEtaleTopology A)} (θ : L((i)^*[A]).obj F ≅ C)
    (e : L((v)^*[A]).obj F ≅ L((a')^*[A]).obj C₀) (χ : C₀ ≅ C₁) :
    sectionRestrictionIso A u v hi h' θ (e ≪≫ L((a')^*[A]).mapIso χ) =
      sectionRestrictionIso A u v hi h' θ e ≪≫ χ := by
  ext
  have := (leftDerivedUpperStarCompSectionIso A i' a' h').hom.naturality χ.hom
  simp only [Functor.comp_map, Functor.id_map] at this
  simp [sectionRestrictionIso, this]

/-- Reading the restriction of a comparison `κ : F ≅ La^* C` at a section gives back the identity:
`κ` restricted to `P'` and read at `i'` against `κ` read at `i` is `𝟙 (Lu^* C)`. -/
lemma sectionRestrictionIso_restrict (hv : v ≫ a = a' ≫ u) (h : i ≫ a = 𝟙 B)
    (κ : F ≅ L((a)^*[A]).obj C) :
    sectionRestrictionIso A u v hi h'
        (L((i)^*[A]).mapIso κ ≪≫ (leftDerivedUpperStarCompSectionIso A i a h).app C)
        (L((v)^*[A]).mapIso κ ≪≫ ((leftDerivedUpperStarComp A v a).app C).symm ≪≫
          (leftDerivedUpperStarComp A a' u (v ≫ a) hv).app C) = Iso.refl _ := by
  ext
  have n₁ := (leftDerivedUpperStarComp A i' v).inv.naturality κ.hom
  have n₂ := (leftDerivedUpperStarComp A u i (i' ≫ v) hi).hom.naturality κ.hom
  simp only [Functor.comp_map] at n₁ n₂
  have H := leftDerivedUpperStar_map_comp_compSectionIso A u a a' v i i' hv hi h h' C
  simp only [sectionRestrictionIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Iso.refl_hom,
    Functor.map_comp, Category.assoc]
  have H' := H
  simp only [Functor.map_comp, Category.assoc] at H'
  rw [H', reassoc_of% n₁, Iso.hom_inv_id_app_assoc, reassoc_of% n₂, Iso.inv_hom_id_app_assoc]
  simp


/-- Reading at a section determines the restriction along the section: two trivializations with
the same reading at `i'` against the same `θ` agree after `Li'^*`. -/
lemma leftDerivedUpperStar_map_eq_of_sectionRestrictionIso_eq (θ : L((i)^*[A]).obj F ≅ C)
    (e e' : L((v)^*[A]).obj F ≅ L((a')^*[A]).obj C₀)
    (H : sectionRestrictionIso A u v hi h' θ e = sectionRestrictionIso A u v hi h' θ e') :
    L((i')^*[A]).map e.hom = L((i')^*[A]).map e'.hom := by
  have := congrArg Iso.hom H
  simp only [sectionRestrictionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom] at this
  rw [cancel_epi, cancel_mono] at this
  exact this
end SectionRestriction
end Etale

end AlgebraicGeometry
