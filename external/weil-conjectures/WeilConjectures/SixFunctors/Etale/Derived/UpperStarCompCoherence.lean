/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Pasting
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp

/-!
# Coherence of the composition isomorphisms of derived pullbacks

The composition isomorphisms `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) are associative
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp_assoc'`): on the image of a complex they are
the composition isomorphisms of the underived pullbacks, which are associative. As a
consequence, the square isomorphisms of the derived pullbacks paste vertically
(`AlgebraicGeometry.Etale.derivedSquareUpperStarIso_paste_vert`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

lemma mapHomotopyCategoryCompHom_upperStarComp_quotient_obj {T S R : Scheme.{u}} (a : T ⟶ S)
    (b : S ⟶ R) (ab : T ⟶ R) (hab : ab = a ≫ b)
    (K : CochainComplex (Sheaf R.smallEtaleTopology A) ℤ) :
    Functor.mapHomotopyCategoryCompHom (b)^*[A] (a)^*[A] (ab)^*[A] (upperStarComp A a b ab hab)
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        (Functor.mapHomologicalComplexCompHom (b)^*[A] (a)^*[A] (ab)^*[A]
          (upperStarComp A a b ab hab) K) := by
  rw [Functor.map_comp]
  congr 1

end Etale

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

open _root_.DerivedCategory

variable {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z)
  (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
lemma mapHomotopyCategoryCompHom_upperStarComp_assoc
    (P : HomotopyCategory (Sheaf Z.smallEtaleTopology A) (.up ℤ)) :
    Functor.mapHomotopyCategoryCompHom (gh)^*[A] (f)^*[A] (fgh)^*[A]
        (upperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])) P ≫
      ((f)^*[A].mapHomotopyCategory (.up ℤ)).map
        (Functor.mapHomotopyCategoryCompHom (h)^*[A] (g)^*[A] (gh)^*[A]
          (upperStarComp A g h gh hgh) P) =
    Functor.mapHomotopyCategoryCompHom (h)^*[A] (fg)^*[A] (fgh)^*[A]
        (upperStarComp A fg h fgh hfgh) P ≫
      Functor.mapHomotopyCategoryCompHom (g)^*[A] (f)^*[A] (fg)^*[A]
        (upperStarComp A f g fg hfg) (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have key := Etale.upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh
  have : ∀ n, _ := fun n ↦ NatTrans.congr_app key (K.X n)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at this
  rw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj,
    mapHomotopyCategoryCompHom_upperStarComp_quotient_obj]
  erw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj,
    mapHomotopyCategoryCompHom_upperStarComp_quotient_obj]
  rw [Functor.mapHomotopyCategory_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  simp only [Functor.mapHomologicalComplexCompHom, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, Functor.mapHomologicalComplex_map_f]
  erw [Category.comp_id, Category.comp_id, Category.comp_id, Category.comp_id]
  exact this n

lemma leftDerivedUpperStarComp_assoc'_app_Qh_obj
    (P : HomotopyCategory (Sheaf Z.smallEtaleTopology A) (.up ℤ)) :
    (leftDerivedUpperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app
        (Qh.obj P) ≫
      L((f)^*[A]).map ((leftDerivedUpperStarComp A g h gh hgh).hom.app (Qh.obj P)) =
    (leftDerivedUpperStarComp A fg h fgh hfgh).hom.app (Qh.obj P) ≫
      (leftDerivedUpperStarComp A f g fg hfg).hom.app (L((h)^*[A]).obj (Qh.obj P)) := by
  rw [← cancel_mono (L((f)^*[A]).map (L((g)^*[A]).map ((h)^*[A].leftDerivedFunctorCounit.app P)) ≫
    L((f)^*[A]).map ((g)^*[A].leftDerivedFunctorCounit.app
      (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) ≫
    (f)^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj
      (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)))]
  -- the left hand side
  have u₁ := leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A g h gh hgh P
  have u₂ := leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A f gh fgh
    (by rw [hfgh, hfg, hgh, Category.assoc]) P
  have u₃ := leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A f g fg hfg
    (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)
  have u₄ := leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A fg h fgh hfgh P
  have n₁ := counit_naturality A f (Functor.mapHomotopyCategoryCompHom (h)^*[A] (g)^*[A]
    (gh)^*[A] (upperStarComp A g h gh hgh) P)
  have n₂ : (leftDerivedUpperStarComp A f g fg hfg).hom.app (L((h)^*[A]).obj (Qh.obj P)) ≫
      L((f)^*[A]).map (L((g)^*[A]).map ((h)^*[A].leftDerivedFunctorCounit.app P)) =
      L((fg)^*[A]).map ((h)^*[A].leftDerivedFunctorCounit.app P) ≫
        (leftDerivedUpperStarComp A f g fg hfg).hom.app _ :=
    ((leftDerivedUpperStarComp A f g fg hfg).hom.naturality _).symm
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [u₁, Functor.map_comp_assoc, n₁,
    reassoc_of% u₂, reassoc_of% n₂, u₃, reassoc_of% u₄, ← Functor.map_comp, ← Functor.map_comp,
    mapHomotopyCategoryCompHom_upperStarComp_assoc A f g h fg gh fgh hfg hgh hfgh P]

/-- **Associativity of the composition isomorphisms of derived pullbacks**, for composites that
are merely equal to the given ones. -/
lemma leftDerivedUpperStarComp_assoc' :
    (leftDerivedUpperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarComp A g h gh hgh).hom L((f)^*[A]) =
      (leftDerivedUpperStarComp A fg h fgh hfgh).hom ≫
        Functor.whiskerLeft L((h)^*[A]) (leftDerivedUpperStarComp A f g fg hfg).hom :=
  Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦
    leftDerivedUpperStarComp_assoc'_app_Qh_obj A f g h fg gh fgh hfg hgh hfgh P

/-- The component form of `leftDerivedUpperStarComp_assoc'`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_assoc'_app (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K ≫
      L((f)^*[A]).map ((leftDerivedUpperStarComp A g h gh hgh).hom.app K) =
    (leftDerivedUpperStarComp A fg h fgh hfgh).hom.app K ≫
      (leftDerivedUpperStarComp A f g fg hfg).hom.app (L((h)^*[A]).obj K) :=
  NatTrans.congr_app (leftDerivedUpperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh) K

/-- The component form of `leftDerivedUpperStarComp_assoc'`, rearranged. -/
@[reassoc]
lemma map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    L((f)^*[A]).map ((leftDerivedUpperStarComp A g h gh hgh).hom.app K) ≫
        (leftDerivedUpperStarComp A f g fg hfg).inv.app (L((h)^*[A]).obj K) =
      (leftDerivedUpperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app K ≫
        (leftDerivedUpperStarComp A fg h fgh hfgh).hom.app K := by
  rw [← cancel_epi ((leftDerivedUpperStarComp A f gh fgh
    (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K),
    ← cancel_mono ((leftDerivedUpperStarComp A f g fg hfg).hom.app (L((h)^*[A]).obj K))]
  simp only [Category.assoc, Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc]
  erw [Category.comp_id]
  exact leftDerivedUpperStarComp_assoc'_app A f g h fg gh fgh hfg hgh hfgh K

/-- The component form of `leftDerivedUpperStarComp_assoc'`, rearranged the other way. -/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A f g fg hfg).hom.app (L((h)^*[A]).obj K) ≫
        L((f)^*[A]).map ((leftDerivedUpperStarComp A g h gh hgh).inv.app K) =
      (leftDerivedUpperStarComp A fg h fgh hfgh).inv.app K ≫
        (leftDerivedUpperStarComp A f gh fgh
          (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K := by
  rw [← cancel_epi ((leftDerivedUpperStarComp A fg h fgh hfgh).hom.app K),
    reassoc_of% (leftDerivedUpperStarComp_assoc'_app A f g h fg gh fgh hfg hgh hfgh K).symm,
    ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id,
    Iso.hom_inv_id_app_assoc]

/-- The inverse form of `leftDerivedUpperStarComp_assoc'_app`. -/
@[reassoc]
lemma map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    L((f)^*[A]).map ((leftDerivedUpperStarComp A g h gh hgh).inv.app K) ≫
        (leftDerivedUpperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app K =
      (leftDerivedUpperStarComp A f g fg hfg).inv.app (L((h)^*[A]).obj K) ≫
        (leftDerivedUpperStarComp A fg h fgh hfgh).inv.app K := by
  rw [← cancel_epi ((leftDerivedUpperStarComp A fg h fgh hfgh).hom.app K ≫
    (leftDerivedUpperStarComp A f g fg hfg).hom.app (L((h)^*[A]).obj K)),
    ← leftDerivedUpperStarComp_assoc'_app A f g h fg gh fgh hfg hgh hfgh]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app_assoc A f g h fg gh fgh
    hfg hgh hfgh, Iso.hom_inv_id_app_assoc]
  simp only [Iso.hom_inv_id_app]

end Etale

end AlgebraicGeometry
