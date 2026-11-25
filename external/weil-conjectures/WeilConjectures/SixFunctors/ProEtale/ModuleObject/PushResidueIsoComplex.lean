/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFac
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueIsoMate

/-!
# The derived (Push) comparison on complexes, for an arbitrary coefficient change

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, and
`f : X ⟶ Y` a morphism of schemes. The comparison
`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom a f : Rf_* ⋙ T^Y ⟶ T^X ⋙ Rf_*`,
the mate of the inverse of the derived (Pull) isomorphism along the derived adjunctions
`Lf^* ⊣ Rf_*`, is computed on the image of a complex `I`: through the units of the right derived
pushforwards and the counits of the derived extensions of scalars, it is the underived (Push)
comparison `ProEtale.CondensedRing.pushHom a f` applied levelwise
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom_app_Qh_fac`).

This follows from the formal computation `CategoryTheory.mateEquiv_app_comp_eq_of_fac`, the
compatibility of the derived (Pull) isomorphism with the counits
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIsoFac`), and the identification of the
underived (Push) with the mate of the inverse of the underived (Pull) isomorphism
(`CategoryTheory.Adjunction.pushHomOfComapIso_eq_mateEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

private lemma CategoryTheory.inv_comp_map_eq_of_comp_map_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B U V : D} {X Y : C} (e : A ≅ B)
    (x₁ : B ⟶ U) (x₂ : U ⟶ F.obj Y) (y₁ : A ⟶ V) (y₂ : V ⟶ F.obj X)
    (p : X ⟶ Y) (q : Y ⟶ X)
    (h : e.hom ≫ x₁ ≫ x₂ = y₁ ≫ y₂ ≫ F.map p) (hpq : p ≫ q = 𝟙 X) :
    e.inv ≫ y₁ ≫ y₂ = x₁ ≫ x₂ ≫ F.map q := by
  rw [← cancel_epi e.hom, Iso.hom_inv_id_assoc, reassoc_of% h, ← F.map_comp, hpq,
    F.map_id, Category.comp_id]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The inverse of the underived (Pull) isomorphism `pullIso a h` on the homotopy categories:
`Ext_h ⋙ h^*_h ⟶ h^*_h ⋙ Ext_h`. -/
noncomputable abbrev pullIsoInvHomotopy {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (.up ℤ) ⋙
        ((h)^*⟦Λ'⟧).mapHomotopyCategory (.up ℤ) ⟶
      ((h)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ) ⋙
        (Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCommIsoHom (.up ℤ) (pullIso a h).symm

/-- `pullIsoInvHomotopy a f` is a left inverse of `pullIsoHomotopy a f`. -/
@[reassoc]
lemma pullIsoHomotopy_app_comp_pullIsoInvHomotopy_app
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (.up ℤ)) :
    (pullIsoHomotopy a f).app K ≫ (pullIsoInvHomotopy a f).app K = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change ((HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _) ≫
      ((HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _) = 𝟙 _
  simp only [← Functor.map_comp]
  refine Eq.trans ?_ ((HomotopyCategory.quotient _ _).map_id _)
  refine congrArg _ ?_
  ext n : 1
  simp only [HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
    Iso.symm_hom, HomologicalComplex.id_f]
  erw [Category.comp_id, Category.comp_id]
  exact Iso.hom_inv_id_app _ _

/-- The derived (Pull) isomorphism through the counits, inverse form: on the image of a
complex `N`, `(derivedUpperStarExtendScalarsIso a f).inv` followed by the counits is the inverse
of the underived (Pull) isomorphism. -/
lemma derivedUpperStarExtendScalarsIso_inv_app_Qh_comp_counit
    (N : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (.up ℤ)) :
    (derivedUpperStarExtendScalarsIso a f).inv.app (DerivedCategory.Qh.obj N) ≫
        L(Mod.extendScalars (coefficientMap a X)).map
          (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app N) ≫
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
          ((((f)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj N) =
      L((f)^*⟦Λ'⟧).map ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app N) ≫
        ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
          (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map ((pullIsoInvHomotopy a f).app N) := by
  exact inv_comp_map_eq_of_comp_map_eq DerivedCategory.Qh
    ((derivedUpperStarExtendScalarsIso a f).app (DerivedCategory.Qh.obj N)) _ _ _ _ _ _
    (derivedUpperStarExtendScalarsIsoFac a f N)
    (pullIsoHomotopy_app_comp_pullIsoInvHomotopy_app a f N)

/-- **The derived (Push) comparison on complexes**, for an arbitrary coefficient change: through
the units of the right derived pushforwards and the counits of the derived extensions of scalars,
`derivedUpperStarExtendScalarsPushHom a f` at the image of a complex `K` is the mate on the
homotopy categories of the inverse of the underived (Pull) isomorphism. -/
theorem derivedUpperStarExtendScalarsPushHom_app_Qh_fac_mate
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (.up ℤ)) :
    L(Mod.extendScalars (coefficientMap a Y)).map (((f)_*⟦Λ⟧).rightDerivedFunctorUnit.app K) ≫
        (derivedUpperStarExtendScalarsPushHom a f).app (DerivedCategory.Qh.obj K) ≫
        R((f)_*⟦Λ'⟧).map ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app K) =
      (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app
          ((((f)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((mateEquiv ((upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ))
            ((upperStarLowerStarAdjunction Λ' f).mapHomotopyCategory (.up ℤ))
            (pullIsoInvHomotopy a f)).app K) ≫
        ((f)_*⟦Λ'⟧).rightDerivedFunctorUnit.app
          (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory (.up ℤ)).obj K) :=
  mateEquiv_app_comp_eq_of_fac
    ((upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ))
    ((upperStarLowerStarAdjunction Λ' f).mapHomotopyCategory (.up ℤ))
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ' f)
    ((f)^*⟦Λ⟧).leftDerivedFunctorCounit ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit
    (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit
    (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit
    ((f)_*⟦Λ⟧).rightDerivedFunctorUnit ((f)_*⟦Λ'⟧).rightDerivedFunctorUnit
    (derivedUpperStarExtendScalarsIso a f).inv (pullIsoInvHomotopy a f)
    (fun N ↦ ((upperStarLowerStarAdjunction Λ' f).mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit
      ((f)_*⟦Λ'⟧).rightDerivedFunctorUnit N)
    (fun M ↦ ((upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) ((f)^*⟦Λ⟧).leftDerivedFunctorCounit
      ((f)_*⟦Λ⟧).rightDerivedFunctorUnit M)
    (derivedUpperStarExtendScalarsIso_inv_app_Qh_comp_counit a f) K

/-- The underived (Push) as the mate of the inverse of the underived (Pull) isomorphism along
`f^* ⊣ f_*`, pointwise. -/
lemma pushHom_app_eq_unit_comp
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (pushHom a f).app M =
      (upperStarLowerStarAdjunction Λ' f).unit.app
          ((Mod.extendScalars (coefficientMap a Y)).obj (((f)_*⟦Λ⟧).obj M)) ≫
        ((f)_*⟦Λ'⟧).map ((pullIso a f).inv.app (((f)_*⟦Λ⟧).obj M) ≫
          (Mod.extendScalars (coefficientMap a X)).map
            ((upperStarLowerStarAdjunction Λ f).counit.app M)) := by
  rw [pushHom, Adjunction.pushHomOfComapIso_eq_mateEquiv _ _
    (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ' f)]
  simp [pullIso]

/-- On the image of a complex `I`, the mate on the homotopy categories of the inverse of the
underived (Pull) isomorphism is the underived (Push) applied levelwise. -/
lemma mateEquiv_pullIsoInvHomotopy_app_quotient
    (I : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) :
    (mateEquiv ((upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ))
        ((upperStarLowerStarAdjunction Λ' f).mapHomotopyCategory (.up ℤ))
        (pullIsoInvHomotopy a f)).app ((HomotopyCategory.quotient _ _).obj I) =
      (NatTrans.mapHomotopyCategory (pushHom a f) (.up ℤ)).app
        ((HomotopyCategory.quotient _ _).obj I) := by
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_map, Category.id_comp, Category.comp_id]
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient _ _).map _ ≫
      (HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _ =
    (HomotopyCategory.quotient _ _).map _
  simp only [← Functor.map_comp]
  refine congrArg _ ?_
  ext n : 1
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
    Iso.symm_hom, Functor.map_comp]
  rw [pushHom_app_eq_unit_comp]
  simp only [Functor.map_comp]
  rfl

-- unifying objects of the derived categories of module objects is slow
/-- **The derived (Push) comparison on complexes**, for an arbitrary coefficient change: through
the units of the right derived pushforwards and the counits of the derived extensions of scalars,
`derivedUpperStarExtendScalarsPushHom a f` at the image of a complex `I` is the underived (Push)
comparison `pushHom a f` applied levelwise. -/
theorem derivedUpperStarExtendScalarsPushHom_app_Qh_fac
    (I : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) :
    L(Mod.extendScalars (coefficientMap a Y)).map
        (((f)_*⟦Λ⟧).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) ≫
        (derivedUpperStarExtendScalarsPushHom a f).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) ≫
        R((f)_*⟦Λ'⟧).map ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj I)) =
      (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app
          ((((f)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj I)) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (pushHom a f) (.up ℤ)).app
          ((HomotopyCategory.quotient _ _).obj I)) ≫
        ((f)_*⟦Λ'⟧).rightDerivedFunctorUnit.app
          (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj I)) := by
  rw [derivedUpperStarExtendScalarsPushHom_app_Qh_fac_mate,
    mateEquiv_pullIsoInvHomotopy_app_quotient]

end AlgebraicGeometry.ProEtale.CondensedRing
