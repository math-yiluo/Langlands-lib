/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.HomotopyCategory.CompIsoTransfer
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurjColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurjCounit

/-!
# The adjoint transfer of the derived extensions of scalars on complexes

Let `E, F ≤ k` be finite subextensions of `ℚ̄_ℓ`. Along the adjunctions
`T^X_{E,k} ⊣ D(Res_{E→k})`, `T^X_{E,Ω} ⊣ D(Res_{E→Ω})` and the transitivity isomorphisms
`T^X_{E,k} ⋙ T^X_{k,Ω} ≅ T^X_{E,Ω}`, `T^X_{F,k} ⋙ T^X_{k,Ω} ≅ T^X_{F,Ω}`, a morphism
`T^X_{E,Ω} K ⟶ T^X_{F,Ω} L` is of the form `τ⁻¹ ≫ T^X_{k,Ω} g ≫ τ` as soon as its adjoint
`K ⟶ D(Res_{E→Ω}) T^X_{F,Ω} L` factors through the adjoint transfer
`D(Res_{E→k}) T^X_{F,k} L ⟶ D(Res_{E→Ω}) T^X_{F,Ω} L`
(`CategoryTheory.Adjunction.eq_inv_app_comp_map_comp_hom_app`).

On the image `L = Q Y` of a complex, this transfer is, modulo the counits of the derived
extensions of scalars and the factorizations of `D(Res)`, the image of the inclusion
`Res_{E→k}(k_X ⊗_{F_X} Y) ⟶ Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y)` of the colimit cocone
`ProEtale.subfieldExtendScalarsCocone`
(`ProEtale.compIsoTransfer_derivedExtendScalars_Qh`).
-/

@[expose] public section

universe u v u'

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod

open MonoidalCategory MonObj

/-- The comparison of adjoint transfers for module objects, with a chosen representative
of the transfer on the homotopy category. -/
private lemma compIsoTransfer_derivedExtendScalars_comparison
    {C : Type u'} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
    [Abelian.HasFunctorialFlatResolution C]
    {R R' S T : C} [MonObj R] [MonObj R'] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj R'] [IsCommMonObj S] [IsCommMonObj T]
    (a : R ⟶ S) (a' : R' ⟶ S) (b : S ⟶ T) (j : R ⟶ T) (j' : R' ⟶ T)
    [IsMonHom a] [IsMonHom a'] [IsMonHom b] [IsMonHom j] [IsMonHom j']
    [PreservesFiniteLimits (extendScalars a')]
    (e : extendScalars a ⋙ extendScalars b ≅ extendScalars j)
    (e' : extendScalars a' ⋙ extendScalars b ≅ extendScalars j')
    (τ : (extendScalars a).leftDerivedFunctor ⋙ (extendScalars b).leftDerivedFunctor ≅
      (extendScalars j).leftDerivedFunctor)
    (τ' : (extendScalars a').leftDerivedFunctor ⋙ (extendScalars b).leftDerivedFunctor ≅
      (extendScalars j').leftDerivedFunctor)
    (hτ : ∀ M : HomotopyCategory (Mod C R) (ComplexShape.up ℤ),
      τ.hom.app (DerivedCategory.Qh.obj M) ≫ (extendScalars j).leftDerivedFunctorCounit.app M =
        (extendScalars b).leftDerivedFunctor.map
            ((extendScalars a).leftDerivedFunctorCounit.app M) ≫
          (extendScalars b).leftDerivedFunctorCounit.app
            (((extendScalars a).mapHomotopyCategory _).obj M) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e _).hom.app M))
    (hτ' : ∀ M : HomotopyCategory (Mod C R') (ComplexShape.up ℤ),
      τ'.hom.app (DerivedCategory.Qh.obj M) ≫ (extendScalars j').leftDerivedFunctorCounit.app M =
        (extendScalars b).leftDerivedFunctor.map
            ((extendScalars a').leftDerivedFunctorCounit.app M) ≫
          (extendScalars b).leftDerivedFunctorCounit.app
            (((extendScalars a').mapHomotopyCategory _).obj M) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e' _).hom.app M))
    (M : HomotopyCategory (Mod C R') (ComplexShape.up ℤ))
    {q : ((comap a).mapHomotopyCategory _).obj
        (((extendScalars a').mapHomotopyCategory _).obj M) ⟶
      ((comap j).mapHomotopyCategory _).obj
        (((extendScalars j').mapHomotopyCategory _).obj M)}
    (hq : Adjunction.compIsoTransfer
      ((extendRestrictAdjunction a).mapHomotopyCategory (ComplexShape.up ℤ))
      ((extendRestrictAdjunction j).mapHomotopyCategory (ComplexShape.up ℤ))
      (Functor.mapHomotopyCategoryCompIso e _) (Functor.mapHomotopyCategoryCompIso e' _) M = q) :
    (comap a).mapDerivedCategory.map ((extendScalars a').leftDerivedFunctorCounit.app M) ≫
        (comap a).mapDerivedCategoryFactorsh.hom.app _ ≫ DerivedCategory.Qh.map q =
      Adjunction.compIsoTransfer (derivedExtendMapDerivedCategoryAdjunction a)
          (derivedExtendMapDerivedCategoryAdjunction j) τ τ' (DerivedCategory.Qh.obj M) ≫
        (comap j).mapDerivedCategory.map ((extendScalars j').leftDerivedFunctorCounit.app M) ≫
        (comap j).mapDerivedCategoryFactorsh.hom.app _ := by
  have hc := Adjunction.compIsoTransfer_comparison
    ((extendRestrictAdjunction a).mapHomotopyCategory (ComplexShape.up ℤ))
    ((extendRestrictAdjunction j).mapHomotopyCategory (ComplexShape.up ℤ))
    (Functor.mapHomotopyCategoryCompIso e _) (Functor.mapHomotopyCategoryCompIso e' _)
    (derivedExtendMapDerivedCategoryAdjunction a) (derivedExtendMapDerivedCategoryAdjunction j)
    τ τ' (extendScalars a).leftDerivedFunctorCounit
    (asIso (extendScalars a').leftDerivedFunctorCounit)
    (extendScalars b).leftDerivedFunctorCounit (extendScalars j).leftDerivedFunctorCounit
    (extendScalars j').leftDerivedFunctorCounit
    (comap a).mapDerivedCategoryFactorsh (comap j).mapDerivedCategoryFactorsh
    (derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh j)
    (derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh a) hτ hτ' M
  rw [hq] at hc
  exact hc

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {E F G : FiniteIntermediateField ℓ}
  (hE : E ≤ G) (hF : F ≤ G)
  (Y : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)

/-- The adjoint transfer of the extensions of scalars on the homotopy categories, on the image of
`Y`, is the image of the inclusion of the colimit cocone `subfieldExtendScalarsCocone`. -/
lemma compIsoTransfer_mapHomotopyCategory_subfieldExtendScalars (k : PadicSubfieldAbove ℓ G) :
    Adjunction.compIsoTransfer
      ((Mod.extendRestrictAdjunction
        (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).mapHomotopyCategory
        (ComplexShape.up ℤ))
      ((Mod.extendRestrictAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (Functor.mapHomotopyCategoryCompIso
        (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ _)) _)
      (Functor.mapHomotopyCategoryCompIso
        (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ _)) _)
      ((HomotopyCategory.quotient _ _).obj Y) =
    (HomotopyCategory.quotient _ _).map ((subfieldExtendScalarsCocone X ℓ hE hF Y).ι.app k) :=
  Adjunction.compIsoTransfer_mapHomotopyCategory_quotient _ _ _ _ _ Y _ fun _ ↦ rfl

/-- The adjoint transfer `D(Res_{E→k}) T^X_{F,k} (Q Y) ⟶ D(Res_{E→Ω}) T^X_{F,Ω} (Q Y)` is, modulo
the counits and the factorizations of `D(Res)`, the image of the inclusion
`Res_{E→k}(k_X ⊗_{F_X} Y) ⟶ Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y)` of the colimit cocone. -/
theorem compIsoTransfer_derivedExtendScalars_Qh (k : PadicSubfieldAbove ℓ G) :
    (Mod.comap (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).mapDerivedCategory.map
        ((Mod.extendScalars
          (padicSubfieldRingObjMap X ℓ (hF.trans k.property))).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj Y)) ≫
      (Mod.comap
        (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).mapDerivedCategoryFactorsh.hom.app _ ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((subfieldExtendScalarsCocone X ℓ hE hF Y).ι.app k)) =
    Adjunction.compIsoTransfer
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (padicSubfieldRingObjMap X ℓ (hE.trans k.property)))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E))
        (derivedExtendScalarsCompIso X ℓ (hE.trans k.property))
        (derivedExtendScalarsCompIso X ℓ (hF.trans k.property))
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Y)) ≫
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory.map
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).leftDerivedFunctorCounit.app
          _) ≫
      (Mod.comap
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactorsh.hom.app _ := by
  exact Mod.compIsoTransfer_derivedExtendScalars_comparison
    (padicSubfieldRingObjMap X ℓ (hE.trans k.property))
    (padicSubfieldRingObjMap X ℓ (hF.trans k.property))
    (padicSubfieldRingObjToPadicAlgCl X ℓ k.obj)
    (padicSubfieldRingObjToPadicAlgCl X ℓ E)
    (padicSubfieldRingObjToPadicAlgCl X ℓ F)
    (Mod.extendScalarsCompIsoOfEq
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (hE.trans k.property)))
    (Mod.extendScalarsCompIsoOfEq
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (hF.trans k.property)))
    (derivedExtendScalarsCompIso X ℓ (hE.trans k.property))
    (derivedExtendScalarsCompIso X ℓ (hF.trans k.property))
    (derivedExtendScalarsCompIso_hom_app_Qh X ℓ (hE.trans k.property))
    (derivedExtendScalarsCompIso_hom_app_Qh X ℓ (hF.trans k.property))
    ((HomotopyCategory.quotient _ _).obj Y)
    (compIsoTransfer_mapHomotopyCategory_subfieldExtendScalars X ℓ hE hF Y k)

end AlgebraicGeometry.ProEtale
