/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendChangeTransfer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars

/-!
# The transitivity of the derived extensions of scalars on complexes

For finite subextensions `E ≤ F` of `ℚ̄_ℓ`, the transitivity isomorphism
`T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` (`ProEtale.derivedExtendScalarsCompIso`) is, on the image
of an object `M` of the homotopy category and modulo the counits of the derived extensions of
scalars (which are isomorphisms, the extensions of scalars being exact), induced by the
isomorphism `ℚ̄_ℓ,X ⊗_{F_X} (F_X ⊗_{E_X} -) ≅ ℚ̄_ℓ,X ⊗_{E_X} -` on the homotopy categories
(`ProEtale.derivedExtendScalarsCompIso_hom_app_Qh`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- `derivedExtendScalarsCompIso` unfolded. -/
lemma derivedExtendScalarsCompIso_eq {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    derivedExtendScalarsCompIso X ℓ h =
      ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorCompIso
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F))).symm ≪≫
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h) ⋙
        Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).leftDerivedFunctorNatIso
        (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)) :=
  rfl

-- Unifying the generic statement `leftDerivedFunctorCompIso_symm_trans_natIso_hom_app_Qh` with
-- the concrete derived categories of module objects (and their many instances) is slow.
/-- The transitivity isomorphism `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` on the image of an object
`M` of the homotopy category, read through the counits of the derived extensions of scalars,
is the isomorphism `ℚ̄_ℓ,X ⊗_{F_X} (F_X ⊗_{E_X} M) ≅ ℚ̄_ℓ,X ⊗_{E_X} M`. -/
lemma derivedExtendScalarsCompIso_hom_app_Qh {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (M : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E)) (ComplexShape.up ℤ)) :
    (derivedExtendScalarsCompIso X ℓ h).hom.app (DerivedCategory.Qh.obj M) ≫
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorCounit.app
          M =
      (derivedExtendScalarsToPadicAlgCl X ℓ F).map
          ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorCounit.app M) ≫
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).leftDerivedFunctorCounit.app
          (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomotopyCategory _).obj M) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))
            (ComplexShape.up ℤ)).hom.app M) := by
  simp only [derivedExtendScalarsCompIso_eq]
  exact Functor.leftDerivedFunctorCompIso_symm_trans_natIso_hom_app_Qh
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F))
    (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)) M

end AlgebraicGeometry.ProEtale
