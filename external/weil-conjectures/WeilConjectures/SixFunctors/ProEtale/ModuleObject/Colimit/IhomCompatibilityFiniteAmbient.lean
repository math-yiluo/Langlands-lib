/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.UnitBiproductDesc
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryBasis
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIso
public import WeilConjectures.CategoryTheory.DerivedCategory.NatTransIdTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsBasis
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparisonOfBasis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldBasis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!

# The internal Hom comparison for a finite extension `E ⊆ F`, on the ambient derived categories

Let `E ≤ F` be finite subextensions of `ℚ̄_ℓ` and `X` a scheme. The derived extension of scalars
`T = F_X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{F_X})` (`ProEtale.derivedExtendScalarsSubfield`),
monoidal through `Functor.leftDerivedFunctorMonoidal`, commutes with internal homs: the
comparison `T RHom(A, B) ⟶ RHom(T A, T B)` is an isomorphism
(`ProEtale.CondensedRing.isIso_ihomComparison_derivedExtendScalarsSubfield`).

The extension of scalars is exact, so `T` is the levelwise functor, with right adjoint the
levelwise restriction of scalars `R`, which is conservative. A basis `e_i` of `F` over `E` makes
`F_X` free over `E_X` (`ProEtale.isIso_biproductDesc_padicSubfieldBasisSection`), so that
`(m_i) ↦ Σ e_i m_i : M^{⊕ι} ⟶ R T M` is an isomorphism, also on derived categories; the result
is then the abstract criterion
`Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_biproductDesc`, the scalars `e_i` acting on
`D(Mod_{F_X})` through `DerivedCategory.natTransId`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) {E F : FiniteIntermediateField ℓ} (h : E ≤ F)

/-- The adjunction `F_X ⊗ᴸ_{E_X} - ⊣ D(Res)` between the derived extension of scalars along
`E_X ⟶ F_X` and the levelwise restriction of scalars: the levelwise adjunction transported
along the identification of the derived functor of the exact extension of scalars with the
levelwise functor. -/
noncomputable def derivedExtendScalarsSubfieldAdjunction :
    derivedExtendScalarsSubfield X ℓ h ⊣
      (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory :=
  (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategoryAdjunction
    |>.ofNatIsoLeft (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm

/-- The scalars `e_i` of a basis of `F` over `E` acting on `D(Mod_{F_X})`. -/
noncomputable def derivedSubfieldBasisSMul (i : Fin (FiniteIntermediateField.finrankOfLE h)) :
    𝟭 (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ F))) ⟶ 𝟭 _ :=
  DerivedCategory.natTransId (Mod.smulNatTrans (padicSubfieldBasisSection X h i))

/-- **The internal Hom comparison for `E ⊆ F` on the ambient derived categories**: for
`A, B ∈ D(Mod_{E_X})`, the comparison `F ⊗ᴸ RHom(A, B) ⟶ RHom(F ⊗ᴸ A, F ⊗ᴸ B)` is an
isomorphism. -/
theorem isIso_ihomComparison_derivedExtendScalarsSubfield
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))) :
    letI := Mod.extendScalarsMonoidal (padicSubfieldRingObjMap X ℓ h)
    letI := (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorMonoidal
    IsIso
      (Functor.LaxMonoidal.ihomComparison (derivedExtendScalarsSubfield X ℓ h) A) := by
  let := Mod.extendScalarsMonoidal (padicSubfieldRingObjMap X ℓ h)
  let := (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorMonoidal
  have : (derivedExtendScalarsSubfield X ℓ h).Additive :=
    Functor.additive_of_iso (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm
  refine Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_biproductDesc _
    (derivedExtendScalarsSubfieldAdjunction ℓ X h) (derivedSubfieldBasisSMul ℓ X h)
    (fun i ↦ DerivedCategory.natTransId_app_tensor _ (Mod.smulNatTrans_app_tensor _)) ?_ A
  intro K
  have hb := Mod.isIso_biproductDesc_extendUnit_smul (padicSubfieldRingObjMap X ℓ h)
    (padicSubfieldBasisSection X h) (isIso_biproductDesc_padicSubfieldBasisSection X h)
  have hK := Adjunction.isIso_biproductDesc_mapDerivedCategoryAdjunction_unit
    (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ h))
    (fun i ↦ Mod.smulNatTrans (padicSubfieldBasisSection X h i)) hb K
  exact Adjunction.isIso_biproductDesc_ofNatIsoLeft_unit _ _ (derivedSubfieldBasisSMul ℓ X h) K hK

end AlgebraicGeometry.ProEtale.CondensedRing
