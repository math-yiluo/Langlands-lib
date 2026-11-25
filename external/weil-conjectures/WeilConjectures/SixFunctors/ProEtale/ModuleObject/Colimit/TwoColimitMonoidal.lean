/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalIso
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidalComp
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.SubcategoryNatTrans
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal

/-!
# The cocone of bounded constructible `E`-complexes is a cocone of monoidal functors

Let `ℓ` be a prime and `X` a scheme. For finite subextensions `E ≤ F` of `ℚ̄_ℓ / ℚ_ℓ`, the derived
extension of scalars `F_X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{F_X})` is strong monoidal
(`ProEtale.CondensedRing.leftDerivedExtendScalarsSubfieldMonoidal`), and the transitivity
isomorphism `ProEtale.derivedExtendScalarsCompIso : T_{E,F} ⋙ T_{F,Ω} ≅ T_{E,Ω}` is a monoidal
natural isomorphism (`ProEtale.CondensedRing.isMonoidal_derivedExtendScalarsCompIso_hom`).

Restricting to the bounded constructible complexes over a scheme `X` of finite type over a field
`k` of characteristic `≠ ℓ`, the transition functors `ProEtale.constructibleExtendScalars` of the
cocone `ProEtale.constructibleCocone` are strong monoidal
(`ProEtale.CondensedRing.monoidal_constructibleExtendScalars`), as are its functors
`ProEtale.constructibleToPadicAlgCl` to the vertex
(`ProEtale.CondensedRing.monoidal_constructibleToPadicAlgCl`), and the compatibility
isomorphisms `ProEtale.constructibleToPadicAlgClCompIso` are monoidal
(`ProEtale.CondensedRing.isMonoidal_constructibleToPadicAlgClCompIso_hom`).

All these monoidal structures are those of `Functor.leftDerivedFunctorMonoidal`, for the
monoidal structures `Mod.extendScalarsMonoidal` of the underived extensions of scalars; the
monoidality of the transitivity isomorphisms follows from the one of the underived ones
(`Mod.isMonoidal_extendScalarsComp_hom`, `Mod.isMonoidal_extendScalarsIsoOfEq_hom`) and from
the compatibility of `Functor.leftDerivedFunctorMonoidal` with compositions and natural
isomorphisms (`Functor.isMonoidal_leftDerivedFunctorCompIso_hom`,
`Functor.isMonoidal_leftDerivedFunctorNatIso_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

section Derived

/-- The derived extension of scalars `F_X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{F_X})` along an
inclusion `E ≤ F` of finite subextensions of `ℚ̄_ℓ` is monoidal, with comonoidal structure the
tensor comparison `Functor.leftDerivedTensorComparison` (`Functor.leftDerivedFunctorMonoidal_δ`). -/
@[instance_reducible]
noncomputable def leftDerivedExtendScalarsSubfieldMonoidal (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).Monoidal :=
  letI := Mod.extendScalarsMonoidal (padicSubfieldRingObjMap X ℓ h)
  (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorMonoidal

/-- The transitivity isomorphism `T_{E,F} ⋙ T_{F,Ω} ≅ T_{E,Ω}` of the derived extensions of
scalars is a monoidal natural isomorphism. -/
lemma isMonoidal_derivedExtendScalarsCompIso_hom (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    letI := leftDerivedExtendScalarsSubfieldMonoidal ℓ X h
    letI := leftDerivedExtendScalarsPadicAlgClMonoidal ℓ F X
    letI := leftDerivedExtendScalarsPadicAlgClMonoidal ℓ E X
    NatTrans.IsMonoidal (derivedExtendScalarsCompIso X ℓ h).hom := by
  let := Mod.extendScalarsMonoidal (padicSubfieldRingObjMap X ℓ h)
  let := Mod.extendScalarsMonoidal (padicSubfieldRingObjToPadicAlgCl X ℓ F)
  let := Mod.extendScalarsMonoidal (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  let := Mod.extendScalarsMonoidal
    (padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjToPadicAlgCl X ℓ F)
  have := Mod.isMonoidal_extendScalarsComp_hom (padicSubfieldRingObjMap X ℓ h)
    (padicSubfieldRingObjToPadicAlgCl X ℓ F)
  have := Mod.isMonoidal_extendScalarsIsoOfEq_hom
    (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)
  have : NatTrans.IsMonoidal ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
      (padicSubfieldRingObjToPadicAlgCl X ℓ F)).symm ≪≫
        Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).hom :=
    inferInstanceAs (NatTrans.IsMonoidal ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
      (padicSubfieldRingObjToPadicAlgCl X ℓ F)).inv ≫
        (Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).hom))
  exact Functor.isMonoidal_leftDerivedFunctorCompIso_symm_trans_natIso_hom _ _ _

end Derived

/-! ### The bounded constructible complexes -/

section BoundedConstructible

variable {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- The derived extension of scalars `F ⊗ᴸ_E - : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦F⟧` on bounded constructible
complexes, for finite subextensions `E ≤ F`, is strong monoidal, with the comparison isomorphisms
of `leftDerivedExtendScalarsSubfieldMonoidal`. -/
noncomputable instance monoidal_constructibleExtendScalars
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    (constructibleExtendScalars X.left ℓ h).Monoidal := by
  letI := leftDerivedExtendScalarsSubfieldMonoidal ℓ X.left h
  unfold constructibleExtendScalars
  exact ObjectProperty.monoidalLift _ _

/-- The compatibility isomorphisms `T_{E,F} ⋙ T_{F,Ω} ≅ T_{E,Ω}` of the cocone of bounded
constructible complexes are monoidal natural isomorphisms. -/
instance isMonoidal_constructibleToPadicAlgClCompIso_hom
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    NatTrans.IsMonoidal (constructibleToPadicAlgClCompIso X.left ℓ h).hom := by
  let := leftDerivedExtendScalarsSubfieldMonoidal ℓ X.left h
  let := leftDerivedExtendScalarsPadicAlgClMonoidal ℓ F X.left
  let := leftDerivedExtendScalarsPadicAlgClMonoidal ℓ E X.left
  have := isMonoidal_derivedExtendScalarsCompIso_hom ℓ X.left h
  exact ObjectProperty.isMonoidal_fullyFaithfulCancelRight_hom _ _ _ _

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
