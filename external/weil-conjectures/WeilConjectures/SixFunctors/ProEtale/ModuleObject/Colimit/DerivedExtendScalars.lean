/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!

# The derived extensions of scalars between the finite subextensions of `ℚ̄_ℓ`

Let `ℓ` be a prime and `X` a scheme. For finite subextensions `E ≤ F` of `ℚ̄_ℓ` over `ℚ_ℓ`, this
file defines the derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} -
```
(`ProEtale.derivedExtendScalarsSubfield`, `ProEtale.derivedExtendScalarsToPadicAlgCl`) and their
transitivity `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` (`ProEtale.derivedExtendScalarsCompIso`). They are
the functors of the cocone of categories of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The derived extensions of scalars and their transitivity -/

section ExtendScalars

/-- The derived extension of scalars `T^X_{E,F} = F_X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{F_X})`
along the inclusion of finite subextensions `E ≤ F`. -/
noncomputable abbrev derivedExtendScalarsSubfield {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :=
  L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))

/-- The derived extension of scalars
`T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{ℚ̄_ℓ,X})` along the inclusion of a finite
subextension `E` into `ℚ̄_ℓ`. -/
noncomputable abbrev derivedExtendScalarsToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) :=
  L(Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))

/-- Transitivity of the derived extension of scalars: `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` for
`E ≤ F`. The extensions of scalars being exact, the composite of their derived functors is the
derived functor of the composite, which is the extension of scalars along the composite
inclusion `E_X ⟶ F_X ⟶ ℚ̄_ℓ,X = E_X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def derivedExtendScalarsCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F ≅
      derivedExtendScalarsToPadicAlgCl X ℓ E :=
  haveI : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h ≫
      padicSubfieldRingObjToPadicAlgCl X ℓ F)) :=
    preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).symm
  (Functor.leftDerivedFunctorCompIso _ _).symm ≪≫
    Functor.leftDerivedFunctorNatIso _
      ((Mod.extendScalarsComp _ _).symm ≪≫
        Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))

end ExtendScalars

end AlgebraicGeometry.ProEtale
