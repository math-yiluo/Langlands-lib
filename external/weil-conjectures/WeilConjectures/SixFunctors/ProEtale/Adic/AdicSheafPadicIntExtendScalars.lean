/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafPadicInt
public import WeilConjectures.SixFunctors.ProEtale.Adic.FreeWeilCoefficients

/-!
# Extension of scalars from `ℤ_ℓ,X`-modules to `ℓ`-adic sheaves

Restriction of scalars `AlgebraicGeometry.ProEtale.AdicSheaf.restrictPadicInt` from `ℓ`-adic
sheaves (sheaves of `ℚ̄_ℓ,X`-modules in sheaves of `ℚ̄_ℓ`-modules) to module objects over `ℤ_ℓ,X`
in abelian sheaves has a left adjoint
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsRestrictAdjunction`):
```
M ↦ ℚ̄_ℓ,X ⊗_{(ℚ̄_ℓ ⊗ ℤ_ℓ,X)^#} (ℚ̄_ℓ ⊗ M)^#.
```
It is built in two steps. The sheafified free `ℚ̄_ℓ`-module functor
`F = CategoryTheory.Sheaf.extendScalarsAb` is a strong monoidal left adjoint of the forgetful
functor `weilCoefficientsForgetAb`, so it sends `ℤ_ℓ,X`-modules to `F(ℤ_ℓ,X)`-modules, left
adjoint to the forgetful functor followed by restriction of scalars along the unit
(`CategoryTheory.Adjunction.mapModAdjunction`). The adjoint `F(ℤ_ℓ,X) ⟶ ℚ̄_ℓ,X` of the inclusion
`ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` is a morphism of commutative ring objects, `F` being braided, and extension of
scalars along it is left adjoint to restriction of scalars
(`CategoryTheory.Mod.extendRestrictAdjunction`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The sheafified free `ℚ̄_ℓ`-module functor from abelian sheaves to sheaves of
`ℚ̄_ℓ`-modules on `X_proét`, left adjoint to `weilCoefficientsForgetAb`. -/
noncomputable abbrev weilCoefficientsFree :
    Sheaf (ProEt.topology X) Ab.{u + 1} ⥤
      Sheaf (ProEt.topology X) (WeilCoefficients.{u} l) :=
  Sheaf.extendScalarsAb (ProEt.topology X) (ULift.{u + 1} (PadicAlgCl l))

/-- The sheafified free `ℚ̄_ℓ`-module functor is left adjoint to the forgetful functor, by a
monoidal adjunction. -/
noncomputable abbrev weilCoefficientsFreeAdjunction :
    weilCoefficientsFree X l ⊣ weilCoefficientsForgetAb l X :=
  Sheaf.extendScalarsAbAdjunction (ProEt.topology X) (ULift.{u + 1} (PadicAlgCl l))

/-- The morphism of ring objects `F(ℤ_ℓ,X) ⟶ ℚ̄_ℓ,X` of sheaves of `ℚ̄_ℓ`-modules adjoint to the
inclusion `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`, where `F` is the sheafified free `ℚ̄_ℓ`-module functor. -/
noncomputable abbrev freePadicIntSheafToAdicConstantSheaf :
    (weilCoefficientsFree X l).obj
        ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (padicIntSheaf X l)) ⟶ adicConstantSheaf l X :=
  ((weilCoefficientsFreeAdjunction X l).homEquiv _ _).symm (padicIntSheafToAdicConstantSheaf X l)

/-- The adjoint `F(ℤ_ℓ,X) ⟶ ℚ̄_ℓ,X` of the inclusion `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` is a morphism of ring
objects. -/
instance isMonHom_freePadicIntSheafToAdicConstantSheaf :
    IsMonHom (freePadicIntSheafToAdicConstantSheaf X l) :=
  (weilCoefficientsFreeAdjunction X l).isMonHom_homEquiv_symm _

/-- `F(ℤ_ℓ,X)` is a commutative ring object, `F` being braided. -/
instance isCommMonObj_weilCoefficientsFree_obj_padicIntSheaf :
    IsCommMonObj ((weilCoefficientsFree X l).obj
      ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntSheaf X l))) :=
  Functor.isCommMonObj_obj (F := weilCoefficientsFree X l)

/-- Extension of scalars from module objects over `ℤ_ℓ,X` in abelian sheaves to `ℓ`-adic
sheaves: `M ↦ ℚ̄_ℓ,X ⊗_{F(ℤ_ℓ,X)} F(M)`, for the sheafified free `ℚ̄_ℓ`-module functor `F`. -/
noncomputable abbrev adicSheafExtendScalars :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (padicIntSheaf X l)) ⥤ AdicSheaf l X :=
  (weilCoefficientsFree X l).mapMod _ ⋙
    Mod.extendScalars (freePadicIntSheafToAdicConstantSheaf X l)

/-- The composite of the right adjoints of the two steps of `adicSheafExtendScalars` is the
restriction of scalars `AdicSheaf.restrictPadicInt` from `ℚ̄_ℓ,X` to `ℤ_ℓ,X`. -/
noncomputable def comapMapModComapIsoRestrictPadicInt :
    Mod.comap (freePadicIntSheafToAdicConstantSheaf X l) ⋙
        ((weilCoefficientsForgetAb l X).mapMod _ ⋙
          Mod.comap ((weilCoefficientsFreeAdjunction X l).unitAlgHom _)) ≅
      AdicSheaf.restrictPadicInt X l :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((weilCoefficientsForgetAb l X).mapModComapIso _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapCongr
      (((weilCoefficientsFreeAdjunction X l).homEquiv_unit _ _ _).symm.trans
        (Equiv.apply_symm_apply _ _)))

/-- **Extension of scalars from `ℤ_ℓ,X`-modules to `ℓ`-adic sheaves** is left adjoint to the
restriction of scalars `AdicSheaf.restrictPadicInt`. -/
noncomputable def adicSheafExtendScalarsRestrictAdjunction :
    adicSheafExtendScalars X l ⊣ AdicSheaf.restrictPadicInt X l :=
  (((weilCoefficientsFreeAdjunction X l).mapModAdjunction _).comp
    (Mod.extendRestrictAdjunction (freePadicIntSheafToAdicConstantSheaf X l))).ofNatIsoRight
    (comapMapModComapIsoRestrictPadicInt X l)

end AlgebraicGeometry.ProEtale
