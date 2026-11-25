/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntExtendScalars

/-!
# `ℓ`-adic sheaves as `ℤ_ℓ,X`-modules

The inclusion `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` of ring objects of abelian sheaves on `X_proét`, followed by the
comparison of the two models of `ℚ̄_ℓ,X`, is a morphism of ring objects
`ℤ_ℓ,X ⟶ ℚ̄_ℓ,X = adicConstantSheaf ℓ X`
(`AlgebraicGeometry.ProEtale.padicIntSheafToAdicConstantSheaf`), the target being viewed as a ring
object of abelian sheaves through the lax monoidal forgetful functor `weilCoefficientsForgetAb`.
Restricting scalars along it, an `ℓ`-adic sheaf is a module object over `ℤ_ℓ,X` in abelian
sheaves (`AlgebraicGeometry.ProEtale.AdicSheaf.restrictPadicInt`). Extension of scalars
`M ↦ ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} M` along it is left adjoint to restriction of scalars
(`AlgebraicGeometry.ProEtale.padicIntExtendScalarsAdicConstantSheafAdjunction`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The morphism of ring objects `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` of abelian sheaves on `X_proét`, into the image
of `adicConstantSheaf ℓ X` under the lax monoidal forgetful functor `weilCoefficientsForgetAb`. -/
noncomputable abbrev padicIntSheafToAdicConstantSheaf :
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (padicIntSheaf X l) ⟶ (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X) :=
  padicIntSheafToPadicAlgClSheaf X l ≫ padicAlgClSheafToAdicConstantSheaf X l

/-- Restriction of scalars from `ℚ̄_ℓ,X` to `ℤ_ℓ,X`: an `ℓ`-adic sheaf as a module object over
`ℤ_ℓ,X` in abelian sheaves on `X_proét`. -/
noncomputable abbrev AdicSheaf.restrictPadicInt :
    AdicSheaf l X ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntSheaf X l)) :=
  AdicSheaf.forgetAb l X ⋙ Mod.comap (padicIntSheafToAdicConstantSheaf X l)

/-- Extension of scalars `M ↦ ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} M` from module objects over `ℤ_ℓ,X` to module
objects over the image of `adicConstantSheaf ℓ X` in abelian sheaves on `X_proét`. -/
noncomputable abbrev padicIntExtendScalarsAdicConstantSheaf :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (padicIntSheaf X l)) ⥤
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) :=
  Mod.extendScalars (padicIntSheafToAdicConstantSheaf X l)

/-- Extension of scalars from `ℤ_ℓ,X`-modules to `ℚ̄_ℓ,X`-modules in abelian sheaves is left
adjoint to restriction of scalars. -/
noncomputable def padicIntExtendScalarsAdicConstantSheafAdjunction :
    padicIntExtendScalarsAdicConstantSheaf X l ⊣
      Mod.comap (padicIntSheafToAdicConstantSheaf X l) :=
  Mod.extendRestrictAdjunction _

end AlgebraicGeometry.ProEtale
