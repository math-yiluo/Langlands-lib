/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLaxMonoidal
public import WeilConjectures.SixFunctors.ProEtale.Adic.Module

/-!
# `ℓ`-adic sheaves as module objects in abelian sheaves

The forgetful functor from sheaves of `ℚ̄_ℓ`-modules to abelian sheaves on `X_proét` is lax
monoidal (`ModuleCat.laxMonoidalForget₂Ab` and `CategoryTheory.sheafComposeLaxMonoidal`), so it
sends the ring object `ℚ̄_ℓ,X = adicConstantSheaf ℓ X` to a ring object of abelian sheaves, and
`ℓ`-adic sheaves to module objects over it
(`AlgebraicGeometry.ProEtale.AdicSheaf.forgetAb`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The forgetful functor from sheaves of `ℚ̄_ℓ`-modules to abelian sheaves on `X_proét`, lax
monoidal for the sheafified tensor products. -/
noncomputable abbrev weilCoefficientsForgetAb :
    Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  sheafCompose (Scheme.ProEt.topology X) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})

noncomputable instance : (weilCoefficientsForgetAb l X).LaxMonoidal :=
  sheafComposeLaxMonoidal _ _

/-- An `ℓ`-adic sheaf, as a module object in abelian sheaves over the image of `ℚ̄_ℓ,X` under
the lax monoidal forgetful functor. -/
noncomputable abbrev AdicSheaf.forgetAb :
    AdicSheaf l X ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) :=
  (weilCoefficientsForgetAb l X).mapMod (adicConstantSheaf l X)

end AlgebraicGeometry.ProEtale
