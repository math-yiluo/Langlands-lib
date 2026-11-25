/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafComposeBraided
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetMonoidalAdjunction

/-!
# Free sheaves of modules on abelian sheaves, as a braided monoidal left adjoint

For a lax braided functor `G : A ⥤ B`, postcomposition `sheafCompose J G` is lax braided for the
sheafified tensor products (`CategoryTheory.sheafComposeLaxBraided`). For a commutative ring
`R`, the sheafified free `R`-module functor `M ↦ (R ⊗[ℤ] M)^#` from abelian sheaves to sheaves of
`R`-modules is strong monoidal and braided, left adjoint to the forgetful functor by a monoidal
adjunction (`CategoryTheory.Sheaf.extendScalarsAbAdjunction`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

namespace Sheaf

universe v

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (R : Type v) [CommRing R]
  [HasWeakSheafify J Ab.{v}] [(J.W (A := Ab.{v})).IsMonoidal]
  [HasWeakSheafify J (ModuleCat.{v} R)] [(J.W (A := ModuleCat.{v} R)).IsMonoidal]
  [J.HasSheafCompose (forget₂ (ModuleCat.{v} R) Ab.{v})]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The sheafified free `R`-module functor `M ↦ (R ⊗[ℤ] M)^#` from abelian sheaves to sheaves of
`R`-modules. -/
noncomputable def extendScalarsAb : Sheaf J Ab.{v} ⥤ Sheaf J (ModuleCat.{v} R) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalarsAb R)

/-- The sheafified free `R`-module functor is left adjoint to the forgetful functor. -/
noncomputable abbrev extendScalarsAbAdjunction :
    extendScalarsAb J R ⊣ sheafCompose J (forget₂ (ModuleCat.{v} R) Ab.{v}) :=
  Sheaf.adjunction J (ModuleCat.extendScalarsAbAdj R)

/-- The sheafified free `R`-module functor is strong monoidal. -/
noncomputable instance : (extendScalarsAb J R).Monoidal :=
  composeAndSheafifyMonoidal J (ModuleCat.extendScalarsAbAdj R)

/-- The adjunction between the sheafified free `R`-module functor and the forgetful functor is
monoidal. -/
instance : (extendScalarsAbAdjunction J R).IsMonoidal :=
  inferInstanceAs (letI := composeAndSheafifyOplaxMonoidal J (ModuleCat.extendScalarsAbAdj R)
    (extendScalarsAbAdjunction J R).IsMonoidal)

/-- The sheafified free `R`-module functor is braided, being the strong monoidal left adjoint of
the lax braided forgetful functor. -/
noncomputable instance : (extendScalarsAb J R).Braided where
  braided := Adjunction.μ_comp_map_braiding (extendScalarsAbAdjunction J R)

end Sheaf

end CategoryTheory
