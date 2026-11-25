/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology

/-! # Module cohomology on open subsets and its restriction maps

Source: Stacks Project, Cohomology, Tags 01DZ, 01E1 and 01EB
(blueprint: def-sc-open-module-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- Sections over an open, as an additive group valued functor on `O_X`-modules.
Source: Stacks, Tags 01DZ and 01EB (blueprint: def-sc-open-module-cohomology). -/
noncomputable def openModuleSections (X : RingedSpace.{u}) (U : Opens X) :
    SheafOfModules.{u} (moduleRings X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget (moduleRings X) ⋙
    PresheafOfModules.toPresheaf (moduleRings X).obj ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- Sections over an open is additive.
Source: Stacks, Tag 01DZ (blueprint: def-sc-open-module-cohomology). -/
instance openModuleSections_additive (X : RingedSpace.{u}) (U : Opens X) :
    (openModuleSections X U).Additive :=
  inferInstanceAs ((SheafOfModules.forget (moduleRings X) ⋙
    PresheafOfModules.toPresheaf (moduleRings X).obj ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).Additive)

/-- The right derived functor of sections over an open, computed with injective
`O_X`-module resolutions. Restriction of such a resolution is injective (Tag 01E1),
so this is `H^p(U,F|_U)`, with the same definition as `moduleCohomology`.
Source: Stacks, Tags 01DZ and 01E1 (blueprint: def-sc-open-module-cohomology). -/
noncomputable def openModuleCohomology (X : RingedSpace.{u}) (p : ℕ) (U : Opens X) :
    SheafOfModules.{u} (moduleRings X) ⥤ AddCommGrpCat.{u} :=
  letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  (openModuleSections X U).rightDerived p

/-- Canonical cohomology restriction, obtained by deriving sectionwise restriction.
Source: Stacks, Tags 01DZ and 01EB (blueprint: def-sc-open-module-cohomology). -/
noncomputable def openModuleCohomologyRestriction (X : RingedSpace.{u}) (p : ℕ)
    {U V : Opens X} (i : V ⟶ U) :
    openModuleCohomology X p U ⟶ openModuleCohomology X p V :=
  letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  NatTrans.rightDerived
    (Functor.whiskerLeft (SheafOfModules.forget (moduleRings X) ⋙
      PresheafOfModules.toPresheaf (moduleRings X).obj)
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map i.op)) p

end AlgebraicGeometry.RingedSpace
