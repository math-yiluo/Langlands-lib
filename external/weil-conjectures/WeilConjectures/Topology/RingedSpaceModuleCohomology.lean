/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Cohomology of modules on a ringed space

Source: Stacks Project, Cohomology, Section 20.11, Tag 01DZ
(blueprint: def-sc-ringed-space-module-cohomology).

For a ringed space `X` and an `O_X`-module `F` (an object of
`SheafOfModules (moduleRings X)`), `H^p(X, F)` is the `p`-th right derived functor of the
global sections functor `Γ(X, -) : Mod(O_X) ⥤ Mod_{O_X(X)}`, computed in the category of
`O_X`-modules. This is the declaration later nodes about cohomology of `O_X`-modules on a
ringed space cite.

## Main definitions and statements

- `globalSectionsFunctor`: `Γ(X, -)` on `O_X`-modules, valued in `O_X(X)`-modules; the
  ringed-space analogue of `AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor`.
- `moduleCohomology`: `H^p(X, -) := R^p Γ(X, -)` (`Functor.rightDerived`).
- `globalSectionsComplex`: global sections of a chosen injective resolution.
- `moduleCohomology_iso_resolution`: `H^p(X, F) ≅ H^p(Γ(X, I^•))` for every injective
  resolution `F[0] → I^•`.
- `moduleCohomology_independent`: the cohomology of `Γ(X, I^•)` does not depend on `I^•`.

## Implementation notes

Mathlib's `CategoryTheory.Sheaf.H` (`TopCat.Sheaf` cohomology) is an `Ext`-group from the
constant sheaf `ℤ` in *abelian* sheaves, i.e. derived functors of `Γ` on `Ab(X)`; it has no
`O_X(X)`-module structure and is not computed in `Mod(O_X)`. The source's
`AlgebraicGeometry.Scheme.Modules.H` applies it to the underlying abelian sheaf of a module on
a scheme. Both agree with `moduleCohomology` only through the theorem that injective
`O_X`-modules are `Γ`-acyclic as abelian sheaves (Stacks, Tag 01E3); here the definition is
the source's, in `Mod(O_X)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSpace

/-- The global sections functor `Γ(X, -) : Mod(O_X) ⥤ Mod_{O_X(X)}`, `F ↦ F(X)`, on modules
over a ringed space: evaluation at the whole space `⊤`.
Source: Stacks Project, Cohomology, Section 20.11, Tag 01DZ
(blueprint: def-sc-ringed-space-module-cohomology). -/
noncomputable def globalSectionsFunctor (X : RingedSpace.{u}) :
    SheafOfModules.{u} (moduleRings X) ⥤ ModuleCat.{u} ((moduleRings X).obj.obj (op ⊤)) :=
  SheafOfModules.evaluation.{u} (moduleRings X) (op ⊤)

/-- Global sections is additive: it is the composite of the additive forgetful functor
and additive evaluation on presheaves of modules.
Source: Stacks Project, Cohomology, Section 20.11, Tag 01DZ
(blueprint: def-sc-ringed-space-module-cohomology). -/
instance globalSectionsFunctor_additive (X : RingedSpace.{u}) :
    (globalSectionsFunctor X).Additive :=
  inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X).obj (op ⊤)).Additive)

/-- Cohomology of modules on a ringed space: `H^p(X, -)` is the `p`-th right derived functor
of global sections `Γ(X, -)` on the abelian category of `O_X`-modules, which has enough
injectives by `moduleSheaves_abelian_enoughInjectives`
(blueprint: lem-sc-ringed-space-module-sheaves-enough-injectives).
Source: Stacks Project, Cohomology, Section 20.11, Tag 01DZ
(blueprint: def-sc-ringed-space-module-cohomology). 
(blueprint: def-sc-sheaf-cohomology-functor)
-/
noncomputable def moduleCohomology (X : RingedSpace.{u}) (p : ℕ) :
    SheafOfModules.{u} (moduleRings X) ⥤ ModuleCat.{u} ((moduleRings X).obj.obj (op ⊤)) :=
  letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  (globalSectionsFunctor X).rightDerived p

/-- Apply global sections termwise to an injective resolution: the complex `Γ(X, I^•)`.
Source: Stacks Project, Cohomology, Section 20.11, Tag 01DZ
(blueprint: def-sc-ringed-space-module-cohomology). -/
noncomputable def globalSectionsComplex {X : RingedSpace.{u}}
    {F : SheafOfModules.{u} (moduleRings X)}
    (I : CategoryTheory.InjectiveResolution F) : CochainComplex
      (ModuleCat.{u} ((moduleRings X).obj.obj (op ⊤))) ℕ :=
  ((globalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

/-- For every injective resolution `F[0] → I^•` of an `O_X`-module, `H^p(X, F)` is the
`p`-th cohomology of the complex `Γ(X, I^•)`.
Source: Stacks Project, Cohomology, Sections 20.11--20.12, Tag 01DZ
(blueprint: def-sc-ringed-space-module-cohomology).

Proof: Enough injectives is supplied by
`lem-sc-ringed-space-module-sheaves-enough-injectives`. By `def-sp-left-exact-additive`,
the right derived functor is formed by applying the additive global-sections functor
to a chosen injective resolution and taking degree `p` homology. Compare that resolution
with `I` using `def-sp-injective-resolutions`: the comparison maps extending the identity
of `F` are a homotopy equivalence, which the additive functor `Γ(X, -)` preserves, hence
an isomorphism on degree-`p` homology. Mathlib's `InjectiveResolution.isoRightDerivedObj`
is this comparison. -/
theorem moduleCohomology_iso_resolution (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X))
    (I : CategoryTheory.InjectiveResolution F) (p : ℕ) :
    Nonempty ((moduleCohomology X p).obj F ≅ (globalSectionsComplex I).homology p) := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  exact ⟨I.isoRightDerivedObj (globalSectionsFunctor X) p⟩

/-- The cohomology of `Γ(X, I^•)` is independent, up to isomorphism, of the chosen injective
resolution. Source: Stacks Project, Cohomology, Section 20.11, Tag 01DZ
(blueprint: def-sc-ringed-space-module-cohomology).

Proof: In the abelian module-sheaf category
(`lem-sc-ringed-space-module-sheaves-enough-injectives`), the two injective resolutions
(`def-sp-injective-resolutions`) are homotopy equivalent by comparison maps extending
the identity of `F`. The additive global-sections functor preserves that homotopy
equivalence. Taking degree `p` homology yields inverse isomorphisms; this is the
resolution-independence construction for `def-sp-left-exact-additive`. -/
theorem moduleCohomology_independent (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X))
    (I J : CategoryTheory.InjectiveResolution F) (p : ℕ) :
    Nonempty ((globalSectionsComplex I).homology p ≅ (globalSectionsComplex J).homology p) := by
  obtain ⟨eI⟩ := moduleCohomology_iso_resolution X F I p
  obtain ⟨eJ⟩ := moduleCohomology_iso_resolution X F J p
  exact ⟨eI.symm ≪≫ eJ⟩


end AlgebraicGeometry.RingedSpace
