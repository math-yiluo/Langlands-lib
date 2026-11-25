/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Rational localizing categories and tensoring with a fixed line

Source: blueprint localizing closure and Tate twist conventions.
(blueprint: def-sfb-rational-localizing-twist).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The localizing derived category used in the affine-line statement.
Source: blueprint `definition-localizing-subcategory` (blueprint:
theorem-f-shriek-ell-adic-coefficients). -/
abbrev rationalLocalizingCategory
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory

/-- The full inclusion of the localizing category into the ambient derived category.
Source: blueprint `definition-localizing-subcategory` (blueprint:
theorem-f-shriek-ell-adic-coefficients). -/
noncomputable abbrev rationalLocalizingInclusion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)).ι

/-- Derived tensor with a specified Tate line, placed in degree zero.
Source: blueprint `definition-tate-twists` (blueprint: theorem-f-shriek-ell-adic-coefficients). -/
noncomputable def rationalTwistFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) :=
  (derivedTensor Λ X).flip.obj ((DerivedCategory.singleFunctor _ 0).obj L)

end AlgebraicGeometry.ProEtale.CondensedRing
