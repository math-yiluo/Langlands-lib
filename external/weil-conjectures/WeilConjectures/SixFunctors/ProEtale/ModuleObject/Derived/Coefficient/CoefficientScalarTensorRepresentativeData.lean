/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData

/-! # Basic comparison data for the scalar tensor representative reduction
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-internal)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

/-- All comparison data occurring in the signed scalar tensor equation.
The fields are the already normalized comparison maps and their stated formulas;
no object is chosen from a bare existence proposition. -/
structure CoefficientScalarTensorRepresentativeBasicData (Z : Scheme.{u}) where
  b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
    (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z)
  o : Mod.extendScalars (coefficientMap a Z) ⋙
      (ModuleRingedComparison.equivalence S Z).functor ≅
    (ModuleRingedComparison.equivalence R Z).functor ⋙ b.extension
  p : internalScalarExtension a Z ⋙
      (ModuleRingedComparison.derivedEquivalence S Z).functor ≅
    (ModuleRingedComparison.derivedEquivalence R Z).functor ⋙ b.derived
  m : b.extension.Monoidal
  t : ModuleRingedComparison.tensor R Z ⋙ b.derived ≅
    b.derived.prod b.derived ⋙ ModuleRingedComparison.tensor S Z

end AlgebraicGeometry.ProEtale.CondensedRing
