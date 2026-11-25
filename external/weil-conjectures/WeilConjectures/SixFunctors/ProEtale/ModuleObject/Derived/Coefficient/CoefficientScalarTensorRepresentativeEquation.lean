/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeData

/-! # Data and equation for the scalar tensor representative reduction

This module packages the comparison data used by the two strict substeps of the
signed representative argument.
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

/-- The signed representative equality for a fixed pair of section complexes. -/
def coefficientScalarTensorRepresentativeEquation (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (P Q : CochainComplex (ModuleRingedComparison.modules R Z) ℤ) : Prop :=
  d.b.derived.map ((ModuleRingedComparison.qTensor R Z).app (P, Q)) ≫
      SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        d.b.extension d.b.extension_additive d.b.derived d.b.counit
        ((ModuleRingedComparison.totalTensor R Z).obj (P, Q)) ≫
    DerivedCategory.Q.map (coefficientSectionScalarTotal a Z d.b d.m P Q) =
  d.t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (ModuleRingedComparison.tensor S Z).map (Prod.mkHom
        (SheafOfModules.scalarPairComplexComparison
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
          (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
          d.b.extension d.b.extension_additive d.b.derived d.b.counit P)
        (SheafOfModules.scalarPairComplexComparison
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
          (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
          d.b.extension d.b.extension_additive d.b.derived d.b.counit Q)) ≫
    (ModuleRingedComparison.qTensor S Z).app
      ((d.b.extension.mapHomologicalComplex (.up ℤ)).obj P,
        (d.b.extension.mapHomologicalComplex (.up ℤ)).obj Q)

end AlgebraicGeometry.ProEtale.CondensedRing
