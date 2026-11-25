/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData
import all Mathlib.Algebra.Homology.Localization

/-! # The derived tensor counit on complex objects

The general derived tensor counit equation is written on complex representatives,
with the quotient and prolonged-functor objects in their native presentations.
(blueprint: lem-sfb-coefficient-scalar-tensor-homotopy-complex)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
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

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  ModuleRingedComparison.totalComparison ModuleRingedComparison.ordinaryTensorComparison
  Localization.Monoidal.tensorBifunctor

-- Compare the homotopy and complex presentations of the same tensor counit face.
/-- The general derived tensor counit equation on internal complex representatives.
Source: Stacks Project, Cohomology on Sites, Tag 07A4, derived tensor compatibility.
Apply Functor.leftDerivedTensorComparison_app_app_comp_tensorHom to the two
homotopy quotient objects. The quotient tensorator is an identity, so its tensor
object is the quotient of the complex tensor. Prolongation to the homotopy
category sends a quotient complex to the quotient of its prolongation. The
homotopy oplax tensor map is the quotient of the complex oplax tensor map.
These identifications give exactly the displayed complex formula.
(blueprint: lem-sfb-coefficient-scalar-tensor-homotopy-complex). -/
private theorem coefficientScalarTensor_homotopyComplex_private (Z : Scheme.{u})
    (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
    let := internalScalarMonoidal a Z
    let F := Mod.extendScalars (coefficientMap a Z)
    let qR := HomotopyCategory.quotient (ModuleRingedComparison.internalModules R Z) (.up ℤ)
    let qS := HomotopyCategory.quotient (ModuleRingedComparison.internalModules S Z) (.up ℤ)
    let Fc := F.mapHomologicalComplex (.up ℤ)
    F.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Qh (qR.obj P) (qR.obj Q)) ≫
        F.leftDerivedFunctorCounit.app (qR.obj (P ⊗ Q)) ≫
        DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
      ((F.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
          (DerivedCategory.Q.obj Q)) ≫
        (F.leftDerivedFunctorCounit.app (qR.obj P) ⊗ₘ
          F.leftDerivedFunctorCounit.app (qR.obj Q)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh (qS.obj (Fc.obj P)) (qS.obj (Fc.obj Q)) := by
  let := internalScalarMonoidal a Z
  exact (Functor.leftDerivedTensorComparison_app_app_comp_tensorHom
    (Mod.extendScalars (coefficientMap a Z))
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)).symm

/-- Public export of the private `coefficientScalarTensor_homotopyComplex_private`
(used by `import all` importers; linter.privateModule). -/
alias coefficientScalarTensor_homotopyComplex := coefficientScalarTensor_homotopyComplex_private

end AlgebraicGeometry.ProEtale.CondensedRing
