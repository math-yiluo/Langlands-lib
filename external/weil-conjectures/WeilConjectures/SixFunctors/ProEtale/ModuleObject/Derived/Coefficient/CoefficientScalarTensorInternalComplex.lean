/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalComplexLocalizationTensorComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarComplexCounit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorHomotopyComplex

/-! # The internal complex scalar tensor square

The counit characterization of the existing total left derived tensor comparison
provides its signed-total-complex representative.
(blueprint: lem-sfb-coefficient-scalar-tensor-internal-complex)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
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

private theorem paste_scalar_complex_faces {C : Type*} [Category C]
    {A B C₀ D E : C} {a a' : A ⟶ B} {b b' : B ⟶ C₀}
    {δ : C₀ ⟶ D} {δD : A ⟶ E} {v v' : E ⟶ D}
    (ha : a = a') (hb : b = b') (hh : a' ≫ b' ≫ δ = δD ≫ v')
    (hv : v = v') : a ≫ b ≫ δ = δD ≫ v := by
  rw [ha, hb, hh, hv]

attribute [local irreducible] coefficientInternalScalarComplex

-- Compare the complex and homotopy localization tensor structures.
/-- The internal scalar tensor comparison on complex representatives.
Source: Stacks Project, Cohomology on Sites, Tag 07A4.
The complex localization tensorator is the homotopy localization tensorator: the
homotopy quotient is strict monoidal and its comparison with complex localization
has identity components. The fixed complex scalar comparison is the derived-functor
counit, by its factorization property. Substitute these two identifications into the
characterizing counit equation of the total left derived tensor comparison. This
identifies the map of the signed ordinary total tensor with the derived tensor map.
(blueprint: lem-sfb-coefficient-scalar-tensor-internal-complex). -/
theorem coefficientScalarTensor_internalComplex (Z : Scheme.{u})
    (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
    let := internalScalarMonoidal a Z
    (internalScalarExtension a Z).map
        ((ModuleRingedComparison.internalLocalizationTensorMap R Z).app (P, Q)) ≫
      coefficientInternalScalarComplex a Z (P ⊗ Q) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (Mod.extendScalars (coefficientMap a Z))).app P).app Q) =
    ((internalScalarTensorComparison a Z).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
      (coefficientInternalScalarComplex a Z P ⊗ₘ coefficientInternalScalarComplex a Z Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj Q) := by
  let := internalScalarMonoidal a Z
  have hh :
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
          Functor.LaxMonoidal.μ DerivedCategory.Qh (qS.obj (Fc.obj P)) (qS.obj (Fc.obj Q)) :=
    (Functor.leftDerivedTensorComparison_app_app_comp_tensorHom
      (Mod.extendScalars (coefficientMap a Z))
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)).symm
  simp only [ModuleRingedComparison.internalLocalizationTensorMap_app,
    internalScalarTensorComparison, internalScalarTensorIso]
  unfold internalScalarExtension
  let F := Mod.extendScalars (coefficientMap a Z)
  exact paste_scalar_complex_faces
    (congrArg F.leftDerivedFunctor.map
      (coefficientScalarTensor_complexLocalization R Z P Q))
    (coefficientScalarTensor_complexCounit a Z (P ⊗ Q)) hh
    (scalar_complex_tensor_factors a Z P Q)

end AlgebraicGeometry.ProEtale.CondensedRing
