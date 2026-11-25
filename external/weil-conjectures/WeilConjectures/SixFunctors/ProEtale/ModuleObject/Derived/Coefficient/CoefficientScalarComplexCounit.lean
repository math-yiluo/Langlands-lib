/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalComplexLocalizationTensorComparison

/-! # The scalar complex comparison is the derived counit

The canonical complex scalar comparison agrees with the total left derived
functor counit at the homotopy quotient of that complex.
(blueprint: lem-sfb-coefficient-scalar-complex-counit)
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

/-- The fixed scalar complex comparison is the derived counit.
Source: Stacks Project, Cohomology on Sites, Tag 07A4, scalar localization comparison.
Expand the fixed complex comparison and use the factorization equation for the
isomorphism between the exact derived functor and the total left derived functor.
The comparison between complex and homotopy localizations has identity components.
Its images under the two functors are identities, so cancellation leaves the counit.
(blueprint: lem-sfb-coefficient-scalar-complex-counit). -/
private theorem coefficientScalarTensor_complexCounit_private (Z : Scheme.{u})
    (K : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
    coefficientInternalScalarComplex a Z K =
      (Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) := by
  unfold coefficientInternalScalarComplex
  rw [← Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac]
  congr 1
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change _ = (Mod.extendScalars (coefficientMap a Z)).mapDerivedCategory.map (𝟙 _) ≫
    _ ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)
  erw [(Mod.extendScalars (coefficientMap a Z)).mapDerivedCategory.map_id _,
    DerivedCategory.Qh.map_id _]
  simp only [Category.id_comp, Category.comp_id]

/-- Public export of the private `coefficientScalarTensor_complexCounit_private`
(used by `import all` importers; linter.privateModule). -/
alias coefficientScalarTensor_complexCounit := coefficientScalarTensor_complexCounit_private

attribute [local irreducible] coefficientInternalScalarComplex

-- Check the counit and localization corner with native functor object types.
/-- The tensor of the two scalar complex comparisons, followed by localization,
is the tensor of the two derived counits followed by homotopy localization.
Use the two scalar-counit equations, tensor their components, and compose with
the equality of complex and homotopy localization tensorators. -/
private theorem scalar_complex_tensor_factors_private (Z : Scheme.{u})
    (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
    let F := Mod.extendScalars (coefficientMap a Z)
    let Fc := F.mapHomologicalComplex (.up ℤ)
    let qR := HomotopyCategory.quotient (ModuleRingedComparison.internalModules R Z) (.up ℤ)
    let qS := HomotopyCategory.quotient (ModuleRingedComparison.internalModules S Z) (.up ℤ)
    let c (K : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
        F.leftDerivedFunctor.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj (Fc.obj K) :=
      coefficientInternalScalarComplex a Z K
    (c P ⊗ₘ c Q) ≫ Functor.LaxMonoidal.μ DerivedCategory.Q (Fc.obj P) (Fc.obj Q) =
      (F.leftDerivedFunctorCounit.app (qR.obj P) ⊗ₘ
        F.leftDerivedFunctorCounit.app (qR.obj Q)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh (qS.obj (Fc.obj P)) (qS.obj (Fc.obj Q)) := by
  dsimp only
  let F := Mod.extendScalars (coefficientMap a Z)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let qR := HomotopyCategory.quotient (ModuleRingedComparison.internalModules R Z) (.up ℤ)
  let qS := HomotopyCategory.quotient (ModuleRingedComparison.internalModules S Z) (.up ℤ)
  let c (K : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
      F.leftDerivedFunctor.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj (Fc.obj K) :=
    coefficientInternalScalarComplex a Z K
  have hct : (c P ⊗ₘ c Q) =
      (F.leftDerivedFunctorCounit.app (qR.obj P) ⊗ₘ
        F.leftDerivedFunctorCounit.app (qR.obj Q)) :=
    congrArg₂ (fun f g ↦ f ⊗ₘ g)
      (coefficientScalarTensor_complexCounit a Z P) (coefficientScalarTensor_complexCounit a Z Q)
  have hμ : Functor.LaxMonoidal.μ DerivedCategory.Q (Fc.obj P) (Fc.obj Q) =
      Functor.LaxMonoidal.μ DerivedCategory.Qh (qS.obj (Fc.obj P)) (qS.obj (Fc.obj Q)) :=
    coefficientScalarTensor_complexLocalization S Z (Fc.obj P) (Fc.obj Q)
  exact congrArg₂ (fun v u ↦ v ≫ u) hct hμ

/-- Public export of the private `scalar_complex_tensor_factors_private`
(used by `import all` importers; linter.privateModule). -/
alias scalar_complex_tensor_factors := scalar_complex_tensor_factors_private

end AlgebraicGeometry.ProEtale.CondensedRing
