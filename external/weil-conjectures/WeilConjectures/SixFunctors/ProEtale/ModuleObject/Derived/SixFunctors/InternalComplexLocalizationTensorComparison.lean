/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedTensorData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Complex and homotopy localization tensor maps

The strict monoidal homotopy quotient and its identity-component comparison with
complex localization identify the two tensor maps on complex representatives.
(blueprint: lem-sfb-internal-complex-localization-tensor-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Complex and homotopy localization have the same tensorator on complex objects.
Source: Stacks Project, Cohomology on Sites, Tag 06YU.
The homotopy quotient tensorator is the identity. The comparison of its composite
with homotopy localization and complex localization also has identity components.
Expand the transported tensorator, then remove the identity factors. This gives
exactly the homotopy localization tensorator.
(blueprint: lem-sfb-internal-complex-localization-tensor-comparison). -/
private theorem coefficientScalarTensor_complexLocalization_private
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) (K L : CochainComplex (ModuleRingedComparison.internalModules Λ Z) ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q K L =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
        ((HomotopyCategory.quotient _ (.up ℤ)).obj L) := by
  let q := HomotopyCategory.quotient (ModuleRingedComparison.internalModules Λ Z) (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (ModuleRingedComparison.internalModules Λ Z)
  have ht : Functor.LaxMonoidal.μ DerivedCategory.Q K L =
      (e.inv.app K ⊗ₘ e.inv.app L) ≫
        Functor.LaxMonoidal.μ (q ⋙ DerivedCategory.Qh) K L ≫ e.hom.app (K ⊗ L) := by
    rfl
  have hc : Functor.LaxMonoidal.μ (q ⋙ DerivedCategory.Qh) K L =
      Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj K) (q.obj L) := by
    change Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj K) (q.obj L) ≫
      DerivedCategory.Qh.map (𝟙 (q.obj (K ⊗ L))) = _
    erw [DerivedCategory.Qh.map_id]
    exact Category.comp_id _
  have he (H : CochainComplex (ModuleRingedComparison.internalModules Λ Z) ℤ) :
      e.inv.app H = 𝟙 (DerivedCategory.Q.obj H) := rfl
  have he' : e.hom.app (K ⊗ L) = 𝟙 (DerivedCategory.Q.obj (K ⊗ L)) := rfl
  rw [ht, hc, he, he, he']
  simp only [id_tensorHom_id, Category.id_comp]
  exact Category.comp_id _

/-- Public export of the private `coefficientScalarTensor_complexLocalization_private`
(used by `import all` importers; linter.privateModule). -/
alias coefficientScalarTensor_complexLocalization :=
  coefficientScalarTensor_complexLocalization_private

end AlgebraicGeometry.ProEtale.CondensedRing
