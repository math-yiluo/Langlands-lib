/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.SixFunctors.Monoidal
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! The scalar-first native derived projection as one fixed natural transformation.
(blueprint: def-sfb-scalar-first-projection-transformation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native derived adjunction's projection, with the scalar variable first.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md, projection formula.
Flip both tensor bifunctors in the standard right-adjoint projection construction,
using the canonical derived tensor comparison. This fixes its functors and tensor
structures once for the unit, shift, and cone calculations.
(blueprint: def-sfb-scalar-first-projection-transformation)
-/
def scalarFirstProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    tensorRight (((CondensedRing.lowerStar Λ f).rightDerivedFunctor).obj K) ⟶
      ((CondensedRing.upperStar Λ f).leftDerivedFunctor ⋙ tensorRight K) ⋙
        (CondensedRing.lowerStar Λ f).rightDerivedFunctor :=
  letI := upperStar_preservesFlat Λ f
  ((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
    (T_C := (curriedTensor (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))).flip)
    (T_D := (curriedTensor (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))).flip)
    ((flipFunctor _ _ _).map (CondensedRing.upperStar Λ f).leftDerivedTensorComparison)).app K

end AlgebraicGeometry.ProEtale.CondensedRing
