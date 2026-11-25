/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Exactness of copower scalar extension at a geometric point -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

/-- The scalar-extension functor `V ↦ ℚ̲̄_ℓ,s ⊗_{ℚ̄_ℓ} V` at a geometric point: extend the
scalars acting on the regular module, then tensor with that module using the
tensor–coyoneda adjunction. Source: local boundary duality, Step 5, scalar extension
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedPointScalarExtension :
    ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)) ⥤ PointMod ℓ k :=
  ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointScalarsOp ℓ k) ⋙
    IsGrothendieckAbelian.tensorObj (𝟙_ (PointMod ℓ k))

/-- Scalar extension at a geometric point is left adjoint to global sections.
Source: local boundary duality, Step 5, scalar extension
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedPointScalarAdjunction :
    condensedPointScalarExtension ℓ k ⊣ pointSections ℓ k :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (pointScalarsOp ℓ k)).comp
    (IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction
      (𝟙_ (PointMod ℓ k)))

omit [IsAlgClosed k] in
/-- Scalar extension is additive and exact. Source: local boundary duality, Step 5.
Every monomorphism of vector spaces has a linear retraction. An additive left adjoint
preserves these retractions and all cokernels, hence preserves homology and finite limits.
This argument also applies to zero-dimensional spaces.
(blueprint: lem-a1-condensed-point-scalar-additive) -/
theorem condensed_point_scalar_additive :
    (condensedPointScalarExtension ℓ k).Additive  := by
  let F := condensedPointScalarExtension ℓ k
  have : F.IsLeftAdjoint := (condensedPointScalarAdjunction ℓ k).isLeftAdjoint
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

end AlgebraicGeometry.ProEtale.CondensedRing
