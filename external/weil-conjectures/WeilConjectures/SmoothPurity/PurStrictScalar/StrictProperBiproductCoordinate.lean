/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarTowerMates
public import WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData
import all WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.Derived.DerivedAdjunctionCochainUnit
import WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence

/-! Coordinate form of the strict finite proper biproduct comparison.

Source: Stacks 0B56, 0940, 0944.
(blueprint: lem-pur-compact-support-strict-scalar-mate-strict-coordinate)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Limits.limit
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

section LocalizationHelpers
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F G : A ⥤ B) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

end LocalizationHelpers

universe u

private def basisSection (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (k : Fin d) (V : W.ProEtᵒᵖ) : S.obj.obj V := by
  classical
  exact ((Pi.lift (fun j : Fin d ↦ if k = j then 𝟙 _ else 0) ≫ b.hom).val.app V)
    (@id (R.obj.obj V) 1)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

end WeilConjectures.PurStrictScalar
