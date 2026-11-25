/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear

/-! # Signed principal cones and derived tensor

Source: blueprint, derived Nakayama resolution, On X paragraph.
(blueprint: lem-pe-principal-cone-tensor-normalization).
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PrincipalNormalization

attribute [local irreducible] upperStarFromPoint
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

section ScalarTools
universe v
open Category BraidedCategory
namespace UnitEndScalars
variable (A : Type u) [Category.{v} A] [Preadditive A]
  [MonoidalCategory A] [MonoidalPreadditive A]
@[instance_reducible] private def scalarRing : CommRing (End (𝟙_ A)) :=
  { (inferInstance : Ring (End (𝟙_ A))) with
    mul_comm := fun a b ↦ by
      apply End.ext
      have h := unitEndAction_naturality a.asHom b
      simpa only [End.mul_asHom, unitEndAction_unit] using h }
private def Scalars := End (𝟙_ A)
private instance : CommRing (Scalars A) := scalarRing A
variable [BraidedCategory A]
end UnitEndScalars
end ScalarTools

private def scalar (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    UnitEndScalars.Scalars (AdicCompletion.Modules l E X) :=
  End.of ((DerivedNakayama.regularPullbackIso l E X).inv ≫
    (DerivedNakayama.pullback l E X).map d.asHom ≫
    (DerivedNakayama.regularPullbackIso l E X).hom)

section Generic
universe v z
variable {A : Type*} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type z} [CommRing B] [Linear B A] [MonoidalLinear B A]
local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

end Generic

end AlgebraicGeometry.ProEtale.PrincipalNormalization
