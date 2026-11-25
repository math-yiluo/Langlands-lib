/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex

/-! # A shared functor for the signed total tensor

Source: Stacks Tags 06YN and 07A4.
(blueprint: def-sf-finite-scalar-representative-total-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v
open CategoryTheory MonoidalCategory
open CategoryTheory.Functor

namespace WeilConjectures

/-- The signed total tensor, with a stable functor head in coefficient applications.
This is the existing raw total construction, with no changed tensor data.
Source: Stacks Tags 06YN and 07A4.
(blueprint: def-sf-finite-scalar-representative-total-tensor). -/
def finiteScalarRepresentativeTotalTensor
    (C : Type*) [Category.{v} C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
    [Limits.HasColimitsOfSize.{0, 0} C] :
    CochainComplex C ℤ × CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  uncurry.obj ((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

end WeilConjectures
