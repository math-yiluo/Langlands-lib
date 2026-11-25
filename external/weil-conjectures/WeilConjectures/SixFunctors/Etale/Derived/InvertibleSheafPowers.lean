/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible

/-!
# Tensor powers of an invertible sheaf in the derived category

Let `L` be an `A`-valued étale sheaf with a tensor inverse `L'`. Placed in degree zero, `L[0]`
has the tensor inverse `L'[0]` in `D(X_ét)`
(`CategoryTheory.MonoidalCategory.TensorInverse.singleFunctor`), and the integer tensor powers of
`L[0]` in `D(X_ét)` are the integer tensor powers of `L` placed in degree zero
(`CategoryTheory.MonoidalCategory.TensorInverse.zpowSingleFunctorIso`): `L` and `L'` are flat, so
the derived tensor products with them are underived.

## Main definitions

- `CategoryTheory.MonoidalCategory.TensorInverse.singleFunctor`: the tensor inverse `L'[0]` of
  `L[0]`.
- `CategoryTheory.MonoidalCategory.TensorInverse.zpowSingleFunctorIso`:
  `L[0]^{⊗ m} ≅ (L^{⊗ m})[0]`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Etale

namespace CategoryTheory.MonoidalCategory.TensorInverse

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The tensor powers of a flat sheaf placed in degree zero are the tensor powers of the sheaf
placed in degree zero. -/
noncomputable def tensorPowNatSingleFunctorIso (F : Sheaf X.smallEtaleTopology A)
    (hF : ObjectProperty.flat F) : (n : ℕ) →
    tensorPowNat ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F) n ≅
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj (tensorPowNat F n)
  | 0 => (singleFunctorObjUnitIso A X).symm
  | n + 1 => whiskerLeftIso _ (tensorPowNatSingleFunctorIso F hF n) ≪≫
      singleFunctorObjTensorIso F _ hF

variable {L : Sheaf X.smallEtaleTopology A} (e : TensorInverse L)

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
include e in
/-- A sheaf `L` with a tensor inverse `L'` is flat. -/
lemma flat : ObjectProperty.flat L :=
  ObjectProperty.flat_of_tensorIso e.rightIso

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
/-- The tensor inverse of a sheaf is flat. -/
lemma flat_obj : ObjectProperty.flat e.obj :=
  ObjectProperty.flat_of_tensorIso e.leftIso

/-- A tensor inverse `L'` of a sheaf `L` gives the tensor inverse `L'[0]` of `L[0]` in
`D(X_ét)`. -/
noncomputable def singleFunctor :
    TensorInverse ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj L) where
  obj := (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj e.obj
  rightIso := singleFunctorObjTensorIso L e.obj e.flat ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e.rightIso ≪≫ singleFunctorObjUnitIso A X
  leftIso := singleFunctorObjTensorIso e.obj L e.flat_obj ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e.leftIso ≪≫ singleFunctorObjUnitIso A X

/-- The integer tensor powers of `L[0]` in `D(X_ét)` are the integer tensor powers of `L` placed
in degree zero. -/
noncomputable def zpowSingleFunctorIso : (m : ℤ) →
    e.singleFunctor.zpow m ≅
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj (e.zpow m)
  | .ofNat n => tensorPowNatSingleFunctorIso L e.flat n
  | .negSucc n => tensorPowNatSingleFunctorIso e.obj e.flat_obj (n + 1)

end CategoryTheory.MonoidalCategory.TensorInverse
