/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# The derived pushforwards and the derived tensor product are triangulated

The derived functors on the unbounded derived categories of étale sheaves are triangulated, for
the commutations with shifts of `WeilConjectures.SixFunctors.Etale.Derived.Shift`:

* `Rg_*` is right adjoint to the triangulated functor `D(g^*)` induced by the exact pullback,
  and its commutation with shifts is the one induced by the adjunction, so it is triangulated
  by `Adjunction.isTriangulated_rightAdjoint`;
* `Rf_! = D(i_!) ⋙ Rg_*` for the chosen compactification `(i, g)` is a composite of two
  triangulated functors;
* `- ⊗ᴸ K` is the tensor product of the monoidal derived category, which is triangulated in
  its first variable (`DerivedCategory.isTriangulated_tensorRight`).

## Main statements

- `AlgebraicGeometry.Etale.isTriangulated_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.isTriangulated_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.isTriangulated_leftDerivedUpperStar`
- `AlgebraicGeometry.Etale.isTriangulated_derivedTensorRight`
- `AlgebraicGeometry.Etale.isTriangulated_derivedTensor_obj`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The total right derived pushforward `Rg_*` is triangulated, being right adjoint to the
triangulated functor `D(g^*)` with the induced commutation with shifts. -/
instance isTriangulated_rightDerivedLowerStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (R((g)_*[A])).IsTriangulated :=
  have := (mapDerivedUpperStarLowerStarAdjunction A g).commShift_of_leftAdjoint ℤ
  (mapDerivedUpperStarLowerStarAdjunction A g).isTriangulated_rightAdjoint

/-- The derived lower shriek `Rf_!` is triangulated: for the chosen compactification `(i, g)`
of `f` it is the composite of the triangulated functors `D(i_!)` and `Rg_*`. -/
instance isTriangulated_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (R(f)_![A]).IsTriangulated :=
  inferInstanceAs ((D(((HasCompactification.compactification f).i)_!open[A]) ⋙
    R(((HasCompactification.compactification f).g)_*[A])).IsTriangulated)

section Monoidal

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The derived pullback `Lg^*` is a triangulated functor, being isomorphic, compatibly with the
shifts, to the functor `D(g^*)` induced by the exact pullback. -/
instance isTriangulated_leftDerivedUpperStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).IsTriangulated :=
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm

/-- Tensoring on the right with a fixed complex, `M ↦ M ⊗ᴸ K`, commutes with shifts. -/
noncomputable instance commShiftDerivedTensorRight
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedTensorRight A X K).CommShift ℤ :=
  inferInstanceAs (((derivedTensor A X).flip.obj K).CommShift ℤ)

attribute [local instance] Sheaf.monoidalCategory in
/-- Tensoring on the right with a fixed complex, `M ↦ M ⊗ᴸ K`, is triangulated. -/
instance isTriangulated_derivedTensorRight
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedTensorRight A X K).IsTriangulated :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A))).flip.obj K).IsTriangulated)

attribute [local instance] Sheaf.monoidalCategory in
/-- Tensoring on the left with a fixed complex, `M ↦ K ⊗ᴸ M`, is triangulated. -/
instance isTriangulated_derivedTensor_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj K).IsTriangulated :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A))).obj K).IsTriangulated)

/-- Tensoring on the right with a fixed complex, `M ↦ M ⊗ᴸ K`, is triangulated. This restates
`isTriangulated_derivedTensorRight` in the `(derivedTensor A X).flip.obj K` form, so that
instance search finds it for functors written in that form. -/
instance isTriangulated_derivedTensor_flip_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).flip.obj K).IsTriangulated :=
  inferInstanceAs (derivedTensorRight A X K).IsTriangulated

end Monoidal

end Etale

end AlgebraicGeometry
