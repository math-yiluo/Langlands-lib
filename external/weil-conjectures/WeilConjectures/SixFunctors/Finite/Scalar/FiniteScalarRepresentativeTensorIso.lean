/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalTensor
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution

/-! # Fixed-scalar representatives on the shared signed total functor

Source: Stacks Tags 06YN and 07A4.
(blueprint: def-sf-finite-scalar-representative-tensor-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

/-- The existing representative isomorphism, assembled by its specified components.
Source: Stacks Tag 07A4, inversion of the K-flat localization tensorators.
(blueprint: def-sf-finite-scalar-representative-tensor-iso). -/
@[irreducible] def finiteScalarRepresentativeTensorIso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (T : Scheme.{u})
    (P : ObjectProperty (CochainComplex (Sheaf (ProEt.topology T) B) ℤ))
    (hP : ∀ Z, P Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z) :
    (P.ι.prod P.ι) ⋙ finiteScalarRepresentativeTotalTensor (Sheaf (ProEt.topology T) B) ⋙
      DerivedCategory.Q ≅
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙
        uncurry.obj (ProEtale.derivedTensor B T) :=
  NatIso.ofComponents
    (fun Z ↦ (finiteScalarFixedTensorRepresentativeForCoefficients B T P hP).app Z)
    (fun {_Z _W} f ↦
      (finiteScalarFixedTensorRepresentativeForCoefficients B T P hP).hom.naturality f)

/-- The shared representative retains the actual localization tensorator components.
Source: Stacks Tag 07A4.
(blueprint: def-sf-finite-scalar-representative-tensor-iso). -/
theorem finiteScalarRepresentativeTensorIso_hom_app
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (T : Scheme.{u})
    (P : ObjectProperty (CochainComplex (Sheaf (ProEt.topology T) B) ℤ))
    (hP : ∀ Z, P Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (Z : P.FullSubcategory × P.FullSubcategory) :
    (finiteScalarRepresentativeTensorIso B T P hP).hom.app Z =
      (finiteScalarFixedTensorRepresentativeForCoefficients B T P hP).hom.app Z := by
  unfold finiteScalarRepresentativeTensorIso
  rfl

end WeilConjectures
