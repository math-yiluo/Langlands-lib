/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# The right adjoint of the direct image along a finite étale morphism

For a finite étale morphism `e : V ⟶ X` the direct image `e_*` of étale sheaves is exact, being
both a left adjoint (of `e^*`, `AlgebraicGeometry.Etale.lowerStarUpperStarAdjunctionOfIsFinite`)
and a right adjoint (of `e^*`). Consequently `Re_! ≅ Re_* ≅ D(e_*)`, and `D(e_*) ⊣ D(e^*)` on the
derived categories (`lemma-affine-space-etale-localization--4`).

The blueprint states the proposition on the small pro-étale sites; the pro-étale direct image along
a finite étale morphism is not available in the library, and the statement is made on the small
étale sites, where the exceptional inverse image of the library lives.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {V X : Scheme.{u}} (e : V ⟶ X) [IsFinite e] [_root_.AlgebraicGeometry.Etale e]

/-- The direct image along a finite étale morphism preserves finite limits, being right adjoint
to the pullback. -/
instance preservesFiniteLimits_lowerStar_of_isFinite_of_etale :
    PreservesFiniteLimits (e)_*[A] :=
  have : PreservesLimitsOfSize.{0, 0} (e)_*[A] :=
    (Etale.upperStarLowerStarAdjunction A e).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _

/-- For a finite étale `e`, the exact functor `D(e_*)` is left adjoint to `D(e^*)`, the derived
version of `AlgebraicGeometry.Etale.lowerStarUpperStarAdjunctionOfIsFinite`. -/
noncomputable def mapDerivedCategoryLowerStarUpperStarAdjunctionOfIsFinite :
    D((e)_*[A]) ⊣ D((e)^*[A]) :=
  (Etale.lowerStarUpperStarAdjunctionOfIsFinite A e).mapDerivedCategoryAdjunction

/-- For a finite étale `e`, the derived compactly supported direct image is the exact direct
image, `Re_! ≅ Re_* ≅ D(e_*)`: `e` is proper and `e_*` is exact. -/
noncomputable def rightDerivedLowerShriekIsoMapDerivedCategoryOfIsFiniteOfEtale
    [HasCompactification e] : R(e)_![A] ≅ D((e)_*[A]) :=
  rightDerivedLowerShriekIsoRightDerivedLowerStar A e ≪≫
    (e)_*[A].rightDerivedFunctorIsoMapDerivedCategory

/-- Blueprint `lemma-affine-space-etale-localization--4`: The right adjoint for a finite etale
morphism.

For a finite étale `e`, the compactly supported direct image `Re_! ≅ D(e_*)` is left adjoint to
the pullback `D(e^*)`. -/
noncomputable def rightDerivedLowerShriekUpperStarAdjunctionOfIsFiniteOfEtale
    [HasCompactification e] : R(e)_![A] ⊣ D((e)^*[A]) :=
  (mapDerivedCategoryLowerStarUpperStarAdjunctionOfIsFinite A e).ofNatIsoLeft
    (rightDerivedLowerShriekIsoMapDerivedCategoryOfIsFiniteOfEtale A e).symm

/-- Blueprint `lemma-affine-space-etale-localization--4`: The right adjoint for a finite etale
morphism.

Let `e : V ⟶ X` be finite étale. Then the direct image `e_*` is exact, and on the derived
categories `Re_! ≅ Re_* ≅ D(e_*)` with `D(e_*) ⊣ D(e^*)`, the pullback being the inverse image. -/
theorem exact_lowerStar_and_rightDerivedLowerShriek_adjunction_of_isFinite_of_etale
    [HasCompactification e] :
    (PreservesFiniteLimits (e)_*[A] ∧ PreservesFiniteColimits (e)_*[A]) ∧
      Nonempty (R(e)_![A] ≅ R((e)_*[A])) ∧ Nonempty (R((e)_*[A]) ≅ D((e)_*[A])) ∧
      Nonempty (D((e)_*[A]) ⊣ D((e)^*[A])) :=
  ⟨⟨inferInstance, inferInstance⟩, ⟨rightDerivedLowerShriekIsoRightDerivedLowerStar A e⟩,
    ⟨(e)_*[A].rightDerivedFunctorIsoMapDerivedCategory⟩,
    ⟨mapDerivedCategoryLowerStarUpperStarAdjunctionOfIsFinite A e⟩⟩

end Etale

end AlgebraicGeometry
