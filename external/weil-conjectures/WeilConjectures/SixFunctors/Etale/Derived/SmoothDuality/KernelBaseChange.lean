/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CommSq
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineKernelAdjunction

/-!
# Proper base change in the form of the kernel adjunction

For a cartesian square `b ≫ q = a ≫ q` with `q` proper (for `q : ℙ¹_S ⟶ S`, the two projections
`a, b` of `ℙ¹_{ℙ¹_S} = ℙ¹_S ×_S ℙ¹_S`), the base change map
`CategoryTheory.Adjunction.kernelBaseChange` of the isomorphism
`Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarCompSquareIso`) is the
derived base change map `AlgebraicGeometry.Etale.derivedBaseChangeMap`, hence invertible at finite
coefficients by the proper base change theorem
(`AlgebraicGeometry.Etale.isIso_kernelBaseChange_of_isPullback`). These are the base change
hypotheses of `CategoryTheory.Adjunction.kernelAdjunction`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- Search the braiding of `ModuleCat Λ` through its symmetric structure and braid étale sheaves
-- through `Etale.sheafBraidedCategory`, as the generic definitions of the derived tensor product
-- do.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance 20000] Etale.sheafBraidedCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`, so that the
-- generic statements specialise syntactically.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

attribute [local instance] leftDerivedUpperStarMonoidal

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Proper base change for the kernel adjunction.** For a cartesian square `b ≫ q = a ≫ q` with
`q` proper, the base change map `Lq^* Rq_* M ⟶ Ra_* Lb^* M` of the isomorphism
`Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` is invertible at finite coefficients. -/
theorem isIso_kernelBaseChange_of_isPullback {T X Y : Scheme.{u}} {a b : T ⟶ X} {q : X ⟶ Y}
    [IsProper q] (sq : IsPullback b a q q) (fg : T ⟶ Y) (ha : fg = a ≫ q) (hb : fg = b ≫ q)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Adjunction.kernelBaseChange
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
      (leftDerivedUpperStarCompSquareIso (ModuleCat.{u + 1} Λ) a b q fg ha hb) M) := by
  rw [leftDerivedUpperStarCompSquareIso_congr _ a b q fg ha hb (b ≫ q) sq.w rfl,
    Adjunction.kernelBaseChange_eq_mateEquiv_app]
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
  exact NatIso.isIso_app_of_isIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) M

end Etale

end AlgebraicGeometry
