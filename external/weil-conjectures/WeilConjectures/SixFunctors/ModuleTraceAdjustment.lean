/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.SixFunctors.DerivedTraceAdjustment

/-! # Module-valued trace adjustment before fixing the coefficient objects -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Trace adjustment for module sheaves before specializing the coefficient objects.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, transport through a presentation.
(auxiliary; not a blueprint node)

Proof: inverse image along the isomorphism is an equivalence, so its adjoint direct
image is an equivalence. The adjunction unit followed by direct image of bL is an
isomorphism from L to the direct image of B. Apply the derived trace-adjustment
calculation to this isomorphism, v and the component of z. Its component equation is
exactly the displayed equality for the native module-valued functors. -/
theorem exists_moduleTraceAdjustment
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ Z) (q : X ⟶ Z) [IsProper q]
    (w : e.hom ≫ g = q) (B : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y)
    (bL v : (ordinaryFinitePullback A e.hom).obj L ≅ B)
    (z : ordinaryFinitePullback A e.hom ⋙ ordinaryFinitePushforward A e.hom ≅ 𝟭 _)
    {U W : DerivedCategoryModule A Z}
    (τ : (ordinaryFinitePushforward A g).obj L ⟶ U) (j : U ⟶ W) :
    ∃ a : B ≅ B,
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a.hom ≫
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) q).hom.app B ≫
          (ordinaryFinitePushforward A q).map v.inv ≫
          (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) e.hom g q w).inv.app
            ((ordinaryFinitePullback A e.hom).obj L) ≫
          (ordinaryFinitePushforward A g).map (z.hom.app L) ≫ τ ≫ j) =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app B ≫
        ((rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) w).inv.app B ≫
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom g).inv.app B ≫
          (ordinaryFinitePushforward A g).map
            (asIso ((derivedUpperStarLowerStarAdjunction
                (ModuleCat.{u + 1} A) e.hom).unit.app L) ≪≫
              (ordinaryFinitePushforward A e.hom).mapIso bL).inv ≫ τ) ≫ j := by
  let : (lowerStar (ModuleCat.{u + 1} A) e.hom).rightDerivedFunctor.IsEquivalence :=
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom
      ).isEquivalence_right_of_isEquivalence_left
  exact exists_derivedTraceAdjustment (ModuleCat.{u + 1} A) e.hom g q w
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q)
    (asIso ((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) e.hom).unit.app L) ≪≫
      (ordinaryFinitePushforward A e.hom).mapIso bL) v (z.app L) τ j

end AlgebraicGeometry.Etale
