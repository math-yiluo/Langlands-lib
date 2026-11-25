/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareData
import WeilConjectures.CategoryTheory.Integral.IntegralResidueMatePasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueRestrictPullComp

/-! # Composition of the canonical residue pull mates -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralResiduePullSquareComp
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The inverse mates satisfy the composition coherence equation.
Source: scalar associativity and mate pasting, Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-integral-residue-derived-pull-square-comp)
Proof. Apply the generic inverse-mate pasting identity to the three restriction/pullback
comparison squares. The associativity isomorphisms are `residueExchangeUpperStarComp`;
naturality and the counit identities reduce both paths to the same composite. -/
theorem integralResidue_pullSquare_comp :
      ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        (K : residueExchangeDerived (integralCoeff ℓ E) Z),
        (residueExchangeReduction ℓ E X).map
            ((residueExchangeUpperStarComp (integralCoeff ℓ E) f g).hom.app K) ≫
          (residueExchangePullHom ℓ E f).app
            ((residueExchangeUpperStar (integralCoeff ℓ E) g).obj K) ≫
          (residueExchangeUpperStar
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
            ((residueExchangePullHom ℓ E g).app K) =
        (residueExchangePullHom ℓ E (f ≫ g)).app K ≫
          (residueExchangeUpperStarComp
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom.app
            ((residueExchangeReduction ℓ E Z).obj K) := by
  intro X Y Z f g K
  unfold residueExchangePullHom
  exact inverseMate_pasting
    (residueExchangeReductionAdjunction ℓ E Z)
    (residueExchangeReductionAdjunction ℓ E Y)
    (residueExchangeReductionAdjunction ℓ E X)
    (residueExchangeRestrictPullIso ℓ E g).hom
    (residueExchangeRestrictPullIso ℓ E f).hom
    (residueExchangeRestrictPullIso ℓ E (f ≫ g)).hom
    (residueExchangeUpperStarComp (integralCoeff ℓ E) f g).hom
    (residueExchangeUpperStarComp
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom
    (residueExchangeRestrictPullIso_comp ℓ E f g) K

end AlgebraicGeometry.ProEtale.CondensedRing
