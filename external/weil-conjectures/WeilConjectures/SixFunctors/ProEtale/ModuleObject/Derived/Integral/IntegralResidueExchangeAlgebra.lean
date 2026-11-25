/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.ResidueExchangeAmbient
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange

/-! # Adjunction algebra for reduction of the exchange arrow

Source: Bhatt--Scholze, Remark 6.8.15, and the calculus of adjunction mates.
(blueprint: lem-weil-pbc-integral-residue-exchange-algebra)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueExchangeAlgebra
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  (c : IntegralResiduePullComparisons.{u} ℓ E)
  {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

private theorem pull_transport {A B : Scheme.{u}} (h i : A ⟶ B) (w : h = i)
    (K : residueExchangeDerived (integralCoeff ℓ E) B) :
    (residueExchangeReduction ℓ E A).map
        (eqToIso (congrArg
          (fun t : A ⟶ B ↦ (residueExchangeUpperStar (integralCoeff ℓ E) t).obj K) w)).hom ≫
      (c.pull i).hom.app K =
    (c.pull h).hom.app K ≫
      (eqToIso (congrArg
        (fun t : A ⟶ B ↦ (residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) t).obj
            ((residueExchangeReduction ℓ E B).obj K)) w)).hom := by
  cases w
  simp only [eqToIso_refl, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

private theorem pull_square (sq : CommSq g' f' f g)
    (K : residueExchangeDerived (integralCoeff ℓ E) Y) :
    (residueExchangeReduction ℓ E X').map
        ((residueExchangeSquare (integralCoeff ℓ E) sq).hom.app K) ≫
      (c.pull g').hom.app ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj K) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) g').map
        ((c.pull f).hom.app K) =
    (c.pull f').hom.app ((residueExchangeUpperStar (integralCoeff ℓ E) g).obj K) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f').map
        ((c.pull g).hom.app K) ≫
      (residueExchangeSquare
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) sq).hom.app
        ((residueExchangeReduction ℓ E Y).obj K) := by
  let eR := eqToIso (congrArg (fun h : X' ⟶ Y ↦
    (residueExchangeUpperStar (integralCoeff ℓ E) h).obj K) sq.w.symm)
  let eA := eqToIso (congrArg (fun h : X' ⟶ Y ↦
    (residueExchangeUpperStar
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) h).obj
      ((residueExchangeReduction ℓ E Y).obj K)) sq.w.symm)
  have he : (residueExchangeReduction ℓ E X').map eR.hom ≫
      (c.pull (g' ≫ f)).hom.app K = (c.pull (f' ≫ g)).hom.app K ≫ eA.hom :=
    pull_transport ℓ E c (f' ≫ g) (g' ≫ f) sq.w.symm K
  simpa only [residueExchangeSquare, transportedCompositeIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.map_comp,
    Iso.app_hom, Iso.app_inv, Category.assoc, eR, eA] using
    (CategoryTheory.Adjunction.composition_square_aux
      ((residueExchangeReduction ℓ E X').mapIso
        ((residueExchangeUpperStarComp (integralCoeff ℓ E) f' g).app K))
      ((residueExchangeReduction ℓ E X').mapIso
        ((residueExchangeUpperStarComp (integralCoeff ℓ E) g' f).app K))
      ((residueExchangeReduction ℓ E X').mapIso eR)
      ((residueExchangeUpperStarComp
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f' g).app
        ((residueExchangeReduction ℓ E Y).obj K))
      ((residueExchangeUpperStarComp
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) g' f).app
        ((residueExchangeReduction ℓ E Y).obj K))
      eA
      ((c.pull (f' ≫ g)).hom.app K)
      ((c.pull (g' ≫ f)).hom.app K)
      ((c.pull f').hom.app ((residueExchangeUpperStar (integralCoeff ℓ E) g).obj K) ≫
        (residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f').map
          ((c.pull g).hom.app K))
      ((c.pull g').hom.app ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj K) ≫
        (residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) g').map
          ((c.pull f).hom.app K))
      (c.comp f' g K) (c.comp g' f K) he)

/-- Coherent reduction pull comparisons transport the actual ambient exchange arrow.

Source: Bhatt--Scholze, Remark 6.8.15, and Mathlib's adjunction mates.
(blueprint: lem-weil-pbc-integral-residue-exchange-algebra)

Proof. The composition equations for the two paths around the scheme square imply
its coefficient pull cube, after cancellation of the first composition isomorphism.
Equality of the composite scheme maps transports the middle comparison by eqToHom
naturality. Both exchange arrows are mates of these square maps. The push comparisons
are mates of the inverse pull comparisons. Their counit identities therefore follow
from mateEquiv_counit. The abstract coefficient-exchange calculation applies. No
comparison or exchange map is assumed invertible. -/
theorem integralResidue_exchange_square (sq : CommSq g' f' f g)
    (K : residueExchangeDerived (integralCoeff ℓ E) X) :
    (c.pull g).hom.app ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) g).map
        ((c.push f).app K) ≫
      (residueExchangeBaseChange
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) sq).app
        ((residueExchangeReduction ℓ E X).obj K) =
    (residueExchangeReduction ℓ E Y').map
        ((residueExchangeBaseChange (integralCoeff ℓ E) sq).app K) ≫
      (c.push f').app ((residueExchangeUpperStar (integralCoeff ℓ E) g').obj K) ≫
      (residueExchangeLowerStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f').map
        ((c.pull g').hom.app K) := by
  exact CategoryTheory.Adjunction.coefficient_exchange_of_counit_at
    (residueExchangeAdjunction (integralCoeff ℓ E) f)
    (residueExchangeAdjunction (integralCoeff ℓ E) f')
    (residueExchangeAdjunction
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
    (residueExchangeAdjunction
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f')
    (residueExchangeSquare (integralCoeff ℓ E) sq).hom
    (residueExchangeSquare
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) sq).hom
    K ((residueExchangeBaseChange (integralCoeff ℓ E) sq).app K)
    ((residueExchangeBaseChange
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) sq).app
      ((residueExchangeReduction ℓ E X).obj K))
    (residueExchangeBaseChange_counit (integralCoeff ℓ E) sq K)
    (residueExchangeBaseChange_counit
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) sq
      ((residueExchangeReduction ℓ E X).obj K))
    (c.pull f) (c.pull f') (c.pull g).hom (c.pull g').hom
    ((c.push f).app K)
    ((c.push f').app ((residueExchangeUpperStar (integralCoeff ℓ E) g').obj K))
    (c.push_counit f K)
    (c.push_counit f' ((residueExchangeUpperStar (integralCoeff ℓ E) g').obj K))
    (pull_square ℓ E c sq ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K))

end AlgebraicGeometry.ProEtale.CondensedRing
