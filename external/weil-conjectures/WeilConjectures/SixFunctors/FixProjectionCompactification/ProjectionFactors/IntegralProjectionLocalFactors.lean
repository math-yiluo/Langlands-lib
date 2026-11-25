/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionFactorData

/-! # The open arrow and support identification before coefficient change

Source: def-exchange-projection and prop-sf-pf-coherence, the open factor.
(blueprint: def-sf-integral-projection-local-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.FixProjectionCompactification.ProjectionFactors

variable {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
  [∀ X, Category.{w} (B X)] {S : SixFunctorPushStage D B}
  {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
  (A : SixFunctorExchangeData S T Q)

/-- The integral open arrow, with its input equality transport made explicit.
The construction works on any supplied coefficient category.
Source: def-exchange-projection (blueprint: def-sf-integral-projection-local-factors). -/
def openMap (K : B Q.X) (L : B Q.Y) :
    ((A.stage.tensorBar.obj (A.stage.openExtension.obj K)).obj
      (A.stage.properPull.obj L)) ⟶
      A.stage.openExtension.obj (((T Q.X).obj K).obj ((S.pull Q.f).obj L)) :=
  (A.stage.openProjection.hom.app K).app L ≫
    A.stage.openExtension.map (eqToHom (by
      change ((A.stage.tensorX.obj K).obj (A.stage.pull.obj L)) = _
      rw [A.tensorX, A.pull]))

/-- The support identification, after the open factor, on a single input.
Source: def-exchange-projection (blueprint: def-sf-integral-projection-local-factors). -/
def supportMap (K : B Q.X) :
    A.stage.properPush.obj (A.stage.openExtension.obj K) ⟶
      (S.support Q.f Q.compactification).obj K :=
  A.stage.compactSupportIdentification.inv.app K ≫ eqToHom (by rw [A.compactSupport])

/-- Factor the datum's second projection factor by moving the input equality
transport through the natural support identification.
Source: naturality (blueprint: def-sf-integral-projection-local-factors). -/
theorem second_via_openMap (K : B Q.X) (L : B Q.Y) :
    second A K L = A.stage.properPush.map (openMap A K L) ≫
      supportMap A (((T Q.X).obj K).obj ((S.pull Q.f).obj L)) := by
  let W := ((T Q.X).obj K).obj ((S.pull Q.f).obj L)
  let e : ((A.stage.tensorX.obj K).obj (A.stage.pull.obj L)) = W := by
    rw [A.tensorX, A.pull]
  let s : A.stage.compactSupport.obj W ⟶ (S.support Q.f Q.compactification).obj W :=
    eqToHom (by rw [A.compactSupport])
  have h := A.stage.compactSupportIdentification.inv.naturality_assoc (eqToHom e) s
  dsimp only [Functor.comp_map] at h
  dsimp only [second, openMap, supportMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [h]
  simp only [s, eqToHom_map, eqToHom_trans]

end WeilConjectures.FixProjectionCompactification.ProjectionFactors
