/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionCoefficientTransport.RationalProjectionTensorCompatibility

/-! # The two factors of a compactification projection

Source: def-exchange-projection, proper counit mate followed by open projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures.ProjectionCoefficientTransport

variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
  {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
  {Q : SixFunctorCompactifiedSquare D}

/-- The intermediate object after the proper counit mate, before open projection.
Source: def-exchange-projection (blueprint: def-sf-projection-mate-factors). -/
def middleObject (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (Q : SixFunctorCompactifiedSquare D) (K : B Q.X) (N : B Q.Y) : B Q.Y :=
  (S.direct Q.p).obj
    (((T Q.Z).obj ((S.openExtension Q.i Q.open_i).obj K)).obj ((S.pull Q.p).obj N))

/-- Identify the intermediate object with the supplied stage coordinates.
Source: def-exchange-projection (blueprint: def-sf-projection-mate-factors).
Proof: substitute the four recorded functor equalities. -/
theorem middle_eq (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    middleObject S T Q K N = A.stage.properPush.obj
      (((A.stage.tensorBar.obj (A.stage.openExtension.obj K)).obj
        (A.stage.properPull.obj N))) := by
  rw [A.properPush, A.tensorBar, A.openExtension, A.properPull]
  rfl

/-- Support identification followed by the proper counit projection mate.
Source: def-exchange-projection (blueprint: def-sf-projection-mate-factors). -/
def properFactor (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    ((T Q.Y).obj ((S.support Q.f Q.compactification).obj K)).obj N ⟶
      middleObject S T Q K N :=
  eqToHom (by rw [A.tensorY, A.compactSupport]) ≫
    (A.stage.tensorY.map (A.stage.compactSupportIdentification.hom.app K)).app N ≫
    ((A.stage.properAdjunction.rightAdjointProjectionMap
      A.stage.tensorPullback.hom).app (A.stage.openExtension.obj K)).app N ≫
    eqToHom (middle_eq A K N).symm

/-- Proper image of open projection, followed by inverse support identification.
Source: def-exchange-projection (blueprint: def-sf-projection-mate-factors). -/
def openFactor (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    middleObject S T Q K N ⟶
      (S.support Q.f Q.compactification).obj
        (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) :=
  eqToHom (middle_eq A K N) ≫
    A.stage.properPush.map ((A.stage.openProjection.hom.app K).app N) ≫
    A.stage.compactSupportIdentification.inv.app
      (((A.stage.tensorX.obj K).obj (A.stage.pull.obj N))) ≫
    eqToHom (by rw [A.tensorX, A.pull, A.compactSupport])

/-- The specified projection is exactly the composite of these two factors.
Source: def-exchange-projection (blueprint: def-sf-projection-mate-factors).
Proof: evaluate the supplied bifunctor composite. The two transports at the
intermediate object cancel. All other factors retain their original order. -/
theorem projection_factorization (A : SixFunctorExchangeData S T Q)
    (K : B Q.X) (N : B Q.Y) :
    A.projectionComponent K N = properFactor A K N ≫ openFactor A K N := by
  simp [SixFunctorExchangeData.projectionComponent, properFactor, openFactor,
    ExchangeProjectionStage.projection, compactificationProjectionFromData,
    Category.assoc, eqToHom_trans_assoc]

variable {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
  (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
    (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))

/-- The coefficient comparison at the intermediate proper-image object.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: def-sf-projection-mate-factors). -/
def middle (Q : SixFunctorCompactifiedSquare D) (K : B Q.X) (N : B Q.Y) :
    (V Q.Y).obj (middleObject S T Q K N) ≅
      middleObject S' T' Q ((V Q.X).obj K) ((V Q.Y).obj N) :=
  (C.directAdjunction Q.p).right.app _ ≪≫
    (S'.direct Q.p).mapIso
      ((t Q.Z).app ((S.openExtension Q.i Q.open_i).obj K, (S.pull Q.p).obj N) ≪≫
        (Functor.uncurry.obj (T' Q.Z)).mapIso
          (Iso.prod ((C.openExtension Q.i Q.open_i).app K)
            ((C.directAdjunction Q.p).left.app N)))

/-- Paste the two factor squares to preserve the specified projection component.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: def-sf-projection-mate-factors).
Proof: expand the proved factorization, apply functoriality, substitute first the
open and then the proper factor square, and recombine the two target factors. -/
theorem projection_preserved_of_factors
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (K : B Q.X) (N : B Q.Y)
    (hp : (V Q.Y).map (properFactor A K N) ≫ (middle C t Q K N).hom =
      (source C t Q.f Q.compactification K N).hom ≫
        properFactor A' ((V Q.X).obj K) ((V Q.Y).obj N))
    (ho : (V Q.Y).map (openFactor A K N) ≫
        (target C t Q.f Q.compactification K N).hom =
      (middle C t Q K N).hom ≫ openFactor A' ((V Q.X).obj K) ((V Q.Y).obj N)) :
    (V Q.Y).map (A.projectionComponent K N) ≫
        (target C t Q.f Q.compactification K N).hom =
      (source C t Q.f Q.compactification K N).hom ≫
        A'.projectionComponent ((V Q.X).obj K) ((V Q.Y).obj N) := by
  rw [projection_factorization, Functor.map_comp, Category.assoc, ho,
    ← Category.assoc, hp, Category.assoc, ← projection_factorization]

end WeilConjectures.ProjectionCoefficientTransport
