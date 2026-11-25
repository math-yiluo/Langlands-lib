/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages

/-! # The proper and open factors of the integral projection

Source: def-exchange-projection, the proper counit mate followed by open projection.
(blueprint: def-sf-integral-projection-factor-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification.ProjectionFactors

section General
variable {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
  [∀ X, Category.{w} (B X)] {S : SixFunctorPushStage D B}
  {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
  (A : SixFunctorExchangeData S T Q) (K : B Q.X) (L : B Q.Y)

/-- Source identification followed by the proper counit projection mate.
Source: def-exchange-projection (blueprint: def-sf-integral-projection-factor-data). -/
def first :
    ((T Q.Y).obj ((S.support Q.f Q.compactification).obj K)).obj L ⟶
      A.stage.properPush.obj
        ((A.stage.tensorBar.obj (A.stage.openExtension.obj K)).obj
          (A.stage.properPull.obj L)) :=
  eqToHom (by simp only [A.tensorY, A.compactSupport]) ≫
    (A.stage.tensorY.map (A.stage.compactSupportIdentification.hom.app K)).app L ≫
      ((A.stage.properAdjunction.rightAdjointProjectionMap
        A.stage.tensorPullback.hom).app (A.stage.openExtension.obj K)).app L

/-- Proper image of open projection followed by the target support identification.
Source: def-exchange-projection (blueprint: def-sf-integral-projection-factor-data). -/
def second :
    A.stage.properPush.obj
        ((A.stage.tensorBar.obj (A.stage.openExtension.obj K)).obj
          (A.stage.properPull.obj L)) ⟶
      (S.support Q.f Q.compactification).obj
        (((T Q.X).obj K).obj ((S.pull Q.f).obj L)) :=
  A.stage.properPush.map ((A.stage.openProjection.hom.app K).app L) ≫
    A.stage.compactSupportIdentification.inv.app
      ((A.stage.tensorX.obj K).obj (A.stage.pull.obj L)) ≫
    eqToHom (by rw [A.tensorX, A.compactSupport, A.pull])

/-- The defining projection is the composite of its proper and open factors.
Source: def-exchange-projection (blueprint: def-sf-integral-projection-factor-data). -/
theorem factorization : A.projectionComponent K L = first A K L ≫ second A K L := by
  simp only [SixFunctorExchangeData.projectionComponent, first, second,
    CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage.projection,
    CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  rfl

end General

/-- Paste two coefficient squares along a factorization.
Source: associativity and functoriality
(blueprint: def-sf-integral-projection-factor-data). -/
theorem paste {B : Type v} [Category.{w} B] {C : Type v'} [Category.{w'} C]
    (F : B ⥤ C) {A₀ A₁ A₂ : B} {B₀ B₁ B₂ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₀ ⟶ A₂)
    (s : F.obj A₀ ⟶ B₀) (p : B₀ ⟶ B₁) (q : B₁ ⟶ B₂)
    (m : F.obj A₁ ⟶ B₁) (t : F.obj A₂ ⟶ B₂)
    (hp : s ≫ p = F.map a ≫ m) (hq : m ≫ q = F.map b ≫ t)
    (hc : a ≫ b = c) : s ≫ (p ≫ q) = F.map c ≫ t := by
  rw [← Category.assoc, hp, Category.assoc, hq, ← Category.assoc, ← F.map_comp, hc]

end WeilConjectures.FixProjectionCompactification.ProjectionFactors
