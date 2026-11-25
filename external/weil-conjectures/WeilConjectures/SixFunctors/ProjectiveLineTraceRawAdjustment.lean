/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
public import WeilConjectures.SixFunctors.ProjectiveLineTraceModel
import WeilConjectures.SixFunctors.ModuleTraceAdjustment

/-! # Comparison of the two explicit projective-line trace presentations

A coefficient automorphism relates geometric transport to the prescribed ordinary trace.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

attribute [local irreducible] derivedTensor singleFunctorObjUnitIso

set_option linter.auxLemma false in
attribute [local instance 100000]
  presentedFiniteP1Trace._proof_1
  presentedFiniteP1Trace._proof_2
  presentedFiniteP1Trace._proof_4
  presentedFiniteP1Trace._proof_5
  presentedFiniteP1Trace._proof_6
  presentedFiniteP1Trace._proof_7
  presentedFiniteP1Trace._proof_8
  presentedFiniteP1Trace._proof_9
  presentedFiniteP1Trace._proof_10
  presentedFiniteP1Trace._proof_11
  presentedFiniteP1Trace._proof_12
  presentedFiniteP1Trace._proof_13
  presentedFiniteP1Trace._proof_14
  presentedFiniteP1Trace._proof_15
  presentedFiniteP1Trace._proof_16
  presentedFiniteP1Trace._proof_17
  presentedFiniteP1Trace._proof_18
  presentedFiniteP1Trace._proof_19
  presentedFiniteP1Trace._proof_20
  presentedFiniteP1Trace._proof_21
  presentedFiniteP1Trace._proof_22
  presentedFiniteP1Trace._proof_23
  presentedFiniteP1Trace._proof_24
  presentedFiniteP1Trace._proof_25
  presentedFiniteP1Trace._proof_26

set_option allowUnsafeReducibility true in
attribute [local irreducible] rightDerivedLowerShriekOfCompactification

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The coefficient adjustment for the explicit projective-line trace composites.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, transport through a presentation.
(auxiliary; not a blueprint node)

Proof: in the module-valued trace-adjustment formula take B to be the shifted Tate
line on X and L to be the shifted Tate line on the projective line. Both coefficient
comparisons are the specified shifted-line pullback comparison. For z use the
geometric push-pull isomorphism of the presentation; take the splitting trace and the
constant-complex unit comparison as the last two maps. Substitution gives the formula.
No property of the supported diagonal class or of either triangle is required. -/
theorem exists_presentedFiniteP1RawAdjustment
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ArbitraryBaseFiniteP1Splitting A N hA t Y hY) :
    let B := (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧
    let L := (ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧
    let g := (ProjectiveLine Y ↘ Y)
    let bL := ordinaryFiniteShiftedLinePullback A N hA t e.hom
      (finiteP1_unitOnPullback N g hY)
    let v := bL
    let z := SfP1Transport.pushPull A e
    let τ := d.trace
    let j := (SfP1Transport.constantUnit A Y).hom
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
  dsimp only
  exact exists_moduleTraceAdjustment A e (ProjectiveLine Y ↘ Y) q w _ _
    (ordinaryFiniteShiftedLinePullback A N hA t e.hom
      (finiteP1_unitOnPullback N (ProjectiveLine Y ↘ Y) hY))
    (ordinaryFiniteShiftedLinePullback A N hA t e.hom
      (finiteP1_unitOnPullback N (ProjectiveLine Y ↘ Y) hY))
    (SfP1Transport.pushPull A e) d.trace (SfP1Transport.constantUnit A Y).hom

end AlgebraicGeometry.Etale
