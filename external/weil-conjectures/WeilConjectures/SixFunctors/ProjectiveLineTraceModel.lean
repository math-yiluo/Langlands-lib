/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange

/-! # Trace models on presentations of the projective line

Source: current blueprint, proposition-adjunction-projective-line--1 and
lemma-cohomology-projective-line-trace. The trace is transported from the normalized finite Kummer
splitting. The counit is an actual inverse-projection composite, defined before asserting
adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The proper ordered projection is invertible for finite coefficients on all complexes.
Source: the proper torsion projection formula, blueprint
proposition-proper-direct-image-constructible-complexes--9. (auxiliary; not a blueprint node)
Proof: the ordered map is the proper projection map conjugated by tensor symmetries.
Each component is invertible; hence so is the natural transformation. -/
theorem isIso_finiteP1Projection
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (q : X ⟶ Y) [IsProper q] (L : DerivedCategoryModule A X) :
    IsIso (ordinaryFiniteProjectionNatTrans A q L) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper A isAddTorsion_of_finite q
  have (K : DerivedCategoryModule A Y) :
      IsIso ((ordinaryFiniteProjectionNatTrans A q L).app K) := by
    dsimp only [ordinaryFiniteProjectionNatTrans, ordinaryFiniteProjection]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The normalized splitting trace on a projective-line presentation, transported using
inverse image along its isomorphism, the adjunction unit, and direct-image composition.
Source: lemma-cohomology-projective-line-trace and the presentation transport in
proposition-adjunction-projective-line--1. (auxiliary; not a blueprint node) -/
@[irreducible]
def presentedFiniteP1Trace
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (q : X ⟶ Y) (e : X ≅ ProjectiveLine Y)
    (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q) (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ArbitraryBaseFiniteP1Splitting A N hA t Y hY) :
    (ordinaryFinitePushforward A q).obj
      ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ⟶ ordinaryFiniteUnit A Y :=
  let L := (ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧
  let hP := finiteP1_unitOnPullback N (ProjectiveLine Y ↘ Y) hY
  let c := ordinaryFiniteShiftedLinePullback A N hA t e.hom hP
  let b := asIso ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) e.hom).unit.app L) ≪≫
    (ordinaryFinitePushforward A e.hom).mapIso c
  (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) w).inv.app _ ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom
      (ProjectiveLine Y ↘ Y)).inv.app _ ≫
    (ordinaryFinitePushforward A (ProjectiveLine Y ↘ Y)).map b.inv ≫ d.trace

/-- The candidate counit for a proper map and a specified finite trace. This is inverse
ordered projection followed by tensor trace, after the canonical proper coincidence.
Source: lemma-cohomology-projective-line-trace, its displayed formula for epsilon.
(auxiliary; not a blueprint node) -/
@[irreducible]
def finiteP1TraceCounit
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (q : X ⟶ Y) [IsProper q] [HasCompactification q] (L : DerivedCategoryModule A X)
    (τ : (ordinaryFinitePushforward A q).obj L ⟶ ordinaryFiniteUnit A Y) :
    ordinaryFiniteTwistedPullback A q L ⋙ R(q)_![ModuleCat.{u + 1} A] ⟶
      𝟭 (DerivedCategoryModule A Y) :=
  letI := isIso_finiteP1Projection A q L
  Functor.whiskerLeft (ordinaryFiniteTwistedPullback A q L)
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom ≫
    inv (ordinaryFiniteProjectionNatTrans A q L) ≫ ordinaryFiniteTensorTrace A Y τ

/-- The inverse-projection counit belonging to the splitting on a presentation.
Source: proposition-adjunction-projective-line--1, canonical counit.
(auxiliary; not a blueprint node) -/
def presentedFiniteP1Counit
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ArbitraryBaseFiniteP1Splitting A N hA t Y hY) :
    ordinaryFiniteTwistedPullback A q ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ⋙
      R(q)_![ModuleCat.{u + 1} A] ⟶ 𝟭 (DerivedCategoryModule A Y) :=
  finiteP1TraceCounit A q _ (presentedFiniteP1Trace A N hA t q e w hY d)

/-- The explicit comparison of the two finite twisted inverse images in a square.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism--6, projective-line
computation. (auxiliary; not a blueprint node) -/
def finiteP1TwistedPullbackComparison
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    (hY : IsUnit (N : Γ(Y, ⊤))) (K : DerivedCategoryModule A Y) :
    (L((g')^*[ModuleCat.{u + 1} A])).obj
        ((ordinaryFiniteTwistedPullback A q
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)).obj K) ≅
      (ordinaryFiniteTwistedPullback A q'
        ((ordinaryFiniteLine A N hA X')⟦(2 : ℤ)⟧)).obj
          ((L((g)^*[ModuleCat.{u + 1} A])).obj K) :=
  ordinaryFiniteTwistedPullbackComparison A q q' g g'
    ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
    ((ordinaryFiniteLine A N hA X')⟦(2 : ℤ)⟧) K
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K)
    (ordinaryFiniteShiftedLinePullback A N hA t g'
      (finiteP1_unitOnPullback N q hY))

end AlgebraicGeometry.Etale
