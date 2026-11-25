/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSitePerfectDuality
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# Axiomatized six-functor data

Source: current blueprint main-20261015, chap-The-pro-etale-site,
sk-def-sf-operations/def-sf-datum, axioms (A1)--(A6) (blueprint: def-sf-datum).

The operation datum fixes the actual coefficient categories and constructions.
The structures below impose properties on those operations; they do not assert
that a concrete six-functor datum exists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w a b a' b'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.SuppliedExchangeProjection
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- Reassociate the same compactification, transporting only its factorization.
Source: the associativity convention in A4 (blueprint: def-sf-datum). -/
def sixFunctorAssocCompactification {D : FiniteFieldDatum.{u}}
    {W X Y Z : SixFunctorSpace D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (c : Compactification ((f ≫ g) ≫ h).hom.left) :
    Compactification (f ≫ g ≫ h).hom.left :=
  (congrArg (fun e : W ⟶ Z ↦ e.hom.left) (Category.assoc f g h)) ▸ c

/-- Direct-image composition is the unique right-adjoint mate of pullback composition.
Consequently the comparison uses the pasted unit and counit, rather than another
adjunction on the same functors. Source: A1 (blueprint: def-sf-datum). -/
def sixFunctorDirectComposition {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) : S.direct (f ≫ g) ≅ S.direct f ⋙ S.direct g :=
  (S.pullDirectAdjunction (f ≫ g)).rightAdjointUniq
    (((S.pullDirectAdjunction g).comp (S.pullDirectAdjunction f)).ofNatIsoLeft
      (S.pullComposition f g).symm)

/-- Exceptional composition is the unique right-adjoint mate of the supplied support
composition; its units and counits are the pasted ones.
Source: A1 and A4 (blueprint: def-sf-datum). -/
def sixFunctorExceptionalComposition {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) :
    S.exceptional (f ≫ g) cfg ≅ S.exceptional g cg ⋙ S.exceptional f cf :=
  (S.exceptionalAdjunction (f ≫ g) cfg).rightAdjointUniq
    (((S.exceptionalAdjunction f cf).comp (S.exceptionalAdjunction g cg)).ofNatIsoLeft
      (S.composition f g cf cg cfg).symm)

/-- Finite-Tor preservation and the support pentagon. Adjunctions and proper coincidence
are already fields of S; their composition comparisons are the mates defined above.
The pentagon is written on components, including the canonical associativity transport.
Source: A1 and A4 on their displayed domains (blueprint: def-sf-datum). -/
structure SixFunctorCoherentStage {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (P : ∀ X, ObjectProperty (B X)) where
  pullDomain : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (K : B Y), P Y K → P X ((S.pull f).obj K)
  directDomain : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (K : B X), P X K → P Y ((S.direct f).obj K)
  supportDomain : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : B X), P X K → P Y ((S.support f c).obj K)
  exceptionalDomain : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : B Y), P Y K → P X ((S.exceptional f c).obj K)
  pentagon : ∀ {W X Y Z : SixFunctorSpace D}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : B W), P W K →
    HEq ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K))
      ((S.composition f (g ≫ h) cf cgh
        (sixFunctorAssocCompactification f g h cfgh)).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K))

/-- The supplied higher-stage exchange and projection maps are invertible on finite-Tor
inputs; the direct-image exchange has exactly the proper-or-smooth alternative.
Source: A2 and A3 (blueprint: def-sf-datum). -/
structure SixFunctorExchangeAxioms {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ X, ObjectProperty (B X)) : Prop where
  compactExchange : ∀ (Q : SixFunctorCompactifiedSquare D) (K : B Q.X), P Q.X K →
    IsIso ((A Q).stage.compactExchange.app K)
  directExchange : ∀ (Q : SixFunctorCompactifiedSquare D) (K : B Q.X), P Q.X K →
    (IsProper Q.f.hom.left ∨ Smooth Q.g.hom.left) → IsIso ((A Q).stage.exchange.app K)
  projection : ∀ (Q : SixFunctorCompactifiedSquare D) (K : B Q.X) (L : B Q.Y),
    P Q.X K → P Q.Y L → IsIso ((A Q).projectionComponent K L)

/-- Restrict an actual coefficient-change functor to the finite-Tor domains.
Source: A5 on its displayed domains (blueprint: def-sf-datum). -/
def sixFunctorDomainChange {B : Type a} [Category.{b} B]
    {B' : Type a'} [Category.{b'} B'] (P : ObjectProperty B) (P' : ObjectProperty B')
    (F : B ⥤ B') (h : ∀ K : P.FullSubcategory, P' (F.obj K.obj)) :
    P.FullSubcategory ⥤ P'.FullSubcategory :=
  P'.lift (P.ι ⋙ F) h

/-- The standard localization used by the ambient coefficient categories.
Source: A6, ordinary derived categories (blueprint: def-sf-datum). -/
abbrev sixFunctorRingedModel {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max a b u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max a b u}]
    (R : Sheaf J CommRingCat.{max a b u}) :=
  @RingedSiteDualityModel.{a, b, u, max a b u + 1} C _ J _ _ R
    (HasDerivedCategory.standard _)

end WeilConjectures
