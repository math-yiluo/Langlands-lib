/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleUnit
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerConstruction
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-!
# Six-functor construction stages

Source: blueprint master, sec-smooth-purity/sk-def-sf-operations,
def-fix-six-functor-datum, order 1491
(blueprint: def-sf-operation-stages).

## Main definitions

* `SixFunctorPushStage`: operations, compactification comparisons, and adjunctions.
* `SixFunctorHigherOperations`: integral and rational constructions.
* `SixFunctorDualityData`: the dualizing object and its internal-Hom construction.

The datum is construction data, including the comparisons, rather than a choice
from an unnormalized existence assertion. This file does not assert that such a
datum exists: the operation theorems supply its adjunction and preservation fields.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w v' w' hA hB hA' hB'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.SuppliedExchangeProjection
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures
open TensorProduct
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)

/-- Finite-type schemes over the specified base, using the existing over category.
Source: the initial setting of def-fix-six-functor-datum
(blueprint: def-sf-operation-stages). -/
abbrev SixFunctorSpace (D : FiniteFieldDatum.{u}) :=
  ObjectProperty.FullSubcategory (fun X : Over (Spec (.of D.k)) ↦
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

/-- The base field as an object of the same finite-type category.
Source: the structure map in clause (5) (blueprint: def-sf-operation-stages). -/
def sixFunctorPoint (D : FiniteFieldDatum.{u}) : SixFunctorSpace D :=
  ⟨Over.mk (𝟙 (Spec (.of D.k))),
    ⟨inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k)))),
      inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))⟩⟩

/-- The structure morphism, with its original base map, in the over category.
Source: clause (5) (blueprint: def-sf-operation-stages). -/
def sixFunctorStructure {D : FiniteFieldDatum.{u}} (X : SixFunctorSpace D) :
    X ⟶ sixFunctorPoint D :=
  ObjectProperty.homMk (Over.homMk X.obj.hom (by simp [sixFunctorPoint]))

/-- Identity-proper compactification of an open immersion, with its supplied
open-immersion proof. Source: clause (2)
(blueprint: def-sf-operation-stages). -/
def sixFunctorOpenCompactification {D : FiniteFieldDatum.{u}}
    {X Y : SixFunctorSpace D} (j : X ⟶ Y) (hj : IsOpenImmersion j.hom.left) :
    Compactification j.hom.left :=
  @Compactification.ofIsOpenImmersion X.obj.left Y.obj.left j.hom.left hj

/-- A Cartesian scheme square with an open/proper compactification square,
bundled in the existing category of finite-type schemes over the fixed base.
Source: clause (3) and def-exchange-projection
(blueprint: def-sf-operation-stages). -/
structure SixFunctorCompactifiedSquare (D : FiniteFieldDatum.{u}) where
  X : SixFunctorSpace D
  Y : SixFunctorSpace D
  X' : SixFunctorSpace D
  Y' : SixFunctorSpace D
  Z : SixFunctorSpace D
  Z' : SixFunctorSpace D
  f : X ⟶ Y
  f' : X' ⟶ Y'
  g : Y' ⟶ Y
  g' : X' ⟶ X
  i : X ⟶ Z
  i' : X' ⟶ Z'
  p : Z ⟶ Y
  p' : Z' ⟶ Y'
  h : Z' ⟶ Z
  open_i : IsOpenImmersion i.hom.left
  open_i' : IsOpenImmersion i'.hom.left
  proper_p : IsProper p.hom.left
  proper_p' : IsProper p'.hom.left
  factorization : f = i ≫ p
  factorization' : f' = i' ≫ p'
  square : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left
  properSquare : IsPullback h.hom.left p'.hom.left p.hom.left g.hom.left
  openSquare : IsPullback g'.hom.left i'.hom.left i.hom.left h.hom.left
  squareComm : g' ≫ f = f' ≫ g
  properComm : h ≫ p = p' ≫ g
  openComm : g' ≫ i = i' ≫ h

/-- The existing compactification represented by the supplied over-category factors.
Source: clause (3) (blueprint: def-sf-operation-stages). -/
def SixFunctorCompactifiedSquare.compactification {D : FiniteFieldDatum.{u}}
    (Q : SixFunctorCompactifiedSquare D) : Compactification Q.f.hom.left where
  Z := Q.Z.obj.left
  g := Q.p.hom.left
  i := Q.i.hom.left
  comm := congrArg (fun e : Q.X ⟶ Q.Y ↦ e.hom.left) Q.factorization
  isProper := Q.proper_p
  isOpenImmersion := Q.open_i

/-- The base-changed candidate from the same supplied compactification square.
Source: clause (3) (blueprint: def-sf-operation-stages). -/
def SixFunctorCompactifiedSquare.compactification' {D : FiniteFieldDatum.{u}}
    (Q : SixFunctorCompactifiedSquare D) : Compactification Q.f'.hom.left where
  Z := Q.Z'.obj.left
  g := Q.p'.hom.left
  i := Q.i'.hom.left
  comm := congrArg (fun e : Q.X' ⟶ Q.Y' ↦ e.hom.left) Q.factorization'
  isProper := Q.proper_p'
  isOpenImmersion := Q.open_i'

/-- Push, open extension, compact support, and the constructible exceptional adjoint
at one coefficient level. Comparisons are natural isomorphisms with identity and
cocycle equations. The operation datum additionally identifies the finite
comparisons with the recorded refinement, composition, proper and open maps;
coherence equations alone do not prescribe their normalization.
Source: clauses (1), (2), and (4) of `def-fix-six-functor-datum`
(blueprint: def-sf-operation-stages). -/
structure SixFunctorPushStage (D : FiniteFieldDatum.{u})
    (B : SixFunctorSpace D → Type v) [∀ X, Category.{w} (B X)] where
  pull : ∀ {X Y : SixFunctorSpace D}, (X ⟶ Y) → B Y ⥤ B X
  pullComposition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z),
    pull (f ≫ g) ≅ pull g ⋙ pull f
  direct : ∀ {X Y : SixFunctorSpace D}, (X ⟶ Y) → B X ⥤ B Y
  pullDirectAdjunction : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y), pull f ⊣ direct f
  openExtension : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y),
    IsOpenImmersion j.hom.left → B X ⥤ B Y
  openAdjunction : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left), openExtension j hj ⊣ pull j
  support : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    Compactification f.hom.left → B X ⥤ B Y
  exceptional : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    Compactification f.hom.left → B Y ⥤ B X
  exceptionalAdjunction : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left), support f c ⊣ exceptional f c
  comparison : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left), support f c ≅ support f d
  comparison_refl : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left), comparison f c c = Iso.refl _
  comparison_trans : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d e : Compactification f.hom.left),
    comparison f c e = comparison f c d ≪≫ comparison f d e
  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left),
    support (f ≫ g) cfg ≅ support f cf ⋙ support g cg
  composition_comparison : ∀ {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf df : Compactification f.hom.left) (cg dg : Compactification g.hom.left)
    (cfg dfg : Compactification (f ≫ g).hom.left),
    comparison (f ≫ g) cfg dfg ≪≫ composition f g df dg dfg =
      composition f g cf cg cfg ≪≫
        Functor.isoWhiskerRight (comparison f cf df) (support g cg) ≪≫
        Functor.isoWhiskerLeft (support f df) (comparison g cg dg)
  properIdentity : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left], support f (.ofIsProper f.hom.left) ≅ direct f
  openIdentification : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left),
    support j (sixFunctorOpenCompactification j hj) ≅ openExtension j hj

/-- The proper identification factors through the identity-open compactification.
Source: clause (2) (blueprint: def-sf-operation-stages). -/
def SixFunctorPushStage.properIdentification {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left] (c : Compactification f.hom.left) :=
  S.comparison f c (.ofIsProper f.hom.left) ≪≫ S.properIdentity f

/-- The open exchange inverse is the mate of the prescribed pullback square.
Source: def-exchange-projection, open factor
(blueprint: def-sf-operation-stages). -/
def sixFunctorOpenBaseChangeInverse {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (Q : SixFunctorCompactifiedSquare D) :=
  Functor.whiskerRight
      (Functor.whiskerRight (S.openAdjunction Q.i Q.open_i).unit (S.pull Q.g'))
      (S.openExtension Q.i' Q.open_i') ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (S.openExtension Q.i Q.open_i)
        ((S.pullComposition Q.g' Q.i).symm ≪≫
          eqToIso (congrArg (fun e ↦ S.pull e) Q.openComm) ≪≫
          S.pullComposition Q.i' Q.h).hom)
      (S.openExtension Q.i' Q.open_i') ≫
    Functor.whiskerLeft (S.openExtension Q.i Q.open_i ⋙ S.pull Q.h)
      (S.openAdjunction Q.i' Q.open_i').counit

/-- The inverse open projection is the transpose of the open unit tensored with identity,
followed by inverse tensor pullback and the specified f=pi comparison.
Source: def-exchange-projection, projection factor gamma
(blueprint: def-sf-operation-stages). -/
def sixFunctorOpenProjectionInverse {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (Q : SixFunctorCompactifiedSquare D)
    (μ : (Functor.postcompose₂.obj (S.pull Q.i)).obj (T Q.Z) ≅
      (((Functor.whiskeringLeft₂ _).obj (S.pull Q.i)).obj (S.pull Q.i)).obj (T Q.X))
    (K : B Q.X) (N : B Q.Y) :=
  (S.openExtension Q.i Q.open_i).map
      (((T Q.X).obj K).map
        ((eqToIso (congrArg (fun e ↦ S.pull e) Q.factorization) ≪≫
          S.pullComposition Q.i Q.p).hom.app N)) ≫
    ((S.openAdjunction Q.i Q.open_i).homEquiv _ _).symm
      (((T Q.X).map ((S.openAdjunction Q.i Q.open_i).unit.app K)).app
          ((S.pull Q.i).obj ((S.pull Q.p).obj N)) ≫
        (μ.inv.app ((S.openExtension Q.i Q.open_i).obj K)).app ((S.pull Q.p).obj N))

/-- A compactification given by its actual open and proper factors in the base category.
Source: clause (2), compactification formula
(blueprint: def-sf-operation-stages). -/
def sixFunctorFactorCompactification {D : FiniteFieldDatum.{u}}
    {X Y Z : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (hi : IsOpenImmersion i.hom.left) (hp : IsProper p.hom.left)
    (f : X ⟶ Y) (h : f = i ≫ p) : Compactification f.hom.left where
  Z := Z.obj.left
  i := i.hom.left
  g := p.hom.left
  comm := congrArg (fun e : X ⟶ Y ↦ e.hom.left) h
  isOpenImmersion := hi
  isProper := hp

/-- The support factorization uses the recorded composition law, then the open and
proper identity identifications, in exactly that order.
Source: def-exchange-projection, candidate realization
(blueprint: def-sf-operation-stages). -/
def sixFunctorFactoredSupportIdentification {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y Z : SixFunctorSpace D}
    (i : X ⟶ Z) (p : Z ⟶ Y)
    (hi : IsOpenImmersion i.hom.left) (hp : IsProper p.hom.left)
    (f : X ⟶ Y) (h : f = i ≫ p) :
    S.support f (sixFunctorFactorCompactification i p hi hp f h) ≅
      S.openExtension i hi ⋙ S.direct p := by
  subst f
  letI := hp
  exact S.composition i p (sixFunctorOpenCompactification i hi)
      (.ofIsProper p.hom.left) (sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl) ≪≫
    Functor.isoWhiskerRight (S.openIdentification i hi) _ ≪≫
    Functor.isoWhiskerLeft _ (S.properIdentity p)

/-- The dependency's mate, proper/open paste, and projection construction at a
higher coefficient stage, tied to the very operations of that stage. Its three
maps are `stage.exchange`, `stage.compactExchange`, and `stage.projection`.
Source: clause (3), def-exchange-projection
(blueprint: def-sf-operation-stages). -/
structure SixFunctorExchangeData {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (Q : SixFunctorCompactifiedSquare D) where
  stage : ExchangeProjectionStage (DX := B Q.X) (DB := B Q.Z) (DY := B Q.Y)
    (DX' := B Q.X') (DB' := B Q.Z') (DY' := B Q.Y')
  pull : stage.pull = S.pull Q.f
  push : stage.push = S.direct Q.f
  pull' : stage.pull' = S.pull Q.f'
  push' : stage.push' = S.direct Q.f'
  adjunction : HEq stage.adjunction (S.pullDirectAdjunction Q.f)
  adjunction' : HEq stage.adjunction' (S.pullDirectAdjunction Q.f')
  horizontal : stage.horizontal = S.pull Q.g
  horizontal' : stage.horizontal' = S.pull Q.g'
  openExtension : stage.openExtension = S.openExtension Q.i Q.open_i
  openExtension' : stage.openExtension' = S.openExtension Q.i' Q.open_i'
  properPull : stage.properPull = S.pull Q.p
  properPush : stage.properPush = S.direct Q.p
  properPull' : stage.properPull' = S.pull Q.p'
  properPush' : stage.properPush' = S.direct Q.p'
  properAdjunction : HEq stage.properAdjunction (S.pullDirectAdjunction Q.p)
  properAdjunction' : HEq stage.properAdjunction' (S.pullDirectAdjunction Q.p')
  compactifyingHorizontal : stage.compactifyingHorizontal = S.pull Q.h
  tensorX : stage.tensorX = T Q.X
  tensorBar : stage.tensorBar = T Q.Z
  tensorY : stage.tensorY = T Q.Y
  compactSupport : stage.compactSupport = S.support Q.f Q.compactification
  compactSupport' : stage.compactSupport' = S.support Q.f' Q.compactification'
  pullbackNormalization : HEq stage.pullbackComparison
    ((S.pullComposition Q.f' Q.g).symm ≪≫
      eqToIso (congrArg (fun e ↦ S.pull e) Q.squareComm.symm) ≪≫
      S.pullComposition Q.g' Q.f)
  properPullbackNormalization : HEq stage.properPullbackComparison
    ((S.pullComposition Q.p' Q.g).symm ≪≫
      eqToIso (congrArg (fun e ↦ S.pull e) Q.properComm.symm) ≪≫
      S.pullComposition Q.h Q.p)
  openBaseChangeNormalization : HEq stage.openBaseChange.inv
    (sixFunctorOpenBaseChangeInverse S Q)
  openTensorPullback :
    (Functor.postcompose₂.obj (S.pull Q.i)).obj (T Q.Z) ≅
      (((Functor.whiskeringLeft₂ _).obj (S.pull Q.i)).obj (S.pull Q.i)).obj (T Q.X)
  openProjectionNormalization : ∀ (K : B Q.X) (N : B Q.Y),
    HEq ((stage.openProjection.inv.app K).app N)
      (sixFunctorOpenProjectionInverse S T Q openTensorPullback K N)
  compactSupportNormalization : HEq stage.compactSupportIdentification
    (sixFunctorFactoredSupportIdentification S Q.i Q.p Q.open_i Q.proper_p
      Q.f Q.factorization)
  compactSupportNormalization' : HEq stage.compactSupportIdentification'
    (sixFunctorFactoredSupportIdentification S Q.i' Q.p' Q.open_i' Q.proper_p'
      Q.f' Q.factorization')

/-- Coefficient change retains the specified adjunctions, compactification
comparisons, and their units and counits. This is a record of actual natural
isomorphisms and commuting diagrams, not five arbitrary proposition fields.
Source: def-exchange-projection and the higher-coefficient construction clauses
(blueprint: def-sf-operation-stages). -/
structure SixFunctorCoefficientComparison {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
    (S : SixFunctorPushStage D B) (S' : SixFunctorPushStage D B')
    (L : ∀ X, B X ⥤ B' X) where
  directAdjunction : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    ExchangeProjectionAdjunctionComparison (S.pullDirectAdjunction f)
      (S'.pullDirectAdjunction f) (L Y) (L X)
  supportAdjunction : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left),
    ExchangeProjectionAdjunctionComparison (S.exceptionalAdjunction f c)
      (S'.exceptionalAdjunction f c) (L X) (L Y)
  openExtension : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left),
    S.openExtension j hj ⋙ L Y ≅ L X ⋙ S'.openExtension j hj
  compactification : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left),
    ExchangeProjectionComparisonPreserves (L X) (L Y)
      (supportAdjunction f c).left (supportAdjunction f d).left
      (S.comparison f c d).hom (S'.comparison f c d).hom

  /-- Open adjunctions commute with the same operation comparisons. -/
  openAdjunction : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left),
    ExchangeProjectionAdjunctionComparison (S.openAdjunction j hj)
      (S'.openAdjunction j hj) (L X) (L Y)
  openAdjunction_left : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left), (openAdjunction j hj).left = openExtension j hj
  openAdjunction_right : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left),
    (openAdjunction j hj).right = (directAdjunction j).left
  /-- The compositor is carried through the actual two support comparisons. -/
  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X),
    (L Z).map ((S.composition f g cf cg cfg).hom.app K) ≫
        (supportAdjunction g cg).left.hom.app ((S.support f cf).obj K) ≫
        (S'.support g cg).map ((supportAdjunction f cf).left.hom.app K) =
      (supportAdjunction (f ≫ g) cfg).left.hom.app K ≫
        (S'.composition f g cf cg cfg).hom.app ((L X).obj K)
  properIdentity : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left] (K : B X),
    (L Y).map ((S.properIdentity f).hom.app K) ≫ (directAdjunction f).right.hom.app K =
      (supportAdjunction f (.ofIsProper f.hom.left)).left.hom.app K ≫
        (S'.properIdentity f).hom.app ((L X).obj K)
  openIdentification : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) (K : B X),
    (L Y).map ((S.openIdentification j hj).hom.app K) ≫
        (openExtension j hj).hom.app K =
      (supportAdjunction j (sixFunctorOpenCompactification j hj)).left.hom.app K ≫
        (S'.openIdentification j hj).hom.app ((L X).obj K)
  pullComposition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z) (K : B Z),
    (L X).map ((S.pullComposition f g).hom.app K) ≫
        (directAdjunction f).left.hom.app ((S.pull g).obj K) ≫
        (S'.pull f).map ((directAdjunction g).left.hom.app K) =
      (directAdjunction (f ≫ g)).left.hom.app K ≫
        (S'.pullComposition f g).hom.app ((L Z).obj K)

/-- Localization and common-stage inclusion keep the prescribed object models.
Their operation comparisons are identity components on those models, rather than
freely chosen automorphisms. Together with SixFunctorCoefficientComparison this
pins comparison, composition, proper/open identification and both adjunctions.
Source: rational and common-stage construction formulas, clauses (1)--(4)
(blueprint: def-sf-operation-stages). -/
def SixFunctorCoefficientModelNormalization {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {L : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' L) : Prop :=
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (K : B X),
    HEq ((C.directAdjunction f).right.hom.app K)
      (𝟙 ((L Y).obj ((S.direct f).obj K)))) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (K : B Y),
    HEq ((C.directAdjunction f).left.hom.app K)
      (𝟙 ((L X).obj ((S.pull f).obj K)))) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : B X),
    HEq ((C.supportAdjunction f c).left.hom.app K)
      (𝟙 ((L Y).obj ((S.support f c).obj K)))) ∧
  (∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) (K : B X),
    HEq ((C.openExtension j hj).hom.app K)
      (𝟙 ((L Y).obj ((S.openExtension j hj).obj K))))

/-- Compose the two operation-realization isomorphisms, inserting only associators.
Source: coefficient-change paragraph of def-exchange-projection
(blueprint: def-sf-operation-stages). -/
def sixFunctorCompositeRealization
    {A : Type v} {B : Type w} {C : Type hA}
    {A' : Type v'} {B' : Type w'} {C' : Type hA'}
    [Category.{hB} A] [Category.{hB} B] [Category.{hB} C]
    [Category.{hB'} A'] [Category.{hB'} B'] [Category.{hB'} C']
    {F : A ⥤ B} {G : B ⥤ C} {F' : A' ⥤ B'} {G' : B' ⥤ C'}
    {LA : A ⥤ A'} {LB : B ⥤ B'} {LC : C ⥤ C'}
    (α : F ⋙ LB ≅ LA ⋙ F') (β : G ⋙ LC ≅ LB ⋙ G') :
    (F ⋙ G) ⋙ LC ≅ LA ⋙ (F' ⋙ G') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ β ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α _ ≪≫
    Functor.associator _ _ _

/-- A transformation square has specified endpoints; neither endpoint is new data.
Source: def-exchange-projection, coefficient comparisons
(blueprint: def-sf-operation-stages). -/
def SixFunctorTransformationComparison
    {A : Type v} {B : Type w} {A' : Type v'} {B' : Type w'}
    [Category.{hA} A] [Category.{hB} B] [Category.{hA'} A'] [Category.{hB'} B']
    (L : A ⥤ A') (R : B ⥤ B')
    {F G : A ⥤ B} {F' G' : A' ⥤ B'} (η : F ⟶ G) (η' : F' ⟶ G')
    (source : F ⋙ R ≅ L ⋙ F') (target : G ⋙ R ≅ L ⋙ G') : Prop :=
  ExchangeProjectionComparisonPreserves L R source target η η'

/-- Transport a prescribed operation realization along the recorded stage equalities.
Source: def-exchange-projection, realization convention
(blueprint: def-sf-operation-stages). -/
def sixFunctorStageRealization
    {A : Type v} {B : Type w} {A' : Type v'} {B' : Type w'}
    [Category.{hA} A] [Category.{hB} B] [Category.{hA'} A'] [Category.{hB'} B']
    {L : A ⥤ A'} {R : B ⥤ B'} {F G : A ⥤ B} {F' G' : A' ⥤ B'}
    (h : F = G) (h' : F' = G') (α : G ⋙ R ≅ L ⋙ G') :
    F ⋙ R ≅ L ⋙ F' :=
  Functor.isoWhiskerRight (eqToIso h) R ≪≫ α ≪≫
    Functor.isoWhiskerLeft L (eqToIso h').symm

/-- The projection component in the named operation coordinates, using only the
recorded functor equalities. Source: clause (3)
(blueprint: def-sf-operation-stages). -/
def SixFunctorExchangeData.projectionComponent {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q)
    (K : B Q.X) (N : B Q.Y) :
    ((T Q.Y).obj ((S.support Q.f Q.compactification).obj K)).obj N ⟶
      (S.support Q.f Q.compactification).obj
        (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) :=
  eqToHom (by simp only [Functor.comp_obj, A.tensorY, A.compactSupport]) ≫
    ((A.stage.projection).app K).app N ≫
    eqToHom (by rw [A.tensorX, A.compactSupport, A.pull]; rfl)

/-- Coefficient comparison for the actual exchange maps. Endpoints are composites
of the operation realizations, rather than independent isomorphisms.
Source: clause (3) (blueprint: def-sf-operation-stages). -/
structure SixFunctorExchangeComparison {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (L : ∀ X, B X ⥤ B' X) (C : SixFunctorCoefficientComparison S S' L) where
  tensor : ∀ X : SixFunctorSpace D,
    Functor.uncurry.obj (T X) ⋙ L X ≅
      (L X).prod (L X) ⋙ Functor.uncurry.obj (T' X)
  exchange : SixFunctorTransformationComparison (L Q.X) (L Q.Y')
    A.stage.exchange A'.stage.exchange
    (sixFunctorCompositeRealization
      (sixFunctorStageRealization A.push A'.push (C.directAdjunction Q.f).right)
      (sixFunctorStageRealization A.horizontal A'.horizontal (C.directAdjunction Q.g).left))
    (sixFunctorCompositeRealization
      (sixFunctorStageRealization A.horizontal' A'.horizontal'
        (C.directAdjunction Q.g').left)
      (sixFunctorStageRealization A.push' A'.push' (C.directAdjunction Q.f').right))
  compactExchange : SixFunctorTransformationComparison (L Q.X) (L Q.Y')
    A.stage.compactExchange A'.stage.compactExchange
    (sixFunctorCompositeRealization
      (sixFunctorStageRealization A.compactSupport A'.compactSupport
        (C.supportAdjunction Q.f Q.compactification).left)
      (sixFunctorStageRealization A.horizontal A'.horizontal (C.directAdjunction Q.g).left))
    (sixFunctorCompositeRealization
      (sixFunctorStageRealization A.horizontal' A'.horizontal'
        (C.directAdjunction Q.g').left)
      (sixFunctorStageRealization A.compactSupport' A'.compactSupport'
        (C.supportAdjunction Q.f' Q.compactification').left))
  /-- The projection square is evaluated componentwise, with source tensor realization
  and target support realization at the tensor of the realized input objects. -/
  projection : ∀ (K : B Q.X) (N : B Q.Y),
    HEq ((L Q.Y).map (A.projectionComponent K N) ≫
      (C.supportAdjunction Q.f Q.compactification).left.hom.app
        (((T Q.X).obj K).obj ((S.pull Q.f).obj N)))
      ((tensor Q.Y).hom.app ((S.support Q.f Q.compactification).obj K, N) ≫
        (Functor.uncurry.obj (T' Q.Y)).map
          (Prod.mkHom ((C.supportAdjunction Q.f Q.compactification).left.hom.app K) (𝟙 _)) ≫
        A'.projectionComponent ((L Q.X).obj K) ((L Q.Y).obj N) ≫
        (S'.support Q.f Q.compactification).map
          ((Functor.uncurry.obj (T' Q.X)).map
            (Prod.mkHom (𝟙 _) ((C.directAdjunction Q.f).left.inv.app N)) ≫
            (tensor Q.X).inv.app (K, (S.pull Q.f).obj N)))

/-- The duality construction uses the same exceptional functor and internal Hom.
The pair condition is the recorded bounded-Hom domain, not an unrestricted Hom
closure hypothesis. Source: clause (5) (blueprint: def-sf-operation-stages). -/
structure SixFunctorDualityData {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B)
    (P : ∀ X, ObjectProperty ((B X)ᵒᵖ × B X)) where
  unit : B (sixFunctorPoint D)
  dualPair : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (K : (B X)ᵒᵖ),
    P X (K, (S.exceptional (sixFunctorStructure X) c).obj unit)

/-- Exceptional inverse image of the coefficient unit, with no independent choice
of a dualizing object. Source: clause (5) (blueprint: def-sf-operation-stages). -/
def SixFunctorDualityData.dualizing {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {P : ∀ X, ObjectProperty ((B X)ᵒᵖ × B X)}
    (T : SixFunctorDualityData S P) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left) : B X :=
  (S.exceptional (sixFunctorStructure X) c).obj T.unit

/-- Internal Hom into that very dualizing object, including the functor action.
Source: clause (5) (blueprint: def-sf-operation-stages). -/
def SixFunctorDualityData.verdier {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {P : ∀ X, ObjectProperty ((B X)ᵒᵖ × B X)}
    (T : SixFunctorDualityData S P)
    (H : ∀ X, (P X).FullSubcategory ⥤ B X) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left) :
    (B X)ᵒᵖ ⥤ B X :=
  (P X).lift
    ((𝟭 (B X)ᵒᵖ).prod' ((Functor.const (B X)ᵒᵖ).obj (T.dualizing X c)))
    (T.dualPair X c) ⋙ H X

/-- Finite bounded constructible objects in the existing intrinsic realization.
Source: initial domains (blueprint: def-sf-operation-stages). -/
abbrev sixFunctorFiniteCategory (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) (X : SixFunctorSpace D) :=
  (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).FullSubcategory

/-- The positive exponent version of the recorded ambient finite Hom.
Source: clause (1) (blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteInternalHom (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) (X : SixFunctorSpace D) :
    (proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n))ᵒᵖ ×
      proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) ⥤
        proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ m => exact finiteIntrinsicDerivedInternalHom C.l E X.obj.left m

/-- Positive-exponent ambient tensor from the recorded quotient construction.
Source: clause (1) (blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteTensor (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) (X : SixFunctorSpace D) :
    proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) ×
      proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) ⥤
        proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ m => exact finiteIntrinsicDerivedTensor C.l E X.obj.left m

/-- Positive-exponent ambient pullback, including exponent one.
Source: clause (1) (blueprint: def-sf-operation-stages). -/
def sixFunctorFinitePullback (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    proEtaleDerivedCategory Y.obj.left (Padic.coefficientExtensionRing C.l E n) ⥤
      proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing C.l E n) f.hom.left

/-- The finite permitted-Hom domain is the inverse image of bounded constructibility
under the recorded ambient internal Hom. Source: clause (1)
(blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteHomPairs (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) (X : SixFunctorSpace D) :
    ObjectProperty ((sixFunctorFiniteCategory D C E n hn X)ᵒᵖ ×
      sixFunctorFiniteCategory D C E n hn X) :=
  fun MN ↦ intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left
    ((sixFunctorFiniteInternalHom D C E n hn X).obj
      (op MN.1.unop.obj, MN.2.obj))

/-- Restrict the existing finite internal Hom on exactly its bounded-output pairs.
Source: clause (1) (blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteHom (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) (X : SixFunctorSpace D) :
    (sixFunctorFiniteHomPairs D C E n hn X).FullSubcategory ⥤
      sixFunctorFiniteCategory D C E n hn X :=
  (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).lift
    ((sixFunctorFiniteHomPairs D C E n hn X).ι ⋙
      ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.op.prod
        (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι) ⋙
      sixFunctorFiniteInternalHom D C E n hn X)
    (fun MN ↦ MN.property)

/-- The bundled finite-type object uses its given structure map, without choosing
an alternative map to the base. Source: initial setting
(blueprint: def-sf-operation-stages). -/
instance sixFunctorSpaceOver {D : FiniteFieldDatum.{u}} (X : SixFunctorSpace D) :
    X.obj.left.Over (Spec (.of D.k)) := ⟨X.obj.hom⟩

/-- Finite-type structure from the existing full subcategory.
Source: initial setting (blueprint: def-sf-operation-stages). -/
instance sixFunctorSpaceLft {D : FiniteFieldDatum.{u}} (X : SixFunctorSpace D) :
    LocallyOfFiniteType (X.obj.left ↘ Spec (.of D.k)) := X.property.1

/-- Quasi-compactness from the same finite-type structure.
Source: initial setting (blueprint: def-sf-operation-stages). -/
instance sixFunctorSpaceQc {D : FiniteFieldDatum.{u}} (X : SixFunctorSpace D) :
    QuasiCompact (X.obj.left ↘ Spec (.of D.k)) := X.property.2

/-- Over-category arrows retain the base compatibility equation.
Source: initial setting (blueprint: def-sf-operation-stages). -/
instance sixFunctorMapOver {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) : f.hom.left.IsOver (Spec (.of D.k)) := ⟨Over.w f.hom⟩

/-- The normalized tower construction of the integral and rational support functors.
The tower is the dependency's specified construction; the total inverse limit
carries its right-derived universal property and its unit is invertible on K-injectives;
comparison with the chosen Roos vertex preserves every projection. Rational maps
are the linear extension on pure tensors. This records the complete construction,
rather than selecting an operation from a weakened existence statement.
Source: lem-weil-compact-support-reduction-tower-functor and the normalized
compact-support value definitions, clauses (1)--(4)
(blueprint: def-sf-operation-stages). -/
def SixFunctorSupportConstruction
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (hl : IsUnit (C.l : D.k)) (c : Compactification f.hom.left)
    [HasCountableProducts (DerivedCategory (scalarReductionSource C.l E Y.obj.left))]
    (F : sfIntegralConstructibleCategory C.l E X.obj.left ⥤
      sfIntegralConstructibleCategory C.l E Y.obj.left)
    (G : sfRationalConstructibleCategory C.l E X.obj.left ⥤
      sfRationalConstructibleCategory C.l E Y.obj.left) : Prop :=
  ∃ towerDatum : CompactSupportReductionTowerConstruction C.l E f.hom.left c,
  (F.Additive) ∧
  (F.Linear (Padic.coefficientExtensionIntegers C.l E)) ∧
  (∀ K, F.obj K = sfIntegralCompactSupportValue C.l E D.k hl c K) ∧
  ∃ comparison : F ⋙ (sfIntegralConstructible C.l E Y.obj.left).ι ≅
    (sfIntegralConstructible C.l E X.obj.left).ι ⋙ towerDatum.tower ⋙ towerDatum.limit,
  (∀ (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (m : ℕ), HEq
      (comparison.hom.app K ≫ (towerDatum.projections m).app (towerDatum.tower.obj K.obj) ≫
        (towerDatum.evaluations m).hom.app K.obj)
      (Classical.choose (Classical.choose_spec (exists_isDerivedLimit_and_iso
        (sfCompactSupportTerm C.l E c K.obj)
        (sfCompactSupportTransition C.l E c K.obj)).1) ≫
          Pi.π (sfCompactSupportTerm C.l E c K.obj) m)) ∧
  (G.Linear (Localization.Away (Padic.coefficientExtensionUniformizer C.l E))) ∧
  (∀ K, G.obj ((sfRationalConstructibleLocalization C.l E X.obj.left).obj K) =
    sfRationalCompactSupportValue C.l E D.k hl c K) ∧
  (∀ (K K' : sfIntegralConstructibleCategory C.l E X.obj.left)
    (v : K ⟶ K') (a : Localization.Away (Padic.coefficientExtensionUniformizer C.l E)),
    HEq (G.map (a ⊗ₜ[Padic.coefficientExtensionIntegers C.l E] v :
      (sfRationalConstructibleLocalization C.l E X.obj.left).obj K ⟶
        (sfRationalConstructibleLocalization C.l E X.obj.left).obj K'))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers C.l E]
        (F.map v : F.obj K ⟶ F.obj K')))

/-- The degree-zero completed rank-one coefficient module.
Source: clause (5) (blueprint: def-sf-operation-stages). -/
def sixFunctorIntegralUnit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : DerivedCategory (scalarReductionSource l E X) :=
  DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit _))

/-- Completed and localized operation constructions at a finite coefficient field.
The equations identify the functors with their recorded constructions, including
morphism actions. The generic stage retains all compactification and adjunction
comparisons. Source: higher-coefficient clauses (1)--(5)
(blueprint: def-sf-operation-stages). -/
structure SixFunctorHigherOperations
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] where
  integral : SixFunctorPushStage D (fun X ↦ sfIntegralConstructibleCategory C.l E X.obj.left)
  rational : SixFunctorPushStage D (fun X ↦ sfRationalConstructibleCategory C.l E X.obj.left)
  integralDuality : SixFunctorDualityData integral
    (fun X ↦ constructibleIntegralHomPairs C.l E X.obj.left)
  rationalDuality : SixFunctorDualityData rational
    (fun X ↦ constructibleRationalHomPairs C.l E X.obj.left)
  integralTensor : ∀ X : SixFunctorSpace D,
    sfIntegralConstructibleCategory C.l E X.obj.left ⥤
      sfIntegralConstructibleCategory C.l E X.obj.left ⥤
        sfIntegralConstructibleCategory C.l E X.obj.left
  rationalTensor : ∀ X : SixFunctorSpace D,
    sfRationalConstructibleCategory C.l E X.obj.left ⥤
      sfRationalConstructibleCategory C.l E X.obj.left ⥤
        sfRationalConstructibleCategory C.l E X.obj.left
  integralTensorNormalization : ∀ (X : SixFunctorSpace D)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)],
    integralTensor X = Functor.currying.inverse.obj (constructibleIntegralTensor C.l E X.obj.left)
  rationalTensorNormalization : ∀ (X : SixFunctorSpace D)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)],
    rationalTensor X = Functor.currying.inverse.obj (rationalDerivedTensor C.l E X.obj.left)
  integralExchange : ∀ Q : SixFunctorCompactifiedSquare D,
    SixFunctorExchangeData integral integralTensor Q
  rationalExchange : ∀ Q : SixFunctorCompactifiedSquare D,
    SixFunctorExchangeData rational rationalTensor Q
  integralTensorPullbackNormalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [∀ x : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField x)]
    [∀ y : Q.Y.obj.left, Invertible (C.l : Q.Y.obj.left.residueField y)]
    (M N : sfIntegralConstructibleCategory C.l E Q.Y.obj.left),
    HEq (((integralExchange Q).stage.tensorPullback.hom.app M).app N)
      ((canonicalIntegralPullbackTensor C.l E Q.p.hom.left M N).hom)
  integralOpenTensorPullbackNormalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [∀ x : Q.X.obj.left, Invertible (C.l : Q.X.obj.left.residueField x)]
    [∀ z : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField z)]
    (M N : sfIntegralConstructibleCategory C.l E Q.Z.obj.left),
    HEq (((integralExchange Q).openTensorPullback.hom.app M).app N)
      ((canonicalIntegralPullbackTensor C.l E Q.i.hom.left M N).hom)
  rationalTensorPullbackNormalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [∀ x : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField x)]
    [∀ y : Q.Y.obj.left, Invertible (C.l : Q.Y.obj.left.residueField y)]
    (M N : sfRationalConstructibleCategory C.l E Q.Y.obj.left),
    HEq (((rationalExchange Q).stage.tensorPullback.hom.app M).app N)
      ((canonicalRationalPullbackTensor C.l E Q.p.hom.left M N).hom)
  rationalOpenTensorPullbackNormalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [∀ x : Q.X.obj.left, Invertible (C.l : Q.X.obj.left.residueField x)]
    [∀ z : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField z)]
    (M N : sfRationalConstructibleCategory C.l E Q.Z.obj.left),
    HEq (((rationalExchange Q).openTensorPullback.hom.app M).app N)
      ((canonicalRationalPullbackTensor C.l E Q.i.hom.left M N).hom)
  rationalization : SixFunctorCoefficientComparison integral rational
    (fun X ↦ sfRationalConstructibleLocalization C.l E X.obj.left)
  rationalExchangeComparison : ∀ Q : SixFunctorCompactifiedSquare D,
    SixFunctorExchangeComparison (S := integral) (S' := rational)
      (T := integralTensor) (T' := rationalTensor) (integralExchange Q) (rationalExchange Q)
      (fun X ↦ sfRationalConstructibleLocalization C.l E X.obj.left) rationalization
  integralPullback : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)],
    integral.pull f = constructibleIntegralPullback C.l E f.hom.left
  rationalPullback : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)],
    rational.pull f = rationalDerivedPullback C.l E f.hom.left
  integralDirectImage : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    integral.direct f ⋙ (sfIntegralConstructible C.l E Y.obj.left).ι ≅
      (sfIntegralConstructible C.l E X.obj.left).ι ⋙
        sfCompletedDerivedDirectImage C.l E f.hom.left
  integralDirectLimit : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    [HasProduct (sfDirectImageTerm C.l E f.hom.left K.obj)],
    SfIntegralDirectImage C.l E f.hom.left K.obj
  integralDirectLimitObject : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    [HasProduct (sfDirectImageTerm C.l E f.hom.left K.obj)],
    (integralDirectLimit f K).obj = ((integral.direct f).obj K).obj
  rationalDirectImage : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    sfRationalConstructibleLocalization C.l E X.obj.left ⋙ rational.direct f ≅
      integral.direct f ⋙ sfRationalConstructibleLocalization C.l E Y.obj.left
  supportConstruction : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (hl : IsUnit (C.l : D.k)) (c : Compactification f.hom.left),
    (fun [_hproducts : HasCountableProducts
      (DerivedCategory (scalarReductionSource C.l E Y.obj.left))] ↦
        SixFunctorSupportConstruction D C E f hl c (integral.support f c)
          (rational.support f c))
      (_hproducts := integralOperationsDerivedCountableProducts C.l E Y.obj.left)
  rationalModelNormalization : SixFunctorCoefficientModelNormalization rationalization
  integralUnit : integralDuality.unit.obj ≅ sixFunctorIntegralUnit C.l E (Spec (.of D.k))
  rationalUnit : rationalDuality.unit ≅
    (sfRationalConstructibleLocalization C.l E (Spec (.of D.k))).obj integralDuality.unit

/-- The identity transition is the recorded scalar unit, transported through the
specified stage-system equality. Source: common-stage coefficient conventions
(blueprint: def-sf-operation-stages). -/
def sixFunctorStageUnitor (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : SixFunctorSpace D) (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
    (stageSystem C.l C.Qbar X.obj.left).T (le_rfl : E₀ ≤ E₀) ≅
      𝟭 (Stage C.l C.Qbar X.obj.left E₀) :=
  operationStageTransitionIso C.l C.Qbar X.obj.left E₀ E₀ le_rfl ≪≫
    GeneralAlgebraicallyClosedCoefficients.unitor C.l C.Qbar X.obj.left E₀

/-- The recorded finite compact-support candidate, with quotient finiteness
supplied by the named positive-quotient theorem. Source: clause (2)
(blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteSupport (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing C.l E n)

/-- The recorded etale-transported finite exceptional functor, without an ambient
admissibility hypothesis. Source: clause (4)
(blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteExceptional (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  AlgebraicGeometry.ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E n) c

/-- The recorded termwise finite extension by zero.
Source: clause (2) (blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteOpen (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : SixFunctorSpace D} (j : X ⟶ Y) (hj : IsOpenImmersion j.hom.left) :=
  letI := hj
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (sfIntrinsicExtensionByZero j.hom.left
    (Padic.coefficientExtensionRing C.l E n)).mapDerivedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Rational operations at the specified small coefficient model.
Source: common-stage conventions (blueprint: def-sf-operation-stages). -/
def sixFunctorCoefficientRational (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (A : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SixFunctorHigherOperations D C (Coefficient.{u} C.l C.Qbar E₀))
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
    SixFunctorPushStage D (fun X ↦ Stage C.l C.Qbar X.obj.left E₀) :=
  (A E₀).rational

/-- Tensor at the same small coefficient model.
Source: clause (3) (blueprint: def-sf-operation-stages). -/
def sixFunctorCoefficientTensor (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (A : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SixFunctorHigherOperations D C (Coefficient.{u} C.l C.Qbar E₀))
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
    ∀ X : SixFunctorSpace D, Stage C.l C.Qbar X.obj.left E₀ ⥤
      Stage C.l C.Qbar X.obj.left E₀ ⥤ Stage C.l C.Qbar X.obj.left E₀ :=
  (A E₀).rationalTensor

/-- The three exchange constructions at that small coefficient model.
Source: clause (3) (blueprint: def-sf-operation-stages). -/
def sixFunctorCoefficientExchange (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (A : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SixFunctorHigherOperations D C (Coefficient.{u} C.l C.Qbar E₀))
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) (Q : SixFunctorCompactifiedSquare D) :
    SixFunctorExchangeData (sixFunctorCoefficientRational D C A E₀)
      (sixFunctorCoefficientTensor D C A E₀) Q :=
  (A E₀).rationalExchange Q

/-- The coefficient unit and dualizing construction at that coefficient model.
Source: clause (5) (blueprint: def-sf-operation-stages). -/
def sixFunctorCoefficientDuality (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (A : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SixFunctorHigherOperations D C (Coefficient.{u} C.l C.Qbar E₀))
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
    SixFunctorDualityData (sixFunctorCoefficientRational D C A E₀)
      (fun X ↦ constructibleRationalHomPairs C.l
        (Coefficient.{u} C.l C.Qbar E₀) X.obj.left) :=
  (A E₀).rationalDuality

/-- Common-stage operations and the specified finite-stage comparisons.
These are actual functors and exchange data on the recorded pair categories.
Source: clauses (1)--(5) and common-stage coefficient conventions
(blueprint: def-sf-operation-stages). -/
structure SixFunctorCommonStages (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum) where
  coefficientStages : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    SixFunctorHigherOperations D C (Coefficient.{u} C.l C.Qbar E₀)
  commonStage : SixFunctorPushStage D
    (fun X ↦ generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
  commonStageDuality : SixFunctorDualityData commonStage
    (fun X ↦ commonStageHomPairs C.l C.Qbar X.obj.left)

  commonStagePullback : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)],
    commonStage.pull f = commonStageDerivedPullback C.l C.Qbar f.hom.left
  commonStageTensor : ∀ X : SixFunctorSpace D,
    generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left ⥤
      generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left ⥤
        generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left
  commonStageTensorNormalization : ∀ (X : SixFunctorSpace D)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)],
    commonStageTensor X = Functor.currying.inverse.obj
      (commonStageDerivedTensor C.l C.Qbar X.obj.left)
  commonStageExchange : ∀ Q : SixFunctorCompactifiedSquare D,
    SixFunctorExchangeData commonStage commonStageTensor Q
  commonStageTensorPullbackNormalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [∀ x : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField x)]
    [∀ y : Q.Y.obj.left, Invertible (C.l : Q.Y.obj.left.residueField y)]
    (M N : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Q.Y.obj.left),
    HEq (((commonStageExchange Q).stage.tensorPullback.hom.app M).app N)
      ((canonicalCommonStagePullbackTensor C.l C.Qbar Q.p.hom.left M N).hom)
  commonStageOpenTensorPullbackNormalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [∀ x : Q.X.obj.left, Invertible (C.l : Q.X.obj.left.residueField x)]
    [∀ z : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField z)]
    (M N : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Q.Z.obj.left),
    HEq (((commonStageExchange Q).openTensorPullback.hom.app M).app N)
      ((canonicalCommonStagePullbackTensor C.l C.Qbar Q.i.hom.left M N).hom)
  coefficientTransition : ∀ {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L),
    SixFunctorCoefficientComparison (sixFunctorCoefficientRational D C coefficientStages E₀)
      (sixFunctorCoefficientRational D C coefficientStages L)
      (fun X ↦ (stageSystem C.l C.Qbar X.obj.left).T h)
  commonStageComparison : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    SixFunctorCoefficientComparison
      (sixFunctorCoefficientRational D C coefficientStages E₀) commonStage
      (fun X ↦ inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀)
  coefficientExchangeComparison : ∀ {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar}
    (h : E₀ ≤ L) (Q : SixFunctorCompactifiedSquare D),
    @SixFunctorExchangeComparison D
      (fun X ↦ Stage C.l C.Qbar X.obj.left E₀)
      (fun X ↦ inferInstanceAs
        (Category (Stage C.l C.Qbar X.obj.left E₀)))
      (fun X ↦ Stage C.l C.Qbar X.obj.left L)
      (fun X ↦ inferInstanceAs
        (Category (Stage C.l C.Qbar X.obj.left L)))
      (sixFunctorCoefficientRational D C coefficientStages E₀)
      (sixFunctorCoefficientRational D C coefficientStages L)
      (sixFunctorCoefficientTensor D C coefficientStages E₀)
      (sixFunctorCoefficientTensor D C coefficientStages L) Q
      ((sixFunctorCoefficientExchange D C coefficientStages E₀) Q)
      ((sixFunctorCoefficientExchange D C coefficientStages L) Q)
      (fun X ↦ (stageSystem C.l C.Qbar X.obj.left).T h) (coefficientTransition h)

  commonStageExchangeComparison : ∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D),
    @SixFunctorExchangeComparison D
      (fun X ↦ Stage C.l C.Qbar X.obj.left E₀)
      (fun X ↦ inferInstanceAs
        (Category (Stage C.l C.Qbar X.obj.left E₀)))
      (fun X ↦ generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
      (fun X ↦ inferInstanceAs
        (Category (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)))
      (sixFunctorCoefficientRational D C coefficientStages E₀) commonStage
      (sixFunctorCoefficientTensor D C coefficientStages E₀) commonStageTensor Q
      ((sixFunctorCoefficientExchange D C coefficientStages E₀) Q) (commonStageExchange Q)
      (fun X ↦ inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀)
      (commonStageComparison E₀)
  commonStageSupportValue : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
    [QuasiCompact f.hom.left] (hl : IsUnit (C.l : D.k))
    (c : Compactification f.hom.left)
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
    (K : sfIntegralConstructibleCategory C.l
      (Coefficient.{u} C.l C.Qbar E₀) X.obj.left),
    (commonStage.support f c).obj
        ((inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj
          ((sfRationalConstructibleLocalization C.l
            (Coefficient.{u} C.l C.Qbar E₀) X.obj.left).obj K)) =
      sfQbarCompactSupportValue C.l D.k hl C.Qbar c E₀ K
  commonStageModelNormalization : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    SixFunctorCoefficientModelNormalization (commonStageComparison E₀)
  commonStageUnit : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    commonStageDuality.unit ≅
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := Spec (.of D.k)) E₀).obj
        (sixFunctorCoefficientDuality D C coefficientStages E₀).unit

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The component equation identifying scalar transition followed by inclusion with
inclusion followed by the common-stage operation. Stating this equation for general
categories avoids unfolding coefficient-localization morphisms while checking it.
Source: common-stage coefficient conventions (blueprint: def-sf-operation-stages). -/
def SixFunctorInclusionCoherence
    {A₀ : Type v} {A₁ : Type v'} {B₀ : Type w} {B₁ : Type w'}
    {Ainf : Type hA} {Binf : Type hB}
    [Category.{hA'} A₀] [Category.{hA'} A₁]
    [Category.{hB'} B₀] [Category.{hB'} B₁]
    [Category.{hA'} Ainf] [Category.{hB'} Binf]
    (F : A₀ ⥤ B₀) (F' : A₁ ⥤ B₁) (G : Ainf ⥤ Binf)
    (c : A₀ ⥤ A₁) (d : B₀ ⥤ B₁)
    (U : A₀ ⥤ Ainf) (U' : A₁ ⥤ Ainf) (V : B₀ ⥤ Binf) (V' : B₁ ⥤ Binf)
    (α : F ⋙ d ≅ c ⋙ F') (u : c ⋙ U' ≅ U) (v : d ⋙ V' ≅ V)
    (γ : F ⋙ V ≅ U ⋙ G) (γ' : F' ⋙ V' ≅ U' ⋙ G) : Prop :=
  ∀ K : A₀, G.map (u.hom.app K) ≫ γ.inv.app K =
    γ'.inv.app (c.obj K) ≫ V'.map (α.inv.app K) ≫ v.hom.app (F.obj K)

/-- Identity, successive-extension, and inclusion coherence for the four operations.
The equations use the stage system's prescribed unitors, associators, and inclusions.
Source: common-stage coefficient conventions in clauses (1), (2), and (4)
(blueprint: def-sf-operation-stages). -/
def SixFunctorCommonStageCoherence {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) : Prop :=
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    ExchangeProjectionScalarCocycle
      (fun E₀ ↦ Stage C.l C.Qbar X.obj.left E₀)
      (fun E₀ ↦ Stage C.l C.Qbar Y.obj.left E₀)
      (fun E₀ ↦ (sixFunctorCoefficientRational D C A.coefficientStages E₀).direct f)
      (fun _ _ h ↦ (stageSystem C.l C.Qbar X.obj.left).T h)
      (fun _ _ h ↦ (stageSystem C.l C.Qbar Y.obj.left).T h)
      (sixFunctorStageUnitor D C X) (sixFunctorStageUnitor D C Y)
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar X.obj.left).assoc h h')
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Y.obj.left).assoc h h')
      (fun _ _ h ↦ ((A.coefficientTransition h).directAdjunction f).right)) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L),
    SixFunctorInclusionCoherence
      ((sixFunctorCoefficientRational D C A.coefficientStages E₀).direct f)
      ((sixFunctorCoefficientRational D C A.coefficientStages L).direct f) (A.commonStage.direct f)
      ((stageSystem C.l C.Qbar X.obj.left).T h)
      ((stageSystem C.l C.Qbar Y.obj.left).T h)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) L)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) L)
      (((A.coefficientTransition h).directAdjunction f).right)
      ((stageSystem C.l C.Qbar X.obj.left).transIso h)
      ((stageSystem C.l C.Qbar Y.obj.left).transIso h)
      (((A.commonStageComparison E₀).directAdjunction f).right)
      (((A.commonStageComparison L).directAdjunction f).right)) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    ExchangeProjectionScalarCocycle
      (fun E₀ ↦ Stage C.l C.Qbar Y.obj.left E₀)
      (fun E₀ ↦ Stage C.l C.Qbar X.obj.left E₀)
      (fun E₀ ↦ (sixFunctorCoefficientRational D C A.coefficientStages E₀).pull f)
      (fun _ _ h ↦ (stageSystem C.l C.Qbar Y.obj.left).T h)
      (fun _ _ h ↦ (stageSystem C.l C.Qbar X.obj.left).T h)
      (sixFunctorStageUnitor D C Y) (sixFunctorStageUnitor D C X)
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Y.obj.left).assoc h h')
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar X.obj.left).assoc h h')
      (fun _ _ h ↦ ((A.coefficientTransition h).directAdjunction f).left)) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L),
    SixFunctorInclusionCoherence
      ((sixFunctorCoefficientRational D C A.coefficientStages E₀).pull f)
      ((sixFunctorCoefficientRational D C A.coefficientStages L).pull f) (A.commonStage.pull f)
      ((stageSystem C.l C.Qbar Y.obj.left).T h)
      ((stageSystem C.l C.Qbar X.obj.left).T h)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) L)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) L)
      (((A.coefficientTransition h).directAdjunction f).left)
      ((stageSystem C.l C.Qbar Y.obj.left).transIso h)
      ((stageSystem C.l C.Qbar X.obj.left).transIso h)
      (((A.commonStageComparison E₀).directAdjunction f).left)
      (((A.commonStageComparison L).directAdjunction f).left)) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left),
    ExchangeProjectionScalarCocycle
      (fun E₀ ↦ Stage C.l C.Qbar X.obj.left E₀)
      (fun E₀ ↦ Stage C.l C.Qbar Y.obj.left E₀)
      (fun E₀ ↦ (sixFunctorCoefficientRational D C A.coefficientStages E₀).support f c)
      (fun _ _ h ↦ (stageSystem C.l C.Qbar X.obj.left).T h)
      (fun _ _ h ↦ (stageSystem C.l C.Qbar Y.obj.left).T h)
      (sixFunctorStageUnitor D C X) (sixFunctorStageUnitor D C Y)
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar X.obj.left).assoc h h')
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Y.obj.left).assoc h h')
      (fun _ _ h ↦ ((A.coefficientTransition h).supportAdjunction f c).left)) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L),
    SixFunctorInclusionCoherence
      ((sixFunctorCoefficientRational D C A.coefficientStages E₀).support f c)
      ((sixFunctorCoefficientRational D C A.coefficientStages L).support f c)
      (A.commonStage.support f c)
      ((stageSystem C.l C.Qbar X.obj.left).T h)
      ((stageSystem C.l C.Qbar Y.obj.left).T h)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) L)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) L)
      (((A.coefficientTransition h).supportAdjunction f c).left)
      ((stageSystem C.l C.Qbar X.obj.left).transIso h)
      ((stageSystem C.l C.Qbar Y.obj.left).transIso h)
      (((A.commonStageComparison E₀).supportAdjunction f c).left)
      (((A.commonStageComparison L).supportAdjunction f c).left)) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left),
    ExchangeProjectionScalarCocycle
      (fun E₀ ↦ Stage C.l C.Qbar Y.obj.left E₀)
      (fun E₀ ↦ Stage C.l C.Qbar X.obj.left E₀)
      (fun E₀ ↦ (sixFunctorCoefficientRational D C A.coefficientStages E₀).exceptional f c)
      (fun _ _ h ↦ (stageSystem C.l C.Qbar Y.obj.left).T h)
      (fun _ _ h ↦ (stageSystem C.l C.Qbar X.obj.left).T h)
      (sixFunctorStageUnitor D C Y) (sixFunctorStageUnitor D C X)
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Y.obj.left).assoc h h')
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar X.obj.left).assoc h h')
      (fun _ _ h ↦ ((A.coefficientTransition h).supportAdjunction f c).right)) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L),
    SixFunctorInclusionCoherence
      ((sixFunctorCoefficientRational D C A.coefficientStages E₀).exceptional f c)
      ((sixFunctorCoefficientRational D C A.coefficientStages L).exceptional f c)
      (A.commonStage.exceptional f c)
      ((stageSystem C.l C.Qbar Y.obj.left).T h)
      ((stageSystem C.l C.Qbar X.obj.left).T h)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) L)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) L)
      (((A.coefficientTransition h).supportAdjunction f c).right)
      ((stageSystem C.l C.Qbar Y.obj.left).transIso h)
      ((stageSystem C.l C.Qbar X.obj.left).transIso h)
      (((A.commonStageComparison E₀).supportAdjunction f c).right)
      (((A.commonStageComparison L).supportAdjunction f c).right))

/-- The finite-stage refinement comparison is the recorded witness from
`refinementComparisonIsomorphism`, specialized to the fixed finite-field and
positive quotient data. The operation datum normalizes its comparison components
against this witness; it does not introduce a second witness.
Source: the compactification-comparison paragraph of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-sf-mate/def-fix-six-functor-datum.md`, blueprint id
`def-fix-six-functor-datum`, clause (2)
(blueprint: def-sf-operation-stages). -/
noncomputable def sixFunctorFiniteRefinementComparison
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
    [QuasiCompact f.hom.left] (hl : IsUnit (C.l : D.k))
    {c d : Compactification f.hom.left}
    (r : c.Refinement d) (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left) :=
  refinementComparisonIsomorphism D.k C.l hl E n hn
    f.hom.left r O

/-- The fixed canonical coefficient realization at every positive quotient level.
Source: coefficient presentation in clause (1)
(blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteRealization (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) (X : SixFunctorSpace D) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  sfIntrinsicDerivedEquivalence X.obj.left (Padic.coefficientExtensionRing C.l E n)

/-- Realize a support value at its retained etale-origin witness. All three factors
are the operation realization, the retained input identification, and the recorded
constant-section/K-injective-normalized coefficient comparison.
Source: clause (2) (blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteWitnessSupport
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (F : sixFunctorFiniteCategory D C E n hn X ⥤ sixFunctorFiniteCategory D C E n hn Y)
    (ρ : F ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ≅
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
        sixFunctorFiniteSupport D C E n hn f c)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left)
    (w : (sixFunctorFiniteRealization D C E n hn X).functor.obj
        (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O) ≅ K.obj) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ρ.app K ≪≫ (sixFunctorFiniteSupport D C E n hn f c).mapIso w.symm ≪≫
    (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) c).app
      (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O)

/-- The recorded origin compositor with precisely the three supplied compactifications.
Source: proposition-composition-base-change-rf-shriek--1, witnessed composition
(blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteCompositionComparison
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  letI : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) := ⊥
  letI := discreteTopology_bot (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
  (rightDerivedLowerShriekOfCompactification A cg).map
      ((rightDerivedLowerShriekOfCompactification A cf).map
        (refinementFixedWitnessIso X.obj.left
          (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) O).inv) ≫
    coherenceProEtaleCompositor (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
      cf cg cfg O.2.L ≫
    (rightDerivedLowerShriekOfCompactification A cfg).map
      (refinementFixedWitnessIso X.obj.left
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) O).hom

/-- Realize a composite of two support operations at the retained input witness.
The factors are exactly the two operation realizations and the two canonical
fixed-scalar compact-support realizations; no composite endpoint is supplied.
Source: clause (2) (blueprint: def-sf-operation-stages). -/
def sixFunctorFiniteCompositeWitnessSupport
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (F : sixFunctorFiniteCategory D C E n hn X ⥤ sixFunctorFiniteCategory D C E n hn Y)
    (G : sixFunctorFiniteCategory D C E n hn Y ⥤ sixFunctorFiniteCategory D C E n hn Z)
    (ρ : F ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ≅
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
        sixFunctorFiniteSupport D C E n hn f cf)
    (σ : G ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι ≅
      (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ⋙
        sixFunctorFiniteSupport D C E n hn g cg)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left)
    (w : (sixFunctorFiniteRealization D C E n hn X).functor.obj
        (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O) ≅ K.obj) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  σ.app (F.obj K) ≪≫
    (sixFunctorFiniteSupport D C E n hn g cg).mapIso
      (sixFunctorFiniteWitnessSupport C E n hn f cf F ρ K O w) ≪≫
    (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) cg).app
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) cf).obj
          (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O))

/-- Identity open extension followed by direct image, with the canonical open unit.
Source: the proper identity compactification in clause (2)
(blueprint: def-sf-operation-stages). -/
def sixFunctorProperCandidateIso (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    sfIntrinsicCompactSupport (Compactification.ofIsProper f) A ≅
      proEtaleConstantDerivedDirectImage f A :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenId A X) ≪≫
      Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

/-- The canonical identity direct image is fixed by the inverse-image adjunction.
Source: the open identity compactification in clause (2)
(blueprint: def-sf-operation-stages). -/
def sixFunctorDirectIdentity (A : Type u) [CommRing A] [Finite A] (X : Scheme.{u}) :
    proEtaleConstantDerivedDirectImage (𝟙 X) A ≅ 𝟭 _ :=
  (((sfIntrinsicConstantModuleAdjunction (𝟙 X) A).mapDerivedCategoryRightDerivedAdjunction)
    |>.ofNatIsoLeft (Functor.mapDerivedCategoryNatIso (sfIntrinsicPullbackId A X) ≪≫
      Functor.mapDerivedCategoryIdIso _)).rightAdjointUniq Adjunction.id

/-- Open support is the same exact open extension, using the normalized identity image.
Source: clause (2) (blueprint: def-sf-operation-stages). -/
def sixFunctorOpenCandidateIso (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    sfIntrinsicCompactSupport (Compactification.ofIsOpenImmersion j) A ≅
      (sfIntrinsicExtensionByZero j A).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (sixFunctorDirectIdentity A Y) ≪≫ Functor.rightUnitor _

/-- Finite operations with their prescribed realization and normalization data.
Source: clauses (1)--(5) of def-fix-six-functor-datum
(blueprint: def-sf-operation-stages). -/
structure SixFunctorFiniteOperations
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) where
  finite : SixFunctorPushStage D (sixFunctorFiniteCategory D C E n hn)
  finiteDuality : SixFunctorDualityData finite (sixFunctorFiniteHomPairs D C E n hn)
  finitePullback : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    finite.pull f ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ≅
      (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ⋙
        sixFunctorFinitePullback D C E n hn f
  finiteDirectImage : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    finite.direct f ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ≅
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
        proEtaleConstantDerivedDirectImage f.hom.left (Padic.coefficientExtensionRing C.l E n)
  finiteSupport : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left),
    finite.support f c ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ≅
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
        sixFunctorFiniteSupport D C E n hn f c
  finiteExceptional : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left),
    finite.exceptional f c ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ≅
      (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ⋙
        sixFunctorFiniteExceptional D C E n hn f c
  finiteOpenExtension : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left),
    finite.openExtension j hj ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ≅
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
        sixFunctorFiniteOpen D C E n hn j hj
  /-- Both finite adjunctions retain the canonical ordinary-unit normalization. -/
  finiteDirectAdjunctionNormalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    ∃ a : ExchangeProjectionAdjunctionComparison (finite.pullDirectAdjunction f)
      ((@sfIntrinsicConstantModuleAdjunction X.obj.left Y.obj.left f.hom.left
        (Padic.coefficientExtensionRing C.l E n) _
        (Padic.finite_coefficientExtensionRing C.l E n hn)).mapDerivedCategoryRightDerivedAdjunction
        )
      (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι,
      a.left = finitePullback f ∧ a.right = finiteDirectImage f
  finiteOpenAdjunctionNormalization : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left),
    ∃ a : ExchangeProjectionAdjunctionComparison (finite.openAdjunction j hj)
      (@exceptionalOpenAdjunction X.obj.left Y.obj.left j.hom.left hj
        (Padic.coefficientExtensionRing C.l E n) _
        (Padic.finite_coefficientExtensionRing C.l E n hn))
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
      (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι,
      a.left = finiteOpenExtension j hj ∧ a.right = finitePullback j
  /-- Pullback composition uses the canonical section-normalized comparison. -/
  finitePullCompositionNormalization : ∀ {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (K : sixFunctorFiniteCategory D C E n hn Z),
    (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.map
        ((finite.pullComposition f g).hom.app K) ≫
      (finitePullback f).hom.app ((finite.pull g).obj K) ≫
      (sixFunctorFinitePullback D C E n hn f).map ((finitePullback g).hom.app K) =
    (finitePullback (f ≫ g)).hom.app K ≫
      (@sfIntrinsicDerivedPullbackComp (Padic.coefficientExtensionRing C.l E n) _
        (Padic.finite_coefficientExtensionRing C.l E n hn)
        X.obj.left Y.obj.left Z.obj.left f.hom.left g.hom.left).hom.app K.obj
  /-- Refinement comparisons are the recorded proper-composition/proper-open maps,
  conjugated by the actual realization and the retained witness. -/
  finiteRefinementNormalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
    [QuasiCompact f.hom.left] (hl : IsUnit (C.l : D.k))
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left)
    (w : (sixFunctorFiniteRealization D C E n hn X).functor.obj
        (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O) ≅ K.obj),
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.mapIso
        ((finite.comparison f c d).app K) ≪≫
      sixFunctorFiniteWitnessSupport C E n hn f d (finite.support f d)
        (finiteSupport f d) K O w =
      sixFunctorFiniteWitnessSupport C E n hn f c (finite.support f c)
        (finiteSupport f c) K O w ≪≫
      (sixFunctorFiniteRealization D C E n hn Y).functor.mapIso
          (sixFunctorFiniteRefinementComparison C E n hn f hl r O)
  /-- The composition law is the inverse of the recorded origin compositor,
  conjugated by the two operation realizations at the same retained witness. -/
  finiteCompositionNormalization : ∀ {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left)
    (w : (sixFunctorFiniteRealization D C E n hn X).functor.obj
        (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O) ≅ K.obj),
    (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι.map
        ((finite.composition f g cf cg cfg).inv.app K) ≫
      (sixFunctorFiniteWitnessSupport C E n hn (f ≫ g) cfg (finite.support (f ≫ g) cfg)
        (finiteSupport (f ≫ g) cfg) K O w).hom =
      (sixFunctorFiniteCompositeWitnessSupport C E n hn f g cf cg
        (finite.support f cf) (finite.support g cg)
        (finiteSupport f cf) (finiteSupport g cg) K O w).hom ≫
      (sixFunctorFiniteRealization D C E n hn Z).functor.map
        (sixFunctorFiniteCompositionComparison C E n hn f g cf cg cfg O)
  /-- The proper comparison uses the identity open compactification and its unit. -/
  finiteProperNormalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left] (K : sixFunctorFiniteCategory D C E n hn X),
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.mapIso
        ((finite.properIdentity f).app K) ≪≫ (finiteDirectImage f).app K =
      (finiteSupport f (.ofIsProper f.hom.left)).app K ≪≫
        (@sixFunctorProperCandidateIso (Padic.coefficientExtensionRing C.l E n) _
          (Padic.finite_coefficientExtensionRing C.l E n hn) X.obj.left Y.obj.left
          f.hom.left _).app K.obj
  /-- The open comparison cancels the identity proper image, canonically. -/
  finiteOpenNormalization : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) (K : sixFunctorFiniteCategory D C E n hn X),
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.mapIso
        ((finite.openIdentification j hj).app K) ≪≫ (finiteOpenExtension j hj).app K =
      (finiteSupport j (sixFunctorOpenCompactification j hj)).app K ≪≫
        (@sixFunctorOpenCandidateIso (Padic.coefficientExtensionRing C.l E n) _
          (Padic.finite_coefficientExtensionRing C.l E n hn) X.obj.left Y.obj.left
          j.hom.left hj).app K.obj
  /-- The finite tensor used by the exchange stage is defined on the finite-Tor
  domain.  Its underlying ambient operation is the recorded
  `finiteIntrinsicDerivedTensor`; there is no free tensor on all bounded
  constructible objects. -/
  finiteTensorDomainStage : ∀ X : SixFunctorSpace D,
    finiteTorConstructibleCategory C.l E n hn X.obj.left ⥤
      finiteTorConstructibleCategory C.l E n hn X.obj.left ⥤
        finiteTorConstructibleCategory C.l E n hn X.obj.left
  /-- On finite-Tor inputs the domain tensor is identified with the ambient
  `finiteIntrinsicDerivedTensor`, including its morphism action. -/
  finiteTensorNormalization : ∀ (X : SixFunctorSpace D)
    (K L : finiteTorConstructibleCategory C.l E n hn X.obj.left),
    (finiteTorConstructible C.l E n hn X.obj.left).ι.obj
        (((finiteTensorDomainStage X).obj K).obj L) =
      (sixFunctorFiniteTensor D C E n hn X).obj
        ((finiteTorConstructible C.l E n hn X.obj.left).ι.obj K,
          (finiteTorConstructible C.l E n hn X.obj.left).ι.obj L)
  finiteTensorNormalization_map : ∀ (X : SixFunctorSpace D)
    {K K' L L' : finiteTorConstructibleCategory C.l E n hn X.obj.left}
    (f : K ⟶ K') (g : L ⟶ L'),
    HEq ((sixFunctorFiniteTensor D C E n hn X).map
      (Prod.mkHom ((finiteTorConstructible C.l E n hn X.obj.left).ι.map f)
        ((finiteTorConstructible C.l E n hn X.obj.left).ι.map g)))
      ((finiteTorConstructible C.l E n hn X.obj.left).ι.map
        ((Functor.uncurry.obj (finiteTensorDomainStage X)).map (Prod.mkHom f g)))
  finiteUnit : finiteDuality.unit.obj ≅
    DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (proEtaleConstantModule (Spec (.of D.k)) (Padic.coefficientExtensionRing C.l E n)))

/-- The actual derived quotient reduction restricted to integral constructible objects.
Membership is the corresponding clause of the integral predicate, not a new assumption.
Source: integral coefficient convention, positive exponent m+1
(blueprint: def-sf-operation-stages). -/
def sixFunctorIntegralReduction (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ) (X : SixFunctorSpace D) :
    sfIntegralConstructibleCategory C.l E X.obj.left ⥤
      sixFunctorFiniteCategory D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) X :=
  (intrinsicFiniteTorsionConstructible C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left).lift
    ((sfIntegralConstructible C.l E X.obj.left).ι ⋙
      scalarReductionDerivedExtension C.l E X.obj.left m)
    (fun K ↦ K.property.2.choose_spec.choose_spec.2 m |>.1)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Quotient reduction on a good representative, fixed by the derived scalar counit.
Source: Stacks 06YY, integral reduction construction
(blueprint: def-sf-operation-stages). -/
def sixFunctorIntegralReductionModel
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ) (Y : SixFunctorSpace D)
    (K : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (P : (integralOperationsGoodComplex C.l E Y.obj.left).FullSubcategory)
    (e : (integralOperationsGoodLocalization C.l E Y.obj.left).obj P ≅ K.obj) :=
  (scalarReductionDerivedExtension C.l E Y.obj.left m).mapIso e.symm ≪≫
    unrestrictedTowerResolutionIso C.l E Y.obj.left m (𝟙 P.obj)
      ⟨inferInstance, P.property.1⟩

/-- The finite pullback presentation is the unique comparison preserving its adjunction.
Source: Stacks 03D2, canonical constant-section inverse image
(blueprint: def-sf-operation-stages). -/
def sixFunctorFinitePullbackModel
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionTarget C.l E Y.obj.left m) ℤ) :=
  let α := (coefficientProEtaleModuleAdjunction.{u, u} f.hom.left
      (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing C.l E (m + 1))))).leftAdjointUniq
      (sfIntrinsicConstantModuleAdjunction f.hom.left
        (Padic.coefficientExtensionRing C.l E (m + 1)))
  letI := integralOperationsLevelPullback_additive.{u, u} C.l E f.hom.left m
  letI : (coefficientProEtaleModulePullback.{u, u} f.hom.left
      (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))))).PreservesZeroMorphisms :=
    inferInstanceAs
      ((integralOperationsLevelPullback.{u, u} C.l E f.hom.left m).PreservesZeroMorphisms)
  (sfIntrinsicPullback (Padic.coefficientExtensionRing C.l E (m + 1)) f.hom.left
      ).mapDerivedCategoryFactors.hom.app P ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α.symm (.up ℤ)).hom.app P)

/-- Reduction of exact completed open extension is its canonical scalar-adjunction mate.
Source: Stacks 03DI and 0E8I, open coefficient-change construction
(blueprint: def-sf-operation-stages). -/
def sixFunctorIntegralOpenReduction
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (j : X ⟶ Y) (hj : IsOpenImmersion j.hom.left)
    (K : DerivedCategory (scalarReductionSource C.l E X.obj.left)) :=
  letI := hj
  letI := (sfIntrinsicExtensionByZero_exact j.hom.left
    (Padic.coefficientExtensionRing C.l E (m + 1))).1
  letI := (sfIntrinsicExtensionByZero_exact j.hom.left
    (Padic.coefficientExtensionRing C.l E (m + 1))).2.1
  letI := (sfIntrinsicExtensionByZero_exact j.hom.left
    (Padic.coefficientExtensionRing C.l E (m + 1))).2.2
  (PurCompactSupport.finiteReductionIso C.l E Y.obj.left m).inv.app
      (((PurCompactSupport.openExtension (PurCompactSupport.completed C.l E)
        j.hom.left).mapDerivedCategory).obj K) ≫
    (PurCompactSupport.openComparison
      (PurCompactSupport.reduction C.l E (m + 1) (Nat.le_add_left 1 m)) j.hom.left).app K ≫
    (Functor.mapDerivedCategoryNatIso
      (PurCompactSupport.finiteOpenIso C.l E m j.hom.left)).hom.app _ ≫
    (sixFunctorFiniteOpen D C E (m + 1) (Nat.le_add_left 1 m) j hj).map
      ((PurCompactSupport.finiteReductionIso C.l E X.obj.left m).hom.app K)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Reduction of integral construction maps to every normalized finite stage.
The support comparison is the adjunct of the chosen Roos projection (hence of the
projection retained in supportConstruction), and the direct comparison is the
adjunct of its recorded direct-image projection. The coefficient comparison record
imposes the refinement, composition, proper, open, unit and counit equations on
these very maps. Rationalization then carries these same equations to rational
coefficients. Source: clauses (1)--(4), derived-limit and scalar-extension conventions
(blueprint: def-sf-operation-stages). -/
structure SixFunctorIntegralNormalization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (S : SixFunctorHigherOperations D C E) where
  finiteLevels : ∀ m : ℕ,
    SixFunctorFiniteOperations D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  reduction : ∀ m : ℕ, SixFunctorCoefficientComparison S.integral (finiteLevels m).finite
    (sixFunctorIntegralReduction D C E m)
  supportProjection : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (hl : IsUnit (C.l : D.k)) (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ),
    HEq
      ((intrinsicFiniteTorsionConstructible C.l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) Y.obj.left).ι.map
          (((reduction m).supportAdjunction f c).left.hom.app K) ≫
        ((finiteLevels m).finiteSupport f c).hom.app
          ((sixFunctorIntegralReduction D C E m X).obj K))
      ((scalarReductionDerivedExtension C.l E Y.obj.left m).map
          ((sfIntegralConstructible C.l E Y.obj.left).ι.map
            (eqToHom ((S.supportConstruction f hl c).choose_spec.2.2.1 K))) ≫
        sfCompactSupportChosenReduction C.l D.k hl c E K m)
  /-- Pullback reduction is the fixed projection of the K-flat Roos construction. -/
  pullProjection : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)]
    (K : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (P : (integralOperationsGoodComplex C.l E Y.obj.left).FullSubcategory)
    (e : (integralOperationsGoodLocalization C.l E Y.obj.left).obj P ≅ K.obj) (m : ℕ),
    HEq
      ((intrinsicFiniteTorsionConstructible C.l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left).ι.map
          (((reduction m).directAdjunction f).left.hom.app K) ≫
        ((finiteLevels m).finitePullback f).hom.app
          ((sixFunctorIntegralReduction D C E m Y).obj K) ≫
        (sixFunctorFinitePullback D C E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) f).map
          (sixFunctorIntegralReductionModel C E m Y K P e).hom ≫
        sixFunctorFinitePullbackModel C E m f
          (unrestrictedTowerFiniteComplex C.l E Y.obj.left m P.obj))
      ((scalarReductionDerivedExtension C.l E X.obj.left m).map
          (eqToHom (congrArg (fun F ↦ (F.obj K).obj) (S.integralPullback f))) ≫
        integralPullbackFiniteComparison C.l E f.hom.left K.obj P e m)
  /-- Open extension has its exact completed-ring realization. -/
  openRealization : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left),
    S.integral.openExtension j hj ⋙ (sfIntegralConstructible C.l E Y.obj.left).ι ≅
      (sfIntegralConstructible C.l E X.obj.left).ι ⋙
        (@PurCompactSupport.openExtension (PurCompactSupport.completed C.l E)
          X.obj.left Y.obj.left j.hom.left hj).mapDerivedCategory
  /-- Its reduction comparison is the canonical open-unit scalar mate. -/
  openProjection : ∀ {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ),
    HEq
      ((intrinsicFiniteTorsionConstructible C.l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) Y.obj.left).ι.map
          (((reduction m).openExtension j hj).hom.app K) ≫
        ((finiteLevels m).finiteOpenExtension j hj).hom.app
          ((sixFunctorIntegralReduction D C E m X).obj K))
      ((scalarReductionDerivedExtension C.l E Y.obj.left m).map
          ((openRealization j hj).hom.app K) ≫
        sixFunctorIntegralOpenReduction C E m j hj K.obj)
  directProjection : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    [HasProduct (sfDirectImageTerm C.l E f.hom.left K.obj)] (m : ℕ),
    HEq
      ((intrinsicFiniteTorsionConstructible C.l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) Y.obj.left).ι.map
          (((reduction m).directAdjunction f).right.hom.app K) ≫
        ((finiteLevels m).finiteDirectImage f).hom.app
          ((sixFunctorIntegralReduction D C E m X).obj K))
      ((scalarReductionDerivedExtension C.l E Y.obj.left m).map
          (eqToHom (S.integralDirectLimitObject f K).symm) ≫
        sfDirectImageReductionComparison C.l E f.hom.left (S.integralDirectLimit f K) m)

end WeilConjectures
