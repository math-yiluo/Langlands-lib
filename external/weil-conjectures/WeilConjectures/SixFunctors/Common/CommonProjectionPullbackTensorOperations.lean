/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonProjectionTensorComparison
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # Supplied tensor and pullback operations and their compatibility square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option Elab.async false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.style.haveILetI false

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

/-- The equation for one pair of inputs in a tensor comparison square.
Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: def-sf-projection-pullback-tensor-operations).
This is the expanded equation defining comparison compatibility, without its
universal quantifiers over the two inputs. -/
@[reducible] def projectionTensorComparisonComponent
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (I : A ⥤ A') (J : B ⥤ B')
    {F : A ⥤ B} {G : A' ⥤ B'}
    {TA : A ⥤ A ⥤ A} {TB : B ⥤ B ⥤ B}
    {TA' : A' ⥤ A' ⥤ A'} {TB' : B' ⥤ B' ⥤ B'}
    (φ : (Functor.postcompose₂.obj F).obj TA ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj TB)
    (ψ : (Functor.postcompose₂.obj G).obj TA' ⟶
      (((Functor.whiskeringLeft₂ _).obj G).obj G).obj TB')
    (a : F ⋙ J ≅ I ⋙ G)
    (mA : (Functor.postcompose₂.obj I).obj TA ≅
      (((Functor.whiskeringLeft₂ _).obj I).obj I).obj TA')
    (mB : (Functor.postcompose₂.obj J).obj TB ≅
      (((Functor.whiskeringLeft₂ _).obj J).obj J).obj TB')
    (M N : A) : Prop :=
  J.map ((φ.app M).app N) ≫ (mB.hom.app (F.obj M)).app (F.obj N) =
    a.hom.app ((TA.obj M).obj N) ≫ G.map ((mA.hom.app M).app N) ≫
      ((ψ.app (I.obj M)).app (I.obj N)) ≫
      (TB'.map (a.inv.app M)).app (G.obj (I.obj N)) ≫
      (TB'.obj (J.obj (F.obj M))).map (a.inv.app N)

/-- Transport a tensor/pullback comparison along the recorded functor equalities.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: def-sf-projection-pullback-tensor-operations). -/
def projectionTransportTensorComparison
    {A B : Type*} [Category* A] [Category* B]
    {F F' : A ⥤ B} {T T' : B ⥤ B ⥤ B} {U U' : A ⥤ A ⥤ A}
    (hF : F = F') (hT : T = T') (hU : U = U')
    (φ : (Functor.postcompose₂.obj F).obj U ≅
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T) :
    (Functor.postcompose₂.obj F').obj U' ≅
      (((Functor.whiskeringLeft₂ B).obj F').obj F').obj T' := by
  subst F'
  subst T'
  subst U'
  exact φ

/-- The supplied tensor/pullback comparison in the named operation coordinates.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: def-sf-projection-pullback-tensor-operations). -/
@[irreducible] def projectionPullbackTensor
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q) :
    (Functor.postcompose₂.obj (S.pull Q.p)).obj (T Q.Y) ≅
      (((Functor.whiskeringLeft₂ (B Q.Z)).obj (S.pull Q.p)).obj
        (S.pull Q.p)).obj (T Q.Z) :=
  projectionTransportTensorComparison A.properPull A.tensorBar A.tensorY A.stage.tensorPullback

/-- The curried version of an uncurried natural tensor comparison.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: def-sf-projection-pullback-tensor-operations). -/
@[irreducible] def projectionCurriedTensorComparison
    {A B : Type*} [Category* A] [Category* B]
    (V : A ⥤ B) (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B)
    (t : Functor.uncurry.obj T ⋙ V ≅ V.prod V ⋙ Functor.uncurry.obj T') :
    (Functor.postcompose₂.obj V).obj T ≅
      (((Functor.whiskeringLeft₂ B).obj V).obj V).obj T' :=
  NatIso.ofComponents (fun a ↦ NatIso.ofComponents (fun b ↦ t.app (a, b)) (by
    intro b b' f
    simpa using t.hom.naturality (Prod.mkHom (𝟙 a) f))) (by
      intro a a' f
      ext b
      simpa using t.hom.naturality (Prod.mkHom f (𝟙 b)))

/-- The pullback/tensor square, with all its operation data supplied explicitly.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: def-sf-projection-pullback-tensor-operations). -/
@[irreducible] def projectionTensorComparisonCompatible
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category* (B X)]
    {B' : SixFunctorSpace D → Type*} [∀ X, Category* (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q) : Prop :=
  Adjunction.ComparisonCompatible (C.directAdjunction Q.p).left.symm
    (projectionPullbackTensor A).hom (projectionPullbackTensor A').hom
    (projectionCurriedTensorComparison (V Q.Z) (T Q.Z) (T' Q.Z) (t Q.Z))
    (projectionCurriedTensorComparison (V Q.Y) (T Q.Y) (T' Q.Y) (t Q.Y))

end WeilConjectures
