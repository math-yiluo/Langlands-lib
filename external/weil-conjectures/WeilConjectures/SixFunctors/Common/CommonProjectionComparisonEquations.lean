/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionCoherence
import Mathlib.Tactic.Convert
import WeilConjectures.SixFunctors.Common.CommonProjectionCompactificationOnStage
import WeilConjectures.SixFunctors.Common.CommonProjectionCompositionOnStage
import WeilConjectures.SixFunctors.Common.CommonProjectionProperOnStage

/-! # Compact-support projection comparison equations

Source: the coherence paragraph of the projection-formula proof in
literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done.
(blueprint: lem-sf-common-projection-comparison-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

section PentagonTransport
universe v w v' w'
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
  {V : ∀ X, B X ⥤ B' X}

private theorem coefficient_pentagon (C : SixFunctorCoefficientComparison S S' V)
    {X Y Z W : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : B X)
    (hp : HEq ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
        (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K))
      ((S.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K))) :
    HEq ((S'.composition (f ≫ g) h cfg ch cfgh).hom.app ((V X).obj K) ≫
      (S'.support h ch).map ((S'.composition f g cf cg cfg).hom.app ((V X).obj K)))
      ((S'.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app ((V X).obj K) ≫
        (S'.composition g h cg ch cgh).hom.app
          ((S'.support f cf).obj ((V X).obj K))) := by
  apply heq_of_eq
  apply (cancel_epi ((C.supportAdjunction ((f ≫ g) ≫ h) cfgh).left.hom.app K)).mp
  let e := (C.supportAdjunction h ch).left.hom.app
      ((S.support g cg).obj ((S.support f cf).obj K)) ≫
    (S'.support h ch).map ((C.supportAdjunction g cg).left.hom.app
      ((S.support f cf).obj K)) ≫
    (S'.support h ch).map ((S'.support g cg).map
      ((C.supportAdjunction f cf).left.hom.app K))
  have hl : (V W).map
      ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
        (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K)) ≫ e =
      (C.supportAdjunction ((f ≫ g) ≫ h) cfgh).left.hom.app K ≫
        (S'.composition (f ≫ g) h cfg ch cfgh).hom.app ((V X).obj K) ≫
        (S'.support h ch).map
          ((S'.composition f g cf cg cfg).hom.app ((V X).obj K)) := by
    dsimp only [e]
    simp only [Functor.map_comp, Category.assoc]
    erw [(C.supportAdjunction h ch).left.hom.naturality_assoc]
    simp only [Functor.comp_map]
    have hc := congrArg (S'.support h ch).map (C.composition f g cf cg cfg K)
    simp only [Functor.map_comp] at hc
    erw [hc]
    erw [reassoc_of% C.composition (f ≫ g) h cfg ch cfgh K]
  have hr : (V W).map
      ((S.composition f (g ≫ h) cf cgh cfgh).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K)) ≫ e =
      (C.supportAdjunction ((f ≫ g) ≫ h) cfgh).left.hom.app K ≫
        (S'.composition f (g ≫ h) cf cgh cfgh).hom.app ((V X).obj K) ≫
        (S'.composition g h cg ch cgh).hom.app
          ((S'.support f cf).obj ((V X).obj K)) := by
    dsimp only [e]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% C.composition g h cg ch cgh ((S.support f cf).obj K)]
    erw [← (S'.composition g h cg ch cgh).hom.naturality]
    erw [reassoc_of% C.composition f (g ≫ h) cf cgh cfgh K]
    rfl
  have hh := congrArg (fun a ↦ (V W).map a ≫ e) (eq_of_heq hp)
  convert hl.symm.trans (hh.trans hr) using 1 <;> rfl

end PentagonTransport

section Naturality
universe v w
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {P : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
  {Q : SixFunctorCompactifiedSquare D}

private theorem projection_natural (A : SixFunctorExchangeData P T Q)
    (K K' : B Q.X) (L L' : B Q.Y) (a : K ⟶ K') (b : L ⟶ L') :
    ((T Q.Y).map ((P.support Q.f Q.compactification).map a)).app L ≫
        ((T Q.Y).obj ((P.support Q.f Q.compactification).obj K')).map b ≫
        A.projectionComponent K' L' =
      A.projectionComponent K L ≫ (P.support Q.f Q.compactification).map
        (((T Q.X).map a).app ((P.pull Q.f).obj L) ≫
          ((T Q.X).obj K').map ((P.pull Q.f).map b)) := by
  let η := Functor.uncurry.map A.stage.projection
  have hs : (P.support Q.f Q.compactification).prod (𝟭 (B Q.Y)) ⋙
      Functor.uncurry.obj (T Q.Y) =
      Functor.uncurry.obj (A.stage.compactSupport ⋙ A.stage.tensorY) := by
    simp only [← A.tensorY, ← A.compactSupport]
    rfl
  have ht : ((𝟭 (B Q.X)).prod (P.pull Q.f) ⋙ Functor.uncurry.obj (T Q.X)) ⋙
      P.support Q.f Q.compactification = Functor.uncurry.obj
        ((Functor.postcompose₂.obj A.stage.compactSupport).obj
          ((((Functor.whiskeringLeft₂ (B Q.X)).obj (𝟭 (B Q.X))).obj
            A.stage.pull).obj A.stage.tensorX)) := by
    simp only [← A.tensorX, ← A.compactSupport, ← A.pull]
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro M
      rfl
    intro M M' f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    dsimp
    exact A.stage.compactSupport.map_comp _ _
  let η' := (eqToHom hs) ≫ η ≫ (eqToHom ht.symm)
  have hc : ∀ K L, η'.app (K, L) = A.projectionComponent K L := by
    intro K L
    simp only [η', NatTrans.comp_app, eqToHom_app, η, Functor.uncurry_map_app,
      SixFunctorExchangeData.projectionComponent]
  simpa only [hc, Functor.comp_map, Functor.prod_map, Functor.id_map,
    Functor.uncurry_obj_map, Functor.prod_obj, Functor.id_obj, Category.assoc]
    using η'.naturality (Prod.mkHom a b)

private def projectionTransformation
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (P.support f c).prod (𝟭 (B Y)) ⋙ Functor.uncurry.obj (T Y) ⟶
      ((𝟭 (B X)).prod (P.pull f) ⋙ Functor.uncurry.obj (T X)) ⋙ P.support f c where
  app M := compactSupportProjectionComponent A f c M.1 M.2
  naturality {M N} v := by
    simp only [Functor.comp_map, Functor.prod_map, Functor.id_map,
      Functor.uncurry_obj_map, Functor.prod_obj, Functor.id_obj, Category.assoc]
    convert projection_natural (A (compactSupportProjectionSquare f c))
      M.1 N.1 M.2 N.2 v.1 v.2 using 1 <;> rfl

private def properProjectionTransformationAtSquare
    (a : SixFunctorExchangeData P T Q) :
    (P.direct Q.p).prod (𝟭 (B Q.Y)) ⋙ Functor.uncurry.obj (T Q.Y) ⟶
      ((𝟭 (B Q.Z)).prod (P.pull Q.p) ⋙ Functor.uncurry.obj (T Q.Z)) ⋙ P.direct Q.p := by
  let η := Functor.uncurry.map
    (a.stage.properAdjunction.rightAdjointProjectionMap a.stage.tensorPullback.hom)
  have hs : (P.direct Q.p).prod (𝟭 (B Q.Y)) ⋙ Functor.uncurry.obj (T Q.Y) =
      Functor.uncurry.obj (a.stage.properPush ⋙ a.stage.tensorY) := by
    simp only [← a.tensorY, ← a.properPush]
    rfl
  have ht : ((𝟭 (B Q.Z)).prod (P.pull Q.p) ⋙ Functor.uncurry.obj (T Q.Z)) ⋙ P.direct Q.p =
      Functor.uncurry.obj ((Functor.postcompose₂.obj a.stage.properPush).obj
        ((((Functor.whiskeringLeft₂ (B Q.Z)).obj (𝟭 (B Q.Z))).obj
          a.stage.properPull).obj a.stage.tensorBar)) := by
    simp only [← a.tensorBar, ← a.properPush, ← a.properPull]
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro M
      rfl
    intro M M' v
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    dsimp
    exact a.stage.properPush.map_comp _ _
  exact eqToHom hs ≫ η ≫ eqToHom ht.symm

private def properProjectionTransformation
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left] :
    (P.direct f).prod (𝟭 (B Y)) ⋙ Functor.uncurry.obj (T Y) ⟶
      ((𝟭 (B X)).prod (P.pull f) ⋙ Functor.uncurry.obj (T X)) ⋙ P.direct f :=
  properProjectionTransformationAtSquare (A (compactSupportProperSquare f))

private def properProjectionComponentAtSquare (a : SixFunctorExchangeData P T Q)
    (K : B Q.Z) (L : B Q.Y) :
    ((T Q.Y).obj ((P.direct Q.p).obj K)).obj L ⟶
      (P.direct Q.p).obj (((T Q.Z).obj K).obj ((P.pull Q.p).obj L)) :=
  eqToHom (by rw [a.tensorY, a.properPush]; rfl) ≫
    ((a.stage.properAdjunction.rightAdjointProjectionMap
      a.stage.tensorPullback.hom).app K).app L ≫
    eqToHom (by rw [a.tensorBar, a.properPush, a.properPull]; rfl)

private theorem properProjectionAtSquare_app (a : SixFunctorExchangeData P T Q)
    (K : B Q.Z) (L : B Q.Y) :
    (properProjectionTransformationAtSquare a).app (K, L) =
      properProjectionComponentAtSquare a K L := by
  simp only [properProjectionTransformationAtSquare, NatTrans.comp_app, eqToHom_app,
    Functor.uncurry_map_app, properProjectionComponentAtSquare]

private theorem properProjectionTransformation_app
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left] (K : B X) (L : B Y) :
    (properProjectionTransformation A f).app (K, L) =
      compactSupportProperProjection A f K L := by
  convert properProjectionAtSquare_app (A (compactSupportProperSquare f)) K L using 1 <;> rfl

private def compactificationLeft
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) :=
  Functor.whiskerRight
        ((P.comparison f c d).hom.prod (𝟙 (𝟭 _))) (Functor.uncurry.obj (T Y)) ≫
      projectionTransformation A f d

private def compactificationRight
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) :=
  projectionTransformation A f c ≫
      Functor.whiskerLeft ((𝟭 _).prod (P.pull f) ⋙ Functor.uncurry.obj (T X))
        (P.comparison f c d).hom

private theorem compactificationLeft_app
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) (K : B X) (L : B Y) :
    (compactificationLeft A f c d).app (K, L) =
      ((T Y).map ((P.comparison f c d).hom.app K)).app L ≫
          compactSupportProjectionComponent A f d K L := by
  simp only [compactificationLeft, NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.prod,
    NatTrans.id_app, Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.comp_obj,
    Functor.prod_obj, Functor.id_obj, projectionTransformation, Category.assoc]
  erw [((T Y).obj ((P.support f d).obj K)).map_id L]
  simp only [Category.id_comp]

private theorem compactificationRight_app
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) (K : B X) (L : B Y) :
    (compactificationRight A f c d).app (K, L) =
      compactSupportProjectionComponent A f c K L ≫
          (P.comparison f c d).hom.app (((T X).obj K).obj ((P.pull f).obj L)) := by
  simp only [compactificationRight, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.uncurry_obj_obj, Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    projectionTransformation]

private def compositionLeft
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) :=
  Functor.whiskerRight
        ((P.composition f g cf cg cfg).hom.prod (𝟙 (𝟭 _)))
        (Functor.uncurry.obj (T Z)) ≫
      Functor.whiskerLeft ((P.support f cf).prod (𝟭 _))
        (projectionTransformation A g cg) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft ((𝟭 _).prod (P.pull g))
          (projectionTransformation A f cf)) (P.support g cg)

private def compositionRight
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) :=
  projectionTransformation A (f ≫ g) cfg ≫
      Functor.whiskerLeft ((𝟭 _).prod (P.pull (f ≫ g)) ⋙ Functor.uncurry.obj (T X))
        (P.composition f g cf cg cfg).hom ≫
      Functor.whiskerRight
        (Functor.whiskerRight
          (Functor.whiskerRight
            (NatTrans.prod
              (𝟙 (𝟭 (B X)))
              (P.pullComposition f g).hom) (Functor.uncurry.obj (T X)))
          (P.support f cf)) (P.support g cg)

private theorem compositionLeft_app
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z) :
    (compositionLeft A f g cf cg cfg).app (K, L) =
      ((T Z).map ((P.composition f g cf cg cfg).hom.app K)).app L ≫
          compactSupportProjectionComponent A g cg ((P.support f cf).obj K) L ≫
          (P.support g cg).map
            (compactSupportProjectionComponent A f cf K ((P.pull g).obj L)) := by
  simp only [compositionLeft, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.prod, NatTrans.id_app, Functor.uncurry_obj_map,
    Functor.uncurry_obj_obj, Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    projectionTransformation, Category.assoc]
  erw [((T Z).obj ((P.support g cg).obj ((P.support f cf).obj K))).map_id L]
  simp only [Category.id_comp]

private theorem compositionRight_app
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z) :
    (compositionRight A f g cf cg cfg).app (K, L) =
      compactSupportProjectionComponent A (f ≫ g) cfg K L ≫
          (P.composition f g cf cg cfg).hom.app
            (((T X).obj K).obj ((P.pull (f ≫ g)).obj L)) ≫
          (P.support g cg).map ((P.support f cf).map
            (((T X).obj K).map ((P.pullComposition f g).hom.app L))) := by
  simp only [compositionRight, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.prod, NatTrans.id_app, Functor.uncurry_obj_map,
    Functor.uncurry_obj_obj, Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    projectionTransformation]
  erw [(T X).map_id K]
  simp only [NatTrans.id_app, Category.id_comp]

private def properLeft
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) :=
  Functor.whiskerRight
        ((P.properIdentification f c).hom.prod (𝟙 (𝟭 _))) (Functor.uncurry.obj (T Y)) ≫
      properProjectionTransformation A f

private def properRight
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) :=
  projectionTransformation A f c ≫
      Functor.whiskerLeft ((𝟭 _).prod (P.pull f) ⋙ Functor.uncurry.obj (T X))
        (P.properIdentification f c).hom

private theorem properLeft_app
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : B X) (L : B Y) :
    (properLeft A f c).app (K, L) =
      ((T Y).map ((P.properIdentification f c).hom.app K)).app L ≫
          compactSupportProperProjection A f K L := by
  simp only [properLeft, NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.prod,
    NatTrans.id_app, Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.comp_obj,
    Functor.prod_obj, Functor.id_obj, properProjectionTransformation_app, Category.assoc]
  erw [((T Y).obj ((P.direct f).obj K)).map_id L]
  simp only [Category.id_comp]

private theorem properRight_app
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : B X) (L : B Y) :
    (properRight A f c).app (K, L) =
      compactSupportProjectionComponent A f c K L ≫
          (P.properIdentification f c).hom.app
            (((T X).obj K).obj ((P.pull f).obj L)) := by
  simp only [properRight, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.uncurry_obj_obj,
    Functor.comp_obj, Functor.prod_obj, Functor.id_obj, projectionTransformation]

private theorem component_eq_of_iso {A₀ : Type*} [Category* A₀]
    {B₀ : Type*} [Category* B₀] {F G : A₀ ⥤ B₀} (a b : F ⟶ G)
    {M N : A₀} (e : M ≅ N) (hn : a.app N = b.app N) : a.app M = b.app M := by
  apply (cancel_mono (G.map e.hom)).mp
  rw [← a.naturality, ← b.naturality, hn]

private theorem common_component_eq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {X Y Z : SixFunctorSpace D}
    {F G : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left ×
        generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left ⥤
      generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Z.obj.left}
    (a b : F ⟶ G)
    (hs : ∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
      (L : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀),
      a.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K,
            (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L) =
        b.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K,
            (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L))
    (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
    (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left) :
    a.app (K, L) = b.app (K, L) := by
  let E₀ := Padic.finiteCoefficientCompositum C.l C.Qbar K.stage L.stage
  have hK : K.stage ≤ E₀ :=
    ((Padic.finiteCoefficientFields_properties C.l C.Qbar).1 K.stage L.stage).1
  have hL : L.stage ≤ E₀ :=
    ((Padic.finiteCoefficientFields_properties C.l C.Qbar).1 K.stage L.stage).2
  exact component_eq_of_iso a b
    (Iso.prod
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left).isoToStage
        K hK)
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar Y.obj.left).isoToStage
        L hL))
    (hs E₀ (K.toStage hK) (L.toStage hL))

end Naturality

set_option backward.isDefEq.respectTransparency false in
/-- Common finite coefficient fields transport the four comparison equations
of the normalized projection. No projection invertibility is asserted here.
Source: thm-sf-pf-field.proof.md, Compatibility and the common finite coefficient
field paragraph, and fix-prop-projection-formula.proof.md, final coherence
sentence, in literature/blueprint/latest/blueprint.
(blueprint: lem-sf-common-projection-comparison-equations).
Proof: for any displayed equation choose a finite compositum of the fields of
its inputs. Move each input there using the stage system's isoToStage; its
canonical transition isomorphisms identify each pair with its enlarged model.
Use the canonical common-stage tensor comparison, defined on representatives,
and the normalized pullback/support comparisons. The supplied adjunction
comparisons preserve the proper counit and the open unit/counit, so the image
of each stage projection is exactly the common-stage projection after these
endpoint identifications. Apply inclusion to the stage compactification and
composition equations. Naturality moves the endpoint comparisons through each
factor; commonStageComparison.compactification, .composition and .pullComposition
then identify the specified composites. Cancel the outer isomorphisms to obtain
the two common-stage equations. The threefold version of the same calculation
carries the stage pentagon to the specified common-stage pentagon, including
its transported composite compactification. The .properIdentity equation and
preservation of the proper adjunction identify the proper-counit component and
transport the proper equation. The identity and tower comparisons of the
canonical common-stage tensor and stage-system inclusions show the results are
independent of the chosen compositum. Only forward preservation of equations
is used. Naturality in the input isomorphisms returns the result to the original
pairs; their structure morphisms need not be separated. -/
theorem compactSupportProjectionCoherence_common
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C)
    (hH : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      CompactSupportProjectionCoherence (H.coefficientStages E₀).rational
        (H.coefficientStages E₀).rationalTensor (H.coefficientStages E₀).rationalExchange
        (fun _ _ ↦ True)) :
    CompactSupportProjectionCoherence H.commonStage H.commonStageTensor H.commonStageExchange
      (fun _ _ ↦ True) := by
  constructor
  · intro X Y f _ _ _ c d K L _
    let A := H.commonStageExchange
    let a := compactificationLeft A f c d
    let b := compactificationRight A f c d
    have hs : ∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
        (L₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀),
        a.app ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K₀,
            (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L₀) =
          b.app ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K₀,
            (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L₀) := by
      intro E₀ K₀ L₀
      simpa only [a, b, compactificationLeft_app, compactificationRight_app] using
        commonProjectionCompactification_onStage H E₀ (hH E₀) f c d K₀ L₀
    simpa only [a, b, compactificationLeft_app, compactificationRight_app] using
      common_component_eq (C := C) (X := X) (Y := Y) (Z := Y) a b hs K L
  · intro X Y Z f g _ _ _ _ _ _ cf cg cfg K L _
    let A := H.commonStageExchange
    let a := compositionLeft A f g cf cg cfg
    let b := compositionRight A f g cf cg cfg
    have hs : ∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
        (L₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Z.obj.left E₀),
        a.app ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K₀,
            (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Z.obj.left) E₀).obj L₀) =
          b.app ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K₀,
            (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Z.obj.left) E₀).obj L₀) := by
      intro E₀ K₀ L₀
      simpa only [a, b, compositionLeft_app, compositionRight_app] using
        commonProjectionComposition_onStage H E₀ (hH E₀) f g cf cg cfg K₀ L₀
    simpa only [a, b, compositionLeft_app, compositionRight_app] using
      common_component_eq (C := C) (X := X) (Y := Z) (Z := Z) a b hs K L
  · intro X Y Z W f g h _ _ _ _ _ _ _ _ _ cf cg ch cfg cgh cfgh K
    exact coefficient_pentagon (H.commonStageComparison K.stage) f g h cf cg ch cfg cgh
      cfgh K.obj ((hH K.stage).pentagon f g h cf cg ch cfg cgh cfgh K.obj)
  · intro X Y f _ c K L _
    let A := H.commonStageExchange
    let a := properLeft A f c
    let b := properRight A f c
    have hs : ∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
        (L₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀),
        a.app ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K₀,
            (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L₀) =
          b.app ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K₀,
            (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L₀) := by
      intro E₀ K₀ L₀
      simpa only [a, b, properLeft_app, properRight_app] using
        commonProjectionProper_onStage H E₀ (hH E₀) f c K₀ L₀
    simpa only [a, b, properLeft_app, properRight_app] using
      common_component_eq (C := C) (X := X) (Y := Y) (Z := Y) a b hs K L

end WeilConjectures
