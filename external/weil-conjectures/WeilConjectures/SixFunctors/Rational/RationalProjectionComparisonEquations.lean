/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionCoherence
import WeilConjectures.SixFunctors.ProjectionCoefficientTransport.RationalProjectionTensorCompatibility
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import Mathlib.Algebra.CharP.CharAndCard

/-! # Compact-support projection comparison equations

Source: the coherence paragraph of the projection-formula proof in
literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done.
(blueprint: lem-sf-rational-projection-comparison-equations).
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
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

namespace ProjectionCoefficientTransport

section
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
  {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
  {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
  (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
    (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))

private theorem tensor_first (X : SixFunctorSpace D) {K K' : B X}
    (a : K ⟶ K') (L : B X) :
    (V X).map (((T X).map a).app L) ≫ (t X).hom.app (K', L) =
      (t X).hom.app (K, L) ≫ ((T' X).map ((V X).map a)).app ((V X).obj L) := by
  simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, Category.comp_id] using
    (t X).hom.naturality (Prod.mkHom a (𝟙 L))

private theorem source_refinement {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).map (((T Y).map ((S.comparison f c d).hom.app K)).app L) ≫
        (source C t f d K L).hom =
      (source C t f c K L).hom ≫
        ((T' Y).map ((S'.comparison f c d).hom.app ((V X).obj K))).app ((V Y).obj L) := by
  simp only [source, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [← Category.assoc, tensor_first t, Category.assoc]
  rw [← NatTrans.comp_app, ← Functor.map_comp, C.compactification f c d K,
    Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem target_refinement {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).map ((S.comparison f c d).hom.app
        (((T X).obj K).obj ((S.pull f).obj L))) ≫ (target C t f d K L).hom =
      (target C t f c K L).hom ≫ (S'.comparison f c d).hom.app
        (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) := by
  simp only [target, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, C.compactification f c d, Category.assoc,
    ← (S'.comparison f c d).hom.naturality]
  simp only [Category.assoc]

private theorem refinement_transfer
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (A' : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S' T' Q)
    (hp : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (c : Compactification f.hom.left) (K : B X) (L : B Y),
      (V Y).map (compactSupportProjectionComponent A f c K L) ≫
          (target C t f c K L).hom =
        (source C t f c K L).hom ≫
          compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) (K : B X) (L : B Y)
    (h : ((T Y).map ((S.comparison f c d).hom.app K)).app L ≫
        compactSupportProjectionComponent A f d K L =
      compactSupportProjectionComponent A f c K L ≫
        (S.comparison f c d).hom.app (((T X).obj K).obj ((S.pull f).obj L))) :
    ((T' Y).map ((S'.comparison f c d).hom.app ((V X).obj K))).app ((V Y).obj L) ≫
        compactSupportProjectionComponent A' f d ((V X).obj K) ((V Y).obj L) =
      compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L) ≫
        (S'.comparison f c d).hom.app
          (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) := by
  apply (cancel_epi (source C t f c K L).hom).1
  calc
    _ = (V Y).map (((T Y).map ((S.comparison f c d).hom.app K)).app L) ≫
        (V Y).map (compactSupportProjectionComponent A f d K L) ≫
        (target C t f d K L).hom := by
      rw [← Category.assoc, ← source_refinement C t, Category.assoc, hp]
    _ = (V Y).map (compactSupportProjectionComponent A f c K L) ≫
        (V Y).map ((S.comparison f c d).hom.app
          (((T X).obj K).obj ((S.pull f).obj L))) ≫
        (target C t f d K L).hom := by
      rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [target_refinement C t, ← Category.assoc, hp, Category.assoc]

private theorem proper_identification {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left] (c : Compactification f.hom.left) (K : B X) :
    (V Y).map ((S.properIdentification f c).hom.app K) ≫
        (C.directAdjunction f).right.hom.app K =
      (C.supportAdjunction f c).left.hom.app K ≫
        (S'.properIdentification f c).hom.app ((V X).obj K) := by
  simp only [SixFunctorPushStage.properIdentification, Iso.trans_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [C.properIdentity, ← Category.assoc, C.compactification, Category.assoc]

private theorem source_proper {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left] (c : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).map (((T Y).map ((S.properIdentification f c).hom.app K)).app L) ≫
        (properSource C t f K L).hom =
      (source C t f c K L).hom ≫
        ((T' Y).map ((S'.properIdentification f c).hom.app ((V X).obj K))).app
          ((V Y).obj L) := by
  simp only [source, properSource, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [← Category.assoc, tensor_first t, Category.assoc]
  rw [← NatTrans.comp_app, ← Functor.map_comp, proper_identification C,
    Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem target_proper {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left] (c : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).map ((S.properIdentification f c).hom.app
        (((T X).obj K).obj ((S.pull f).obj L))) ≫ (properTarget C t f K L).hom =
      (target C t f c K L).hom ≫ (S'.properIdentification f c).hom.app
        (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) := by
  simp only [target, properTarget, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, proper_identification C, Category.assoc,
    ← (S'.properIdentification f c).hom.naturality]
  simp only [Category.assoc]

private theorem proper_transfer
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (A' : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S' T' Q)
    (hp : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (c : Compactification f.hom.left) (K : B X) (L : B Y),
      (V Y).map (compactSupportProjectionComponent A f c K L) ≫
          (target C t f c K L).hom =
        (source C t f c K L).hom ≫
          compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L))
    (hq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
      (K : B X) (L : B Y),
      (V Y).map (compactSupportProperProjection A f K L) ≫
          (properTarget C t f K L).hom =
        (properSource C t f K L).hom ≫
          compactSupportProperProjection A' f ((V X).obj K) ((V Y).obj L))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : B X) (L : B Y)
    (h : ((T Y).map ((S.properIdentification f c).hom.app K)).app L ≫
        compactSupportProperProjection A f K L =
      compactSupportProjectionComponent A f c K L ≫
        (S.properIdentification f c).hom.app (((T X).obj K).obj ((S.pull f).obj L))) :
    ((T' Y).map ((S'.properIdentification f c).hom.app ((V X).obj K))).app ((V Y).obj L) ≫
        compactSupportProperProjection A' f ((V X).obj K) ((V Y).obj L) =
      compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L) ≫
        (S'.properIdentification f c).hom.app
          (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) := by
  apply (cancel_epi (source C t f c K L).hom).1
  calc
    _ = (V Y).map (((T Y).map ((S.properIdentification f c).hom.app K)).app L) ≫
        (V Y).map (compactSupportProperProjection A f K L) ≫
        (properTarget C t f K L).hom := by
      rw [← Category.assoc, ← source_proper C t, Category.assoc, hq]
    _ = (V Y).map (compactSupportProjectionComponent A f c K L) ≫
        (V Y).map ((S.properIdentification f c).hom.app
          (((T X).obj K).obj ((S.pull f).obj L))) ≫
        (properTarget C t f K L).hom := by
      rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [target_proper C t, ← Category.assoc, hp, Category.assoc]

private theorem projection_natural_square {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q)
    (K K' : B Q.X) (L L' : B Q.Y) (a : K ⟶ K') (b : L ⟶ L') :
    ((T Q.Y).map ((S.support Q.f Q.compactification).map a)).app L ≫
        ((T Q.Y).obj ((S.support Q.f Q.compactification).obj K')).map b ≫
        A.projectionComponent K' L' =
      A.projectionComponent K L ≫ (S.support Q.f Q.compactification).map
        (((T Q.X).map a).app ((S.pull Q.f).obj L) ≫
          ((T Q.X).obj K').map ((S.pull Q.f).map b)) := by
  let η := Functor.uncurry.map A.stage.projection
  have hs : (S.support Q.f Q.compactification).prod (𝟭 (B Q.Y)) ⋙
      Functor.uncurry.obj (T Q.Y) =
      Functor.uncurry.obj (A.stage.compactSupport ⋙ A.stage.tensorY) := by
    simp only [← A.tensorY, ← A.compactSupport]
    rfl
  have ht : ((𝟭 (B Q.X)).prod (S.pull Q.f) ⋙ Functor.uncurry.obj (T Q.X)) ⋙
      S.support Q.f Q.compactification = Functor.uncurry.obj
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

private theorem projection_natural
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {K K' : B X} {L L' : B Y} (a : K ⟶ K') (b : L ⟶ L') :
    ((T Y).map ((S.support f c).map a)).app L ≫
        ((T Y).obj ((S.support f c).obj K')).map b ≫
        compactSupportProjectionComponent A f c K' L' =
      compactSupportProjectionComponent A f c K L ≫ (S.support f c).map
        (((T X).map a).app ((S.pull f).obj L) ≫
          ((T X).obj K').map ((S.pull f).map b)) := by
  exact projection_natural_square (A (compactSupportProjectionSquare f c)) _ _ _ _ a b

private theorem projection_first
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {K K' : B X} (a : K ⟶ K') (L : B Y) :
    ((T Y).map ((S.support f c).map a)).app L ≫
        compactSupportProjectionComponent A f c K' L =
      compactSupportProjectionComponent A f c K L ≫
        (S.support f c).map (((T X).map a).app ((S.pull f).obj L)) := by
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] using
    projection_natural A f c a (𝟙 L)

private theorem projection_second
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : B X) {L L' : B Y} (b : L ⟶ L') :
    ((T Y).obj ((S.support f c).obj K)).map b ≫
        compactSupportProjectionComponent A f c K L' =
      compactSupportProjectionComponent A f c K L ≫
        (S.support f c).map (((T X).obj K).map ((S.pull f).map b)) := by
  simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] using
    projection_natural A f c (𝟙 K) b

private theorem inner_source {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (K : B X) (L : B Z) :
    (inner C t g ((S.support f cf).obj K) L).hom ≫
        ((T' Y).map ((C.supportAdjunction f cf).left.hom.app K)).app
          ((S'.pull g).obj ((V Z).obj L)) =
      (source C t f cf K ((S.pull g).obj L)).hom ≫
        ((T' Y).obj ((S'.support f cf).obj ((V X).obj K))).map
          ((C.directAdjunction g).left.hom.app L) := by
  simp only [inner, source, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.comp_id, Category.assoc]
  have hn := ((T' Y).map ((C.supportAdjunction f cf).left.hom.app K)).naturality
    ((C.directAdjunction g).left.hom.app L)
  simp only [Functor.comp_obj] at hn
  rw [hn]

private def doubleTarget {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (K : B X) (L : B Z) :
    (V Z).obj ((S.support g cg).obj ((S.support f cf).obj
      (((T X).obj K).obj ((S.pull f).obj ((S.pull g).obj L))))) ≅
    (S'.support g cg).obj ((S'.support f cf).obj
      (((T' X).obj ((V X).obj K)).obj
        ((S'.pull f).obj ((S'.pull g).obj ((V Z).obj L))))) :=
  (C.supportAdjunction g cg).left.app _ ≪≫ (S'.support g cg).mapIso
    (target C t f cf K ((S.pull g).obj L) ≪≫ (S'.support f cf).mapIso
      (((T' X).obj ((V X).obj K)).mapIso
        ((S'.pull f).mapIso ((C.directAdjunction g).left.app L))))

private theorem source_composition {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z) :
    (source C t (f ≫ g) cfg K L).hom ≫
        ((T' Z).map ((S'.composition f g cf cg cfg).hom.app ((V X).obj K))).app
          ((V Z).obj L) =
      (V Z).map (((T Z).map ((S.composition f g cf cg cfg).hom.app K)).app L) ≫
        (source C t g cg ((S.support f cf).obj K) L).hom ≫
        ((T' Z).map ((S'.support g cg).map
          ((C.supportAdjunction f cf).left.hom.app K))).app ((V Z).obj L) := by
  simp only [source, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc]
  have ht := tensor_first t Z ((S.composition f g cf cg cfg).hom.app K) L
  simp only [Functor.comp_obj] at ht
  rw [← Category.assoc ((V Z).map _), ht]
  simp only [Category.assoc]
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rw [C.composition f g cf cg cfg K]

private theorem composition_left
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (A' : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S' T' Q)
    (hp : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (c : Compactification f.hom.left) (K : B X) (L : B Y),
      (V Y).map (compactSupportProjectionComponent A f c K L) ≫
          (target C t f c K L).hom =
        (source C t f c K L).hom ≫
          compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L))
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z) :
    (source C t (f ≫ g) cfg K L).hom ≫
        ((T' Z).map ((S'.composition f g cf cg cfg).hom.app ((V X).obj K))).app
          ((V Z).obj L) ≫
        compactSupportProjectionComponent A' g cg ((S'.support f cf).obj ((V X).obj K))
          ((V Z).obj L) ≫
        (S'.support g cg).map (compactSupportProjectionComponent A' f cf ((V X).obj K)
          ((S'.pull g).obj ((V Z).obj L))) =
      (V Z).map (((T Z).map ((S.composition f g cf cg cfg).hom.app K)).app L ≫
        compactSupportProjectionComponent A g cg ((S.support f cf).obj K) L ≫
        (S.support g cg).map
          (compactSupportProjectionComponent A f cf K ((S.pull g).obj L))) ≫
        (doubleTarget C t f g cf cg K L).hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% source_composition C t f g cf cg cfg K L]
  have hpf := projection_first A' g cg
    ((C.supportAdjunction f cf).left.hom.app K) ((V Z).obj L)
  simp only [Functor.comp_obj] at hpf
  rw [← Category.assoc (((T' Z).map ((S'.support g cg).map _)).app _), hpf]
  simp only [Category.assoc]
  rw [← Category.assoc (source C t g cg _ L).hom, ← hp]
  simp only [target, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp,
    reassoc_of% inner_source C t f g cf K L]
  simp only [Functor.map_comp]
  have hps := projection_second A' f cf ((V X).obj K)
    ((C.directAdjunction g).left.hom.app L)
  simp only [Functor.comp_obj] at hps
  rw [← Functor.map_comp, hps]
  simp only [Functor.map_comp]
  rw [← Functor.map_comp, ← Functor.map_comp,
    ← reassoc_of% (hp f cf K ((S.pull g).obj L)), Functor.map_comp]
  have hn := (C.supportAdjunction g cg).left.hom.naturality
    (compactSupportProjectionComponent A f cf K ((S.pull g).obj L))
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc ((C.supportAdjunction g cg).left.hom.app _), ← hn]
  simp only [doubleTarget, target, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]

private theorem tensor_second (X : SixFunctorSpace D) (K : B X)
    {L L' : B X} (a : L ⟶ L') :
    (V X).map (((T X).obj K).map a) ≫ (t X).hom.app (K, L') =
      (t X).hom.app (K, L) ≫ ((T' X).obj ((V X).obj K)).map ((V X).map a) := by
  simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] using
    (t X).hom.naturality (Prod.mkHom (𝟙 K) a)

private def doubleInner {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (K : B X) (L : B Z) :=
  inner C t f K ((S.pull g).obj L) ≪≫
    ((T' X).obj ((V X).obj K)).mapIso
      ((S'.pull f).mapIso ((C.directAdjunction g).left.app L))

private theorem inner_composition {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (K : B X) (L : B Z) :
    (V X).map (((T X).obj K).map ((S.pullComposition f g).hom.app L)) ≫
        (doubleInner C t f g K L).hom =
      (inner C t (f ≫ g) K L).hom ≫
        ((T' X).obj ((V X).obj K)).map
          ((S'.pullComposition f g).hom.app ((V Z).obj L)) := by
  simp only [doubleInner, inner, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.assoc]
  have ht := tensor_second t X K ((S.pullComposition f g).hom.app L)
  simp only [Functor.comp_obj] at ht
  rw [← Category.assoc ((V X).map _), ht]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, C.pullComposition f g L,
    Functor.map_comp]

private def doubleSupport {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left) :
    (S.support f cf ⋙ S.support g cg) ⋙ V Z ≅
      V X ⋙ (S'.support f cf ⋙ S'.support g cg) :=
  sixFunctorCompositeRealization (C.supportAdjunction f cf).left
    (C.supportAdjunction g cg).left

private theorem doubleTarget_hom {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (K : B X) (L : B Z) :
    (doubleTarget C t f g cf cg K L).hom =
      (doubleSupport C f g cf cg).hom.app
          (((T X).obj K).obj ((S.pull f).obj ((S.pull g).obj L))) ≫
        (S'.support g cg).map ((S'.support f cf).map (doubleInner C t f g K L).hom) := by
  simp only [doubleTarget, doubleSupport, doubleInner, target,
    sixFunctorCompositeRealization, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.mapIso_hom,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]

private theorem doubleSupport_composition {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) :
    (V Z).map ((S.composition f g cf cg cfg).hom.app K) ≫
        (doubleSupport C f g cf cg).hom.app K =
      (C.supportAdjunction (f ≫ g) cfg).left.hom.app K ≫
        (S'.composition f g cf cg cfg).hom.app ((V X).obj K) := by
  simpa only [doubleSupport, sixFunctorCompositeRealization, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using
    C.composition f g cf cg cfg K

private theorem target_composition {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z) :
    (V Z).map ((S.composition f g cf cg cfg).hom.app
        (((T X).obj K).obj ((S.pull (f ≫ g)).obj L))) ≫
      (V Z).map ((S.support g cg).map ((S.support f cf).map
        (((T X).obj K).map ((S.pullComposition f g).hom.app L)))) ≫
      (doubleTarget C t f g cf cg K L).hom =
    (target C t (f ≫ g) cfg K L).hom ≫
      (S'.composition f g cf cg cfg).hom.app
        (((T' X).obj ((V X).obj K)).obj ((S'.pull (f ≫ g)).obj ((V Z).obj L))) ≫
      (S'.support g cg).map ((S'.support f cf).map
        (((T' X).obj ((V X).obj K)).map
          ((S'.pullComposition f g).hom.app ((V Z).obj L)))) := by
  rw [doubleTarget_hom]
  have hn := (doubleSupport C f g cf cg).hom.naturality
    (((T X).obj K).map ((S.pullComposition f g).hom.app L))
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc
    ((V Z).map ((S.support g cg).map ((S.support f cf).map _))), hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, inner_composition C t,
    Functor.map_comp, Functor.map_comp]
  rw [← Category.assoc ((V Z).map _), doubleSupport_composition C]
  simp only [target, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  have hm := (S'.composition f g cf cg cfg).hom.naturality
    (inner C t (f ≫ g) K L).hom
  simp only [Functor.comp_map, Functor.comp_obj] at hm
  rw [← reassoc_of% hm]

private theorem composition_transfer
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (A' : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S' T' Q)
    (hp : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (c : Compactification f.hom.left) (K : B X) (L : B Y),
      (V Y).map (compactSupportProjectionComponent A f c K L) ≫
          (target C t f c K L).hom =
        (source C t f c K L).hom ≫
          compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L))
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z)
    (h : ((T Z).map ((S.composition f g cf cg cfg).hom.app K)).app L ≫
        compactSupportProjectionComponent A g cg ((S.support f cf).obj K) L ≫
        (S.support g cg).map
          (compactSupportProjectionComponent A f cf K ((S.pull g).obj L)) =
      compactSupportProjectionComponent A (f ≫ g) cfg K L ≫
        (S.composition f g cf cg cfg).hom.app
          (((T X).obj K).obj ((S.pull (f ≫ g)).obj L)) ≫
        (S.support g cg).map ((S.support f cf).map
          (((T X).obj K).map ((S.pullComposition f g).hom.app L)))) :
    ((T' Z).map ((S'.composition f g cf cg cfg).hom.app ((V X).obj K))).app ((V Z).obj L) ≫
        compactSupportProjectionComponent A' g cg ((S'.support f cf).obj ((V X).obj K))
          ((V Z).obj L) ≫
        (S'.support g cg).map (compactSupportProjectionComponent A' f cf ((V X).obj K)
          ((S'.pull g).obj ((V Z).obj L))) =
      compactSupportProjectionComponent A' (f ≫ g) cfg ((V X).obj K) ((V Z).obj L) ≫
        (S'.composition f g cf cg cfg).hom.app
          (((T' X).obj ((V X).obj K)).obj ((S'.pull (f ≫ g)).obj ((V Z).obj L))) ≫
        (S'.support g cg).map ((S'.support f cf).map
          (((T' X).obj ((V X).obj K)).map
            ((S'.pullComposition f g).hom.app ((V Z).obj L)))) := by
  apply (cancel_epi (source C t (f ≫ g) cfg K L).hom).1
  rw [composition_left C t A A' hp, h]
  simp only [Functor.map_comp, Category.assoc]
  rw [target_composition C t, ← Category.assoc, hp]
  simp only [Category.assoc]

private def triple {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (K : B X) :
    (V W).obj ((S.support h ch).obj ((S.support g cg).obj ((S.support f cf).obj K))) ≅
      (S'.support h ch).obj
        ((S'.support g cg).obj ((S'.support f cf).obj ((V X).obj K))) :=
  (C.supportAdjunction h ch).left.app _ ≪≫ (S'.support h ch).mapIso
    ((C.supportAdjunction g cg).left.app _ ≪≫
      (S'.support g cg).mapIso ((C.supportAdjunction f cf).left.app K))

private theorem triple_left {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : B X) :
    (V W).map ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
        (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K)) ≫
        (triple C f g h cf cg ch K).hom =
      (C.supportAdjunction ((f ≫ g) ≫ h) cfgh).left.hom.app K ≫
        (S'.composition (f ≫ g) h cfg ch cfgh).hom.app ((V X).obj K) ≫
        (S'.support h ch).map ((S'.composition f g cf cg cfg).hom.app ((V X).obj K)) := by
  simp only [triple, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have hn := (C.supportAdjunction h ch).left.hom.naturality
    ((S.composition f g cf cg cfg).hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc ((V W).map ((S.support h ch).map _)), hn]
  simp only [Category.assoc]
  simp only [← Functor.map_comp]
  rw [C.composition f g cf cg cfg K]
  simp only [Functor.map_comp]
  rw [reassoc_of% C.composition (f ≫ g) h cfg ch cfgh K]

private theorem triple_right {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification (f ≫ (g ≫ h)).hom.left) (K : B X) :
    (V W).map ((S.composition f (g ≫ h) cf cgh cfgh).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K)) ≫
        (triple C f g h cf cg ch K).hom =
      (C.supportAdjunction (f ≫ (g ≫ h)) cfgh).left.hom.app K ≫
        (S'.composition f (g ≫ h) cf cgh cfgh).hom.app ((V X).obj K) ≫
        (S'.composition g h cg ch cgh).hom.app ((S'.support f cf).obj ((V X).obj K)) := by
  simp only [triple, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% C.composition g h cg ch cgh ((S.support f cf).obj K)]
  have hn := (S'.composition g h cg ch cgh).hom.naturality
    ((C.supportAdjunction f cf).left.hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn]
  rw [reassoc_of% C.composition f (g ≫ h) cf cgh cfgh K]

private theorem support_transport {X Y : SixFunctorSpace D} (f g : X ⟶ Y)
    (e : f = g) (c : Compactification f.hom.left) :
    S.support f c = S.support g
      (Eq.mp (congrArg (fun q : X ⟶ Y ↦ Compactification q.hom.left) e) c) := by
  cases e
  rfl

private theorem comparison_transport {X Y : SixFunctorSpace D} (f g : X ⟶ Y)
    (e : f = g) (c : Compactification f.hom.left) (K : B X) :
    HEq ((C.supportAdjunction f c).left.hom.app K)
      ((C.supportAdjunction g
        (Eq.mp (congrArg (fun q : X ⟶ Y ↦ Compactification q.hom.left) e) c)).left.hom.app K) := by
  cases e
  rfl

private theorem map_heq {A : Type v} [Category.{w} A]
    {A' : Type v'} [Category.{w'} A'] (F : A ⥤ A')
    {X Y X' Y' : A} (hx : X = X') (hy : Y = Y')
    {a : X ⟶ Y} {b : X' ⟶ Y'} (hab : HEq a b) : HEq (F.map a) (F.map b) := by
  cases hx
  cases hy
  cases hab
  rfl

private theorem cancel_iso_heq {A : Type v} [Category.{w} A]
    {X Y X' Y' Z : A} (e : X ≅ Y) (e' : X' ≅ Y')
    (hx : X = X') (hy : Y = Y') (he : HEq e.hom e'.hom)
    (a : Y ⟶ Z) (b : Y' ⟶ Z) (hab : HEq (e.hom ≫ a) (e'.hom ≫ b)) : HEq a b := by
  cases hx
  cases hy
  have he' := eq_of_heq he
  rw [he'] at hab
  exact heq_of_eq ((cancel_epi e'.hom).1 (eq_of_heq hab))

include C in
private theorem pentagon_transfer {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : B X)
    (hp : HEq ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
        (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K))
      ((S.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun q : X ⟶ W ↦ Compactification q.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K))) :
    HEq ((S'.composition (f ≫ g) h cfg ch cfgh).hom.app ((V X).obj K) ≫
        (S'.support h ch).map ((S'.composition f g cf cg cfg).hom.app ((V X).obj K)))
      ((S'.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun q : X ⟶ W ↦ Compactification q.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app ((V X).obj K) ≫
        (S'.composition g h cg ch cgh).hom.app
          ((S'.support f cf).obj ((V X).obj K))) := by
  let d := Eq.mp (congrArg (fun q : X ⟶ W ↦ Compactification q.hom.left)
    (Category.assoc f g h)) cfgh
  have hobj := support_transport (S := S) _ _ (Category.assoc f g h) cfgh
  have hobj' := support_transport (S := S') _ _ (Category.assoc f g h) cfgh
  apply cancel_iso_heq
    ((C.supportAdjunction ((f ≫ g) ≫ h) cfgh).left.app K)
    ((C.supportAdjunction (f ≫ (g ≫ h)) d).left.app K)
    (congrArg (fun (F : B X ⥤ B W) ↦ (V W).obj (F.obj K)) hobj)
    (congrArg (fun (F : B' X ⥤ B' W) ↦ F.obj ((V X).obj K)) hobj')
    (comparison_transport C _ _ (Category.assoc f g h) cfgh K)
  simp only [Iso.app_hom]
  rw [← triple_left C f g h cf cg ch cfg cfgh K,
    ← triple_right C f g h cf cg ch cgh d K]
  exact heq_comp (congrArg (fun (F : B X ⥤ B W) ↦ (V W).obj (F.obj K)) hobj) rfl rfl
    (map_heq (V W) (congrArg (fun (F : B X ⥤ B W) ↦ F.obj K) hobj) rfl hp) HEq.rfl

end
end ProjectionCoefficientTransport

private theorem integral_finiteTor {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    finiteTorConstructibleIntegral C.l E X.obj.left K.obj := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) := fun x ↦
    let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ X.obj.hom.appTop ≫
      X.obj.left.Γevaluation x).hom
    (Eq.mp (congrArg IsUnit (map_natCast φ C.l))
      ((isUnit_iff_ne_zero.mpr
        (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : C.l.Prime)
          C.different.symm)).map φ)).invertible
  rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
  exact K.property

/-- Rational localization preserves the four comparison equations of the
normalized compact-support projection. This only transports equalities; it does
not assert invertibility or naturality of the rational component.
Source: thm-sf-pf-field.proof.md, Compatibility, and the final coherence sentence
of fix-prop-projection-formula.proof.md, in literature/blueprint/latest/blueprint.
(blueprint: lem-sf-rational-projection-comparison-equations).
Proof: give each rational input its literal integral model; the raw scalar
localization has unchanged objects. The residue Tor criterion identifies the
integral constructible predicate with the uniform finite-Tor predicate, so the
input equations apply to these models. Use the canonical tensor localization
comparison, normalized on pure tensor morphisms. The tensor and tensor-pullback
normalizations in H identify it with the prescribed tensor operations and their
pullback comparisons. The operation comparisons preserve adjunction units and
counits, hence identify the localization of the proper counit mate and the
open projection with the prescribed rational component. Apply localization to
the integral refinement equation and cancel the canonical tensor/support
endpoint comparisons. For composition, move those comparisons past tensor and
support maps by naturality; H.rationalization.composition and .pullComposition
identify the two compositors and the final pullback comparison. The remaining
equation is the image of the integral composition equation. Apply the same
calculation to three support factors to transport the pentagon, keeping the
associativity transport of its compactification. Finally, .compactification and
.properIdentity carry properIdentification to its rational counterpart; the
unit/counit comparison identifies the proper projection mate, giving the proper
equation. Every cancellation is of a specified natural isomorphism, and every
equality is transported forward, without reflecting equality by localization. -/
theorem compactSupportProjectionCoherence_rational
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (hH : CompactSupportProjectionCoherence H.integral H.integralTensor H.integralExchange
      (fun X K ↦ finiteTorConstructibleIntegral C.l E X.obj.left K.obj)) :
    CompactSupportProjectionCoherence H.rational H.rationalTensor H.rationalExchange
      (fun _ _ ↦ True) := by
  obtain ⟨hp, hq⟩ := rationalProjectionTensorCompatibility H
  let t := rationalProjectionTensorComparison H
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y f _ _ _ c d K L _
    exact ProjectionCoefficientTransport.refinement_transfer H.rationalization t
      H.integralExchange H.rationalExchange hp f c d K.obj L.obj
      (hH.compactification f c d K.obj L.obj (integral_finiteTor Y L.obj))
  · intro X Y Z f g _ _ _ _ _ _ cf cg cfg K L _
    exact ProjectionCoefficientTransport.composition_transfer H.rationalization t
      H.integralExchange H.rationalExchange hp f g cf cg cfg K.obj L.obj
      (hH.composition f g cf cg cfg K.obj L.obj (integral_finiteTor Z L.obj))
  · intro X Y Z W f g h _ _ _ _ _ _ _ _ _ cf cg ch cfg cgh cfgh K
    exact ProjectionCoefficientTransport.pentagon_transfer H.rationalization
      f g h cf cg ch cfg cgh cfgh K.obj
      (hH.pentagon f g h cf cg ch cfg cgh cfgh K.obj)
  · intro X Y f _ c K L _
    exact ProjectionCoefficientTransport.proper_transfer H.rationalization t
      H.integralExchange H.rationalExchange hp hq f c K.obj L.obj
      (hH.proper f c K.obj L.obj (integral_finiteTor Y L.obj))

end WeilConjectures
