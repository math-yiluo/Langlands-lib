/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import WeilConjectures.SixFunctors.Rational.RationalProjectionTensorModels
import Mathlib.Algebra.CharP.CharAndCard

/-! # Shared tensor comparison for rational projection mates

Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-rational-projection-tensor-compatibility).
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
open AlgebraicGeometry.ProEtale CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures.ProjectionCoefficientTransport

variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
  {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
  {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
  (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
    (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))

/-- Tensor comparison followed by the pullback comparison in the second slot.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-rational-projection-tensor-compatibility). -/
def inner {X Y : SixFunctorSpace D} (f : X ⟶ Y) (K : B X) (L : B Y) :
    (V X).obj (((T X).obj K).obj ((S.pull f).obj L)) ≅
      ((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L)) :=
  (t X).app (K, (S.pull f).obj L) ≪≫
    (Functor.uncurry.obj (T' X)).mapIso
      (Iso.prod (Iso.refl _) ((C.directAdjunction f).left.app L))

/-- The source endpoint of the localized compact-support projection.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-rational-projection-tensor-compatibility). -/
def source {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).obj (((T Y).obj ((S.support f c).obj K)).obj L) ≅
      ((T' Y).obj ((S'.support f c).obj ((V X).obj K))).obj ((V Y).obj L) :=
  (t Y).app ((S.support f c).obj K, L) ≪≫
    (Functor.uncurry.obj (T' Y)).mapIso
      (Iso.prod ((C.supportAdjunction f c).left.app K) (Iso.refl _))

/-- The target endpoint of the localized compact-support projection.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-rational-projection-tensor-compatibility). -/
def target {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).obj ((S.support f c).obj (((T X).obj K).obj ((S.pull f).obj L))) ≅
      (S'.support f c).obj
        (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) :=
  (C.supportAdjunction f c).left.app _ ≪≫ (S'.support f c).mapIso (inner C t f K L)

/-- The proper source endpoint uses the direct-image comparison.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-rational-projection-tensor-compatibility). -/
def properSource {X Y : SixFunctorSpace D} (f : X ⟶ Y) (K : B X) (L : B Y) :
    (V Y).obj (((T Y).obj ((S.direct f).obj K)).obj L) ≅
      ((T' Y).obj ((S'.direct f).obj ((V X).obj K))).obj ((V Y).obj L) :=
  (t Y).app ((S.direct f).obj K, L) ≪≫
    (Functor.uncurry.obj (T' Y)).mapIso
      (Iso.prod ((C.directAdjunction f).right.app K) (Iso.refl _))

/-- The proper target endpoint uses the same tensor/pullback comparison.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-rational-projection-tensor-compatibility). -/
def properTarget {X Y : SixFunctorSpace D} (f : X ⟶ Y) (K : B X) (L : B Y) :
    (V Y).obj ((S.direct f).obj (((T X).obj K).obj ((S.pull f).obj L))) ≅
      (S'.direct f).obj
        (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) :=
  (C.directAdjunction f).right.app _ ≪≫ (S'.direct f).mapIso (inner C t f K L)

end WeilConjectures.ProjectionCoefficientTransport

namespace WeilConjectures
open ProjectionCoefficientTransport

private theorem normalizedProjection
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {F F₀ : B ⥤ A} {G G₀ : A ⥤ B}
    {TX TX₀ : A ⥤ A ⥤ A} {TY TY₀ : B ⥤ B ⥤ B}
    (adj : F ⊣ G) (adj₀ : F₀ ⊣ G₀)
    (mu : (Functor.postcompose₂.obj F₀).obj TY₀ ≅
      (((Functor.whiskeringLeft₂ _).obj F₀).obj F₀).obj TX₀)
    (hF : F₀ = F) (hG : G₀ = G) (hX : TX₀ = TX) (hY : TY₀ = TY)
    (ha : HEq adj₀ adj) (K : A) (L : B) :
    eqToHom (by rw [hG, hY]) ≫
        ((adj₀.rightAdjointProjectionMap mu.hom).app K).app L ≫
        eqToHom (by rw [hF, hG, hX]) =
      ((adj.rightAdjointProjectionMap
        (eqToIso (by rw [hF, hY]) ≪≫ mu ≪≫
          eqToIso (by rw [hF, hX])).hom).app K).app L := by
  subst F₀ G₀ TX₀ TY₀
  cases eq_of_heq ha
  simp

private theorem normalizedTensorPullback_heq
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {F F₀ : B ⥤ A} {TX TX₀ : A ⥤ A ⥤ A} {TY TY₀ : B ⥤ B ⥤ B}
    (mu : (Functor.postcompose₂.obj F₀).obj TY₀ ≅
      (((Functor.whiskeringLeft₂ _).obj F₀).obj F₀).obj TX₀)
    (hF : F₀ = F) (hX : TX₀ = TX) (hY : TY₀ = TY) (M N : B) :
    HEq (((eqToIso (by rw [hF, hY]) ≪≫ mu ≪≫
      eqToIso (by rw [hF, hX])).hom.app M).app N) ((mu.hom.app M).app N) := by
  subst F₀ TX₀ TY₀
  simp

private def properTensorPullback
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left] :
    (Functor.postcompose₂.obj (S.pull f)).obj (T Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (S.pull f)).obj (S.pull f)).obj (T X) :=
  eqToIso (by rw [(A (compactSupportProperSquare f)).tensorY,
    (A (compactSupportProperSquare f)).properPull]; rfl) ≪≫
    (A (compactSupportProperSquare f)).stage.tensorPullback ≪≫
      eqToIso (by rw [(A (compactSupportProperSquare f)).tensorBar,
        (A (compactSupportProperSquare f)).properPull]; rfl)

private theorem properProjection_eq
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : B X) (L : B Y) :
    compactSupportProperProjection A f K L =
      (((S.pullDirectAdjunction f).rightAdjointProjectionMap
        (properTensorPullback A f).hom).app K).app L := by
  exact normalizedProjection (S.pullDirectAdjunction f)
    (A (compactSupportProperSquare f)).stage.properAdjunction
    (A (compactSupportProperSquare f)).stage.tensorPullback
    (A (compactSupportProperSquare f)).properPull
    (A (compactSupportProperSquare f)).properPush
    (A (compactSupportProperSquare f)).tensorBar
    (A (compactSupportProperSquare f)).tensorY
    (A (compactSupportProperSquare f)).properAdjunction K L

section ProjectionTransport
universe a b a' b' ha hb ha' hb'
variable {A : Type a} [Category.{ha} A] {B : Type b} [Category.{hb} B]
  {A' : Type a'} [Category.{ha'} A'] {B' : Type b'} [Category.{hb'} B']

private theorem coefficientProjection
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (c : A ⥤ A') (d : B ⥤ B')
    (e : ExchangeProjectionAdjunctionComparison adj adj' c d)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (tA : TA ⋙ c ≅ c.prod c ⋙ TA') (tB : TB ⋙ d ≅ d.prod d ⋙ TB')
    (mu : ∀ U V : A, F.obj (TA.obj (U, V)) ⟶ TB.obj (F.obj U, F.obj V))
    (mu' : ∀ U V : A', F'.obj (TA'.obj (U, V)) ⟶ TB'.obj (F'.obj U, F'.obj V))
    (mu'_natural : ∀ {U V : A'} (a : U ⟶ V) (N : A'),
      F'.map (TA'.map (Prod.mkHom a (𝟙 N))) ≫ mu' V N =
        mu' U N ≫ TB'.map (Prod.mkHom (F'.map a) (𝟙 (F'.obj N))))
    (square : ∀ U V : A,
      d.map (mu U V) ≫ tB.hom.app (F.obj U, F.obj V) ≫
          TB'.map (Prod.mkHom (e.left.hom.app U) (e.left.hom.app V)) =
        e.left.hom.app (TA.obj (U, V)) ≫ F'.map (tA.hom.app (U, V)) ≫
          mu' (c.obj U) (c.obj V))
    (M : B) (N : A)
    (p : TA.obj (G.obj M, N) ⟶ G.obj (TB.obj (M, F.obj N)))
    (p' : TA'.obj (G'.obj (d.obj M), c.obj N) ⟶
      G'.obj (TB'.obj (d.obj M, F'.obj (c.obj N))))
    (hp : F.map p ≫ adj.counit.app _ =
      mu (G.obj M) N ≫ TB.map (Prod.mkHom (adj.counit.app M) (𝟙 _)))
    (hp' : F'.map p' ≫ adj'.counit.app _ =
      mu' (G'.obj (d.obj M)) (c.obj N) ≫
        TB'.map (Prod.mkHom (adj'.counit.app (d.obj M)) (𝟙 _))) :
    c.map p ≫ e.right.hom.app _ ≫ G'.map
        (tB.hom.app (M, F.obj N) ≫ TB'.map (Prod.mkHom (𝟙 _) (e.left.hom.app N))) =
      tA.hom.app (G.obj M, N) ≫
        TA'.map (Prod.mkHom (e.right.hom.app M) (𝟙 _)) ≫ p' := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [← Category.assoc (c.map p), adj'.homEquiv_naturality_right_symm]
  simp only [adj'.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (e.counit _)]
  have hn := e.left.inv.naturality p
  change F'.map (c.map p) ≫ e.left.inv.app _ =
    e.left.inv.app _ ≫ d.map (F.map p) at hn
  rw [reassoc_of% hn, ← d.map_comp_assoc, hp, d.map_comp]
  have ht := tB.hom.naturality (Prod.mkHom (adj.counit.app M) (𝟙 (F.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map] at ht
  simp only [Functor.comp_obj, Functor.id_obj, CategoryTheory.Functor.map_id] at ht
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  have hmu := mu'_natural (e.right.hom.app M) (c.obj N)
  simp only [Functor.comp_obj] at hmu ⊢
  rw [hp', reassoc_of% hmu]
  simp only [← TB'.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  have hc := e.counit M
  have hc' : e.left.hom.app (G.obj M) ≫ F'.map (e.right.hom.app M) ≫
      adj'.counit.app (d.obj M) = d.map (adj.counit.app M) := by
    rw [hc, Iso.hom_inv_id_app_assoc]
  have hs := congrArg (fun z ↦ e.left.inv.app (TA.obj (G.obj M, N)) ≫ z ≫
    TB'.map (Prod.mkHom (F'.map (e.right.hom.app M) ≫ adj'.counit.app (d.obj M))
      (𝟙 (F'.obj (c.obj N))))) (square (G.obj M) N)
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, ← TB'.map_comp,
    prod_comp, Functor.comp_obj, Category.comp_id, Category.id_comp, hc'] using hs

private theorem coefficientHomEquiv
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (c : A ⥤ A') (d : B ⥤ B')
    (e : ExchangeProjectionAdjunctionComparison adj adj' c d)
    {U : A} {V : B} (q : F.obj U ⟶ V) :
    c.map (adj.homEquiv U V q) ≫ e.right.hom.app V =
      adj'.homEquiv _ _ (e.left.inv.app U ≫ d.map q) := by
  simp only [adj.homEquiv_unit, adj'.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn := e.right.hom.naturality q
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [← e.unit U]
  simp only [Category.assoc, ← G'.map_comp_assoc,
    Iso.hom_inv_id_app]
  simp

private theorem coefficientLeftProjection
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (c : A ⥤ A') (d : B ⥤ B')
    (e : ExchangeProjectionAdjunctionComparison adj adj' c d)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (tA : TA ⋙ c ≅ c.prod c ⋙ TA') (tB : TB ⋙ d ≅ d.prod d ⋙ TB')
    (nu : ∀ U V : B, TA.obj (G.obj U, G.obj V) ⟶ G.obj (TB.obj (U, V)))
    (nu' : ∀ U V : B', TA'.obj (G'.obj U, G'.obj V) ⟶ G'.obj (TB'.obj (U, V)))
    (nu'_natural : ∀ {U V : B'} (a : U ⟶ V) (N : B'),
      TA'.map (Prod.mkHom (G'.map a) (𝟙 _)) ≫ nu' V N =
        nu' U N ≫ G'.map (TB'.map (Prod.mkHom a (𝟙 N))))
    (square : ∀ U V : B,
      c.map (nu U V) ≫ e.right.hom.app _ ≫ G'.map (tB.hom.app (U, V)) =
        tA.hom.app (G.obj U, G.obj V) ≫
          TA'.map (Prod.mkHom (e.right.hom.app U) (e.right.hom.app V)) ≫
            nu' (d.obj U) (d.obj V))
    (M : A) (N : B)
    (q : F.obj (TA.obj (M, G.obj N)) ⟶ TB.obj (F.obj M, N))
    (q' : F'.obj (TA'.obj (c.obj M, G'.obj (d.obj N))) ⟶
      TB'.obj (F'.obj (c.obj M), d.obj N))
    (hq : adj.homEquiv _ _ q =
      TA.map (Prod.mkHom (adj.unit.app M) (𝟙 _)) ≫ nu (F.obj M) N)
    (hq' : adj'.homEquiv _ _ q' =
      TA'.map (Prod.mkHom (adj'.unit.app (c.obj M)) (𝟙 _)) ≫
        nu' (F'.obj (c.obj M)) (d.obj N)) :
    d.map q ≫ tB.hom.app (F.obj M, N) ≫
        TB'.map (Prod.mkHom (e.left.hom.app M) (𝟙 _)) =
      e.left.hom.app _ ≫ F'.map
        (tA.hom.app (M, G.obj N) ≫ TA'.map
          (Prod.mkHom (𝟙 _) (e.right.hom.app N))) ≫ q' := by
  apply (cancel_epi (e.left.inv.app _)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (adj'.homEquiv _ _).injective
  rw [adj'.homEquiv_naturality_right, adj'.homEquiv_naturality_right,
    ← coefficientHomEquiv adj adj' c d e q, hq]
  rw [adj'.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  rw [hq']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (square (F.obj M) N)]
  have ht := tA.hom.naturality (Prod.mkHom (adj.unit.app M) (𝟙 (G.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map] at ht
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id] at ht
  rw [reassoc_of% ht]
  have hn := nu'_natural (e.left.hom.app M) (d.obj N)
  dsimp only [Functor.comp_obj] at hn
  rw [← hn]
  simp only [← TA'.map_comp_assoc, prod_comp, Category.id_comp, Category.comp_id,
    e.unit M]

private theorem inverseTensorSquare
    {F : A ⥤ B} {F' : A' ⥤ B'} (c : A ⥤ A') (d : B ⥤ B')
    (e : F ⋙ d ≅ c ⋙ F')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (tA : TA ⋙ c ≅ c.prod c ⋙ TA') (tB : TB ⋙ d ≅ d.prod d ⋙ TB')
    (M N : A) (mu : F.obj (TA.obj (M, N)) ≅ TB.obj (F.obj M, F.obj N))
    (mu' : F'.obj (TA'.obj (c.obj M, c.obj N)) ≅
      TB'.obj (F'.obj (c.obj M), F'.obj (c.obj N)))
    (hs : d.map mu.hom ≫ tB.hom.app (F.obj M, F.obj N) ≫
      TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
        e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu'.hom) :
    d.map mu.inv ≫ e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) =
      tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) ≫ mu'.inv := by
  apply (cancel_epi (d.map mu.hom)).mp
  simp only [← d.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% hs]
  simp

private theorem tensorPullback_naturality (F : A ⥤ B)
    (TA : A ⥤ A ⥤ A) (TB : B ⥤ B ⥤ B)
    (mu : (Functor.postcompose₂.obj F).obj TA ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj TB)
    {U V : A} (a : U ⟶ V) (N : A) :
    F.map ((Functor.uncurry.obj TA).map (Prod.mkHom a (𝟙 N))) ≫ (mu.app V).app N =
      (mu.app U).app N ≫
        (Functor.uncurry.obj TB).map (Prod.mkHom (F.map a) (𝟙 _)) := by
  change F.map (((TA.map a).app N) ≫ (TA.obj V).map (𝟙 N)) ≫ (mu.app V).app N =
    (mu.app U).app N ≫
      ((TB.map (F.map a)).app (F.obj N) ≫ (TB.obj (F.obj V)).map (𝟙 _))
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  exact congrArg (fun t ↦ t.app N) (mu.naturality a)

end ProjectionTransport

section ProperCoefficientTransport
attribute [local irreducible] properTensorPullback

private theorem properCoefficientProjection
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {V : ∀ X, B X ⥤ B' X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (A' : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S' T' Q)
    (C : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (square : ∀ M N : B Y,
      (V X).map (((properTensorPullback A f).hom.app M).app N) ≫
        (t X).hom.app ((S.pull f).obj M, (S.pull f).obj N) ≫
        (Functor.uncurry.obj (T' X)).map
          (Prod.mkHom ((C.directAdjunction f).left.hom.app M)
            ((C.directAdjunction f).left.hom.app N)) =
      (C.directAdjunction f).left.hom.app (((T Y).obj M).obj N) ≫
        (S'.pull f).map ((t Y).hom.app (M, N)) ≫
        (((properTensorPullback A' f).hom.app ((V Y).obj M)).app ((V Y).obj N)))
    (K : B X) (L : B Y) :
    (V Y).map (compactSupportProperProjection A f K L) ≫
        (properTarget C t f K L).hom =
      (properSource C t f K L).hom ≫
        compactSupportProperProjection A' f ((V X).obj K) ((V Y).obj L) := by
  let mu := properTensorPullback A f
  let mu' := properTensorPullback A' f
  have hn : ∀ {U V : B' Y}
      (a : U ⟶ V) (N : B' Y),
      (S'.pull f).map ((Functor.uncurry.obj (T' Y)).map
          (Prod.mkHom a (𝟙 N))) ≫ (mu'.hom.app V).app N =
        (mu'.hom.app U).app N ≫
          (Functor.uncurry.obj (T' X)).map
            (Prod.mkHom ((S'.pull f).map a) (𝟙 _)) := by
    intro U V a N
    exact tensorPullback_naturality _ _ _ mu'.hom a N
  have hp := (S.pullDirectAdjunction f).map_rightAdjointProjectionMap_app_app_comp_counit
    mu.hom K L
  have hp' := (S'.pullDirectAdjunction f).map_rightAdjointProjectionMap_app_app_comp_counit
    mu'.hom ((V X).obj K)
      ((V Y).obj L)
  have h := coefficientProjection (S.pullDirectAdjunction f)
    (S'.pullDirectAdjunction f)
    (V Y)
    (V X)
    (C.directAdjunction f)
    (Functor.uncurry.obj (T Y))
    (Functor.uncurry.obj (T X))
    (Functor.uncurry.obj (T' Y))
    (Functor.uncurry.obj (T' X))
    (t Y) (t X)
    (fun M N ↦ (mu.hom.app M).app N) (fun M N ↦ (mu'.hom.app M).app N)
    hn square K L
    (((S.pullDirectAdjunction f).rightAdjointProjectionMap mu.hom).app K |>.app L)
    (((S'.pullDirectAdjunction f).rightAdjointProjectionMap mu'.hom).app
      ((V X).obj K) |>.app
        ((V Y).obj L))
    (by simpa using hp) (by simpa using hp')
  simpa only [properProjection_eq, properTarget, properSource,
    ProjectionCoefficientTransport.inner, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Functor.map_comp,
    Category.assoc, Functor.uncurry_obj_obj, Functor.comp_obj, mu, mu'] using h

end ProperCoefficientTransport

section NormalizeCompactProjection
universe cx cz cy hx hz hy

private theorem normalizedCompactProjection
    {X : Type cx} [Category.{hx} X] {Z : Type cz} [Category.{hz} Z]
    {Y : Type cy} [Category.{hy} Y]
    {J J₀ : X ⥤ Z} {F F₀ : Y ⥤ X} {P P₀ : Y ⥤ Z} {R R₀ : Z ⥤ Y}
    {U U₀ : X ⥤ Y}
    {TX TX₀ : X ⥤ X ⥤ X} {TZ TZ₀ : Z ⥤ Z ⥤ Z} {TY TY₀ : Y ⥤ Y ⥤ Y}
    (adj : P ⊣ R) (adj₀ : P₀ ⊣ R₀)
    (mu : (Functor.postcompose₂.obj P₀).obj TY₀ ≅
      (((Functor.whiskeringLeft₂ _).obj P₀).obj P₀).obj TZ₀)
    (gamma : (((Functor.whiskeringLeft₂ _).obj J₀).obj P₀).obj TZ₀ ≅
      (Functor.postcompose₂.obj J₀).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 X)).obj F₀).obj TX₀))
    (sigma : U₀ ≅ J₀ ⋙ R₀)
    (hJ : J₀ = J) (hF : F₀ = F) (hP : P₀ = P) (hR : R₀ = R) (hU : U₀ = U)
    (hX : TX₀ = TX) (hZ : TZ₀ = TZ) (hY : TY₀ = TY) (ha : HEq adj₀ adj)
    (K : X) (N : Y) :
    eqToHom (by rw [hU, hY]; rfl) ≫
        (((Functor.whiskerRight sigma.hom TY₀ ≫
          compactificationProjectionFromData J₀ F₀ P₀ R₀ adj₀ TX₀ TZ₀ TY₀ mu gamma ≫
          (Functor.postcompose₂.map sigma.inv).app
            ((((Functor.whiskeringLeft₂ _).obj (𝟭 X)).obj F₀).obj TX₀)).app K).app N) ≫
        eqToHom (by rw [hU, hX, hF]) =
      (TY.map ((eqToIso hU.symm ≪≫ sigma ≪≫
        eqToIso (by rw [hJ, hR])).hom.app K)).app N ≫
      ((adj.rightAdjointProjectionMap (eqToIso (by rw [hP, hY]) ≪≫ mu ≪≫
        eqToIso (by rw [hP, hZ])).hom).app (J.obj K)).app N ≫
      R.map ((eqToIso (by rw [hJ, hP, hZ]; rfl) ≪≫ (gamma.app K).app N ≪≫
        eqToIso (by rw [hJ, hF, hX])).hom) ≫
      (eqToIso hU.symm ≪≫ sigma ≪≫ eqToIso (by rw [hJ, hR])).inv.app
        (((TX.obj K).obj (F.obj N))) := by
  subst J₀ F₀ P₀ R₀ U₀ TX₀ TZ₀ TY₀
  cases eq_of_heq ha
  simp [compactificationProjectionFromData, Category.assoc]

end NormalizeCompactProjection

section CompactCoefficientTransport
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
  {V : ∀ X, B X ⥤ B' X}

variable {T : ∀ X, B X ⥤ B X ⥤ B X}
  {Q : SixFunctorCompactifiedSquare D}

private def coordinateTensor (A : SixFunctorExchangeData S T Q) :
    (Functor.postcompose₂.obj (S.pull Q.p)).obj (T Q.Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (S.pull Q.p)).obj (S.pull Q.p)).obj (T Q.Z) :=
  eqToIso (by rw [A.tensorY, A.properPull]) ≪≫ A.stage.tensorPullback ≪≫
    eqToIso (by rw [A.tensorBar, A.properPull])

private theorem coordinateTensor_heq (A : SixFunctorExchangeData S T Q)
    (M N : B Q.Y) :
    HEq (((coordinateTensor A).hom.app M).app N)
      ((A.stage.tensorPullback.hom.app M).app N) := by
  exact normalizedTensorPullback_heq A.stage.tensorPullback
    A.properPull A.tensorBar A.tensorY M N

private def coordinateOpen (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    ((T Q.Z).obj ((S.openExtension Q.i Q.open_i).obj K)).obj ((S.pull Q.p).obj N) ≅
      (S.openExtension Q.i Q.open_i).obj (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) :=
  eqToIso (by rw [A.tensorBar, A.openExtension, A.properPull]; rfl) ≪≫
    (A.stage.openProjection.app K).app N ≪≫
      eqToIso (by rw [A.tensorX, A.pull, A.openExtension]; rfl)

private def coordinateSupport (A : SixFunctorExchangeData S T Q) :
    S.support Q.f Q.compactification ≅ S.openExtension Q.i Q.open_i ⋙ S.direct Q.p :=
  eqToIso A.compactSupport.symm ≪≫ A.stage.compactSupportIdentification ≪≫
    eqToIso (by rw [A.openExtension, A.properPush])

private theorem normalizedIso_heq
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {F F₀ G G₀ : A ⥤ B} (e : F₀ ≅ G₀) (hF : F₀ = F) (hG : G₀ = G) :
    HEq (eqToIso hF.symm ≪≫ e ≪≫ eqToIso hG) e := by
  subst F₀ G₀
  simp

private theorem coordinateSupport_eq (A : SixFunctorExchangeData S T Q) :
    coordinateSupport A = sixFunctorFactoredSupportIdentification S
      Q.i Q.p Q.open_i Q.proper_p Q.f Q.factorization := by
  exact eq_of_heq ((normalizedIso_heq A.stage.compactSupportIdentification
    A.compactSupport (by rw [A.openExtension, A.properPush])).trans
      A.compactSupportNormalization)

private theorem coordinateOpen_inv (A : SixFunctorExchangeData S T Q)
    (K : B Q.X) (N : B Q.Y) :
    (coordinateOpen A K N).inv =
      sixFunctorOpenProjectionInverse S T Q A.openTensorPullback K N := by
  apply eq_of_heq
  simpa only [coordinateOpen, Iso.trans_inv, Iso.app_inv, eqToIso.inv, Category.assoc,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff] using A.openProjectionNormalization K N

private theorem coordinateProjection (A : SixFunctorExchangeData S T Q)
    (K : B Q.X) (N : B Q.Y) :
    A.projectionComponent K N =
      ((T Q.Y).map ((coordinateSupport A).hom.app K)).app N ≫
        (((S.pullDirectAdjunction Q.p).rightAdjointProjectionMap
          (coordinateTensor A).hom).app ((S.openExtension Q.i Q.open_i).obj K)).app N ≫
        (S.direct Q.p).map (coordinateOpen A K N).hom ≫
        (coordinateSupport A).inv.app (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) := by
  exact normalizedCompactProjection (S.pullDirectAdjunction Q.p) A.stage.properAdjunction
    A.stage.tensorPullback A.stage.openProjection A.stage.compactSupportIdentification
    A.openExtension A.pull A.properPull A.properPush A.compactSupport
    A.tensorX A.tensorBar A.tensorY A.properAdjunction K N

private theorem factoredSupportSquare
    (C : SixFunctorCoefficientComparison S S' V)
    {X Z Y : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (hi : IsOpenImmersion i.hom.left) (hp : IsProper p.hom.left)
    (f : X ⟶ Y) (h : f = i ≫ p) (K : B X) :
    (V Y).map ((sixFunctorFactoredSupportIdentification S i p hi hp f h).hom.app K) ≫
        (C.directAdjunction p).right.hom.app ((S.openExtension i hi).obj K) ≫
        (S'.direct p).map ((C.openExtension i hi).hom.app K) =
      (C.supportAdjunction f (sixFunctorFactorCompactification i p hi hp f h)).left.hom.app K ≫
        (sixFunctorFactoredSupportIdentification S' i p hi hp f h).hom.app ((V X).obj K) := by
  subst f
  let := hp
  simp only [sixFunctorFactoredSupportIdentification, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (C.properIdentity p ((S.openExtension i hi).obj K))]
  have hn := (C.supportAdjunction p (.ofIsProper p.hom.left)).left.hom.naturality
    ((S.openIdentification i hi).hom.app K)
  change (V Y).map ((S.support p (.ofIsProper p.hom.left)).map
      ((S.openIdentification i hi).hom.app K)) ≫ _ = _ at hn
  rw [reassoc_of% hn]
  have hn' := (S'.properIdentity p).hom.naturality ((C.openExtension i hi).hom.app K)
  change (S'.support p (.ofIsProper p.hom.left)).map _ ≫ _ = _ at hn'
  dsimp only [Functor.comp_obj] at hn'
  rw [← hn']
  rw [← (S'.support p (.ofIsProper p.hom.left)).map_comp_assoc]
  rw [C.openIdentification i hi K]
  rw [(S'.support p (.ofIsProper p.hom.left)).map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (C.composition i p (sixFunctorOpenCompactification i hi)
    (.ofIsProper p.hom.left)
      (sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl) K)]

private def pullFactor (S : SixFunctorPushStage D B) (Q : SixFunctorCompactifiedSquare D) :
    S.pull Q.f ≅ S.pull Q.p ⋙ S.pull Q.i :=
  eqToIso (congrArg (fun e ↦ S.pull e) Q.factorization) ≪≫ S.pullComposition Q.i Q.p

private theorem coordinateOpen_inv_eq (A : SixFunctorExchangeData S T Q)
    (K : B Q.X) (N : B Q.Y) :
    (coordinateOpen A K N).inv =
      (S.openExtension Q.i Q.open_i).map
        ((Functor.uncurry.obj (T Q.X)).map
          (Prod.mkHom (𝟙 K) ((pullFactor S Q).hom.app N))) ≫
      (((S.openAdjunction Q.i Q.open_i).projectionMap (S.pull Q.i) (T Q.X) (T Q.Z)
        A.openTensorPullback.inv).app K).app ((S.pull Q.p).obj N) := by
  rw [coordinateOpen_inv, Adjunction.projectionMap_app_app]
  simp only [sixFunctorOpenProjectionInverse, pullFactor, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rfl

private theorem pullFactorSquare (C : SixFunctorCoefficientComparison S S' V)
    (Q : SixFunctorCompactifiedSquare D) (N : B Q.Y) :
    (V Q.X).map ((pullFactor S Q).hom.app N) ≫
        (C.directAdjunction Q.i).left.hom.app ((S.pull Q.p).obj N) ≫
        (S'.pull Q.i).map ((C.directAdjunction Q.p).left.hom.app N) =
      (C.directAdjunction Q.f).left.hom.app N ≫
        (pullFactor S' Q).hom.app ((V Q.Y).obj N) := by
  have gen {X Z Y : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
      (f : X ⟶ Y) (h : f = i ≫ p) (N : B Y) :
      (V X).map (((eqToIso (congrArg (fun e ↦ S.pull e) h) ≪≫
        S.pullComposition i p).hom.app N)) ≫
        (C.directAdjunction i).left.hom.app ((S.pull p).obj N) ≫
        (S'.pull i).map ((C.directAdjunction p).left.hom.app N) =
      (C.directAdjunction f).left.hom.app N ≫
        ((eqToIso (congrArg (fun e ↦ S'.pull e) h) ≪≫
          S'.pullComposition i p).hom.app ((V Y).obj N)) := by
    subst f
    simpa using C.pullComposition i p N
  exact gen Q.i Q.p Q.f Q.factorization N

private theorem coefficientOpenSquare
    {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (C : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    (square : ∀ M N : B Q.Z,
      (V Q.X).map ((A.openTensorPullback.hom.app M).app N) ≫
        (t Q.X).hom.app ((S.pull Q.i).obj M, (S.pull Q.i).obj N) ≫
        (Functor.uncurry.obj (T' Q.X)).map
          (Prod.mkHom ((C.directAdjunction Q.i).left.hom.app M)
            ((C.directAdjunction Q.i).left.hom.app N)) =
      (C.directAdjunction Q.i).left.hom.app (((T Q.Z).obj M).obj N) ≫
        (S'.pull Q.i).map ((t Q.Z).hom.app (M, N)) ≫
        ((A'.openTensorPullback.hom.app ((V Q.Z).obj M)).app ((V Q.Z).obj N)))
    (K : B Q.X) (N : B Q.Y) :
    (V Q.Z).map (coordinateOpen A K N).hom ≫
        (C.openExtension Q.i Q.open_i).hom.app _ ≫
        (S'.openExtension Q.i Q.open_i).map (inner C t Q.f K N).hom =
      (t Q.Z).hom.app ((S.openExtension Q.i Q.open_i).obj K, (S.pull Q.p).obj N) ≫
        (Functor.uncurry.obj (T' Q.Z)).map
          (Prod.mkHom ((C.openExtension Q.i Q.open_i).hom.app K)
            ((C.directAdjunction Q.p).left.hom.app N)) ≫
        (coordinateOpen A' ((V Q.X).obj K) ((V Q.Y).obj N)).hom := by
  let J := S.openExtension Q.i Q.open_i
  let J' := S'.openExtension Q.i Q.open_i
  let P := S.pull Q.i
  let P' := S'.pull Q.i
  let q := (S.openAdjunction Q.i Q.open_i).projectionMap P (T Q.X) (T Q.Z)
    A.openTensorPullback.inv
  let q' := (S'.openAdjunction Q.i Q.open_i).projectionMap P' (T' Q.X) (T' Q.Z)
    A'.openTensorPullback.inv
  have hs : ∀ U W : B Q.Z,
      (V Q.X).map ((A.openTensorPullback.inv.app U).app W) ≫
        (C.openAdjunction Q.i Q.open_i).right.hom.app _ ≫
        P'.map ((t Q.Z).hom.app (U, W)) =
      (t Q.X).hom.app (P.obj U, P.obj W) ≫
        (Functor.uncurry.obj (T' Q.X)).map
          (Prod.mkHom ((C.openAdjunction Q.i Q.open_i).right.hom.app U)
            ((C.openAdjunction Q.i Q.open_i).right.hom.app W)) ≫
        ((A'.openTensorPullback.inv.app ((V Q.Z).obj U)).app ((V Q.Z).obj W)) := by
    intro U W
    rw [C.openAdjunction_right]
    exact inverseTensorSquare (V Q.Z) (V Q.X) (C.directAdjunction Q.i).left
      (Functor.uncurry.obj (T Q.Z)) (Functor.uncurry.obj (T Q.X))
      (Functor.uncurry.obj (T' Q.Z)) (Functor.uncurry.obj (T' Q.X)) (t Q.Z) (t Q.X)
      U W ((A.openTensorPullback.app U).app W)
      ((A'.openTensorPullback.app ((V Q.Z).obj U)).app ((V Q.Z).obj W)) (square U W)
  have hn : ∀ {U W : B' Q.Z} (a : U ⟶ W) (L : B' Q.Z),
      (Functor.uncurry.obj (T' Q.X)).map (Prod.mkHom (P'.map a) (𝟙 _)) ≫
          (A'.openTensorPullback.inv.app W).app L =
        (A'.openTensorPullback.inv.app U).app L ≫
          P'.map ((Functor.uncurry.obj (T' Q.Z)).map (Prod.mkHom a (𝟙 L))) := by
    intro U W a L
    simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id]
    exact congrArg (fun z ↦ z.app L) (A'.openTensorPullback.inv.naturality a)
  have hq (L : B Q.Z) := coefficientLeftProjection
    (S.openAdjunction Q.i Q.open_i) (S'.openAdjunction Q.i Q.open_i)
    (V Q.X) (V Q.Z) (C.openAdjunction Q.i Q.open_i)
    (Functor.uncurry.obj (T Q.X)) (Functor.uncurry.obj (T Q.Z))
    (Functor.uncurry.obj (T' Q.X)) (Functor.uncurry.obj (T' Q.Z)) (t Q.X) (t Q.Z)
    (fun U W ↦ (A.openTensorPullback.inv.app U).app W)
    (fun U W ↦ (A'.openTensorPullback.inv.app U).app W) hn hs K L
    ((q.app K).app L) ((q'.app ((V Q.X).obj K)).app ((V Q.Z).obj L))
    (by
      rw [Adjunction.projectionMap_app_app]
      change ((S.openAdjunction Q.i Q.open_i).homEquiv
        (((T Q.X).obj K).obj (P.obj L)) (((T Q.Z).obj (J.obj K)).obj L))
          (((S.openAdjunction Q.i Q.open_i).homEquiv
            (((T Q.X).obj K).obj (P.obj L)) (((T Q.Z).obj (J.obj K)).obj L)).symm _) = _
      rw [Equiv.apply_symm_apply]
      simp [P, Adjunction.projectionMapTranspose])
    (by
      rw [Adjunction.projectionMap_app_app]
      change ((S'.openAdjunction Q.i Q.open_i).homEquiv
        (((T' Q.X).obj ((V Q.X).obj K)).obj (P'.obj ((V Q.Z).obj L)))
        (((T' Q.Z).obj (J'.obj ((V Q.X).obj K))).obj ((V Q.Z).obj L)))
          (((S'.openAdjunction Q.i Q.open_i).homEquiv
            (((T' Q.X).obj ((V Q.X).obj K)).obj (P'.obj ((V Q.Z).obj L)))
            (((T' Q.Z).obj (J'.obj ((V Q.X).obj K))).obj ((V Q.Z).obj L))).symm _) = _
      rw [Equiv.apply_symm_apply]
      simp [P', Adjunction.projectionMapTranspose])
  simp only [C.openAdjunction_left, C.openAdjunction_right] at hq
  let TX' := Functor.uncurry.obj (T' Q.X)
  let TZ' := Functor.uncurry.obj (T' Q.Z)
  have hqN := hq ((S.pull Q.p).obj N)
  have hqn : J'.map (TX'.map (Prod.mkHom (𝟙 ((V Q.X).obj K))
      (P'.map ((C.directAdjunction Q.p).left.hom.app N)))) ≫
        (q'.app ((V Q.X).obj K)).app ((S'.pull Q.p).obj ((V Q.Y).obj N)) =
      (q'.app ((V Q.X).obj K)).app ((V Q.Z).obj ((S.pull Q.p).obj N)) ≫
        TZ'.map (Prod.mkHom (𝟙 (J'.obj ((V Q.X).obj K)))
          ((C.directAdjunction Q.p).left.hom.app N)) := by
    simpa [TX', TZ', J', P'] using
      (q'.app ((V Q.X).obj K)).naturality ((C.directAdjunction Q.p).left.hom.app N)
  have hqFinal : (V Q.Z).map ((q.app K).app ((S.pull Q.p).obj N)) ≫
      (t Q.Z).hom.app (J.obj K, (S.pull Q.p).obj N) ≫
      TZ'.map (Prod.mkHom ((C.openExtension Q.i Q.open_i).hom.app K)
        ((C.directAdjunction Q.p).left.hom.app N)) =
    (C.openExtension Q.i Q.open_i).hom.app _ ≫
      J'.map ((t Q.X).hom.app (K, P.obj ((S.pull Q.p).obj N)) ≫
        TX'.map (Prod.mkHom (𝟙 ((V Q.X).obj K))
          ((C.directAdjunction Q.i).left.hom.app ((S.pull Q.p).obj N) ≫
            P'.map ((C.directAdjunction Q.p).left.hom.app N)))) ≫
      (q'.app ((V Q.X).obj K)).app ((S'.pull Q.p).obj ((V Q.Y).obj N)) := by
    have hh := congrArg (fun z ↦ z ≫ TZ'.map
      (Prod.mkHom (𝟙 (J'.obj ((V Q.X).obj K)))
        ((C.directAdjunction Q.p).left.hom.app N))) hqN
    simp only [Category.assoc] at hh
    rw [← hqn] at hh
    dsimp only [J, J', P, P', TX', TZ'] at hh ⊢
    simpa only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
      prod_comp, Category.id_comp, Category.comp_id, Functor.comp_obj] using hh
  have ht := (t Q.X).hom.naturality
    (Prod.mkHom (𝟙 K) ((pullFactor S Q).hom.app N))
  dsimp only [Functor.comp_map, Functor.prod_map] at ht
  simp only [CategoryTheory.Functor.map_id] at ht
  have hf := pullFactorSquare C Q N
  apply (cancel_epi ((V Q.Z).map (coordinateOpen A K N).inv)).mp
  apply (cancel_mono (coordinateOpen A' ((V Q.X).obj K) ((V Q.Y).obj N)).inv).mp
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  symm
  rw [coordinateOpen_inv_eq, coordinateOpen_inv_eq]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [J, J', P, P', TX', TZ', q, q'] at hqFinal
  rw [hqFinal]
  have hj := (C.openExtension Q.i Q.open_i).hom.naturality
    ((Functor.uncurry.obj (T Q.X)).map
      (Prod.mkHom (𝟙 K) ((pullFactor S Q).hom.app N)))
  dsimp only [Functor.comp_map] at hj
  rw [reassoc_of% hj]
  simp only [ProjectionCoefficientTransport.inner, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.prod_hom,
    Iso.refl_hom, ← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht]
  simp only [← Functor.map_comp, prod_comp, Category.comp_id, hf,
    Functor.uncurry_obj_obj]

private theorem uncurryMapLeft {A : Type v} [Category.{w} A]
    (T : A ⥤ A ⥤ A) {M M' : A} (a : M ⟶ M') (N : A) :
    (Functor.uncurry.obj T).map (Prod.mkHom a (𝟙 N)) = (T.map a).app N := by
  simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem coefficientCompactSquare
    {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (C : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    (square : ∀ M N : B Q.Y,
      (V Q.Z).map (((coordinateTensor A).hom.app M).app N) ≫
        (t Q.Z).hom.app ((S.pull Q.p).obj M, (S.pull Q.p).obj N) ≫
        (Functor.uncurry.obj (T' Q.Z)).map
          (Prod.mkHom ((C.directAdjunction Q.p).left.hom.app M)
            ((C.directAdjunction Q.p).left.hom.app N)) =
      (C.directAdjunction Q.p).left.hom.app (((T Q.Y).obj M).obj N) ≫
        (S'.pull Q.p).map ((t Q.Y).hom.app (M, N)) ≫
        (((coordinateTensor A').hom.app ((V Q.Y).obj M)).app ((V Q.Y).obj N)))
    (ho : ∀ (K : B Q.X) (N : B Q.Y),
      (V Q.Z).map (coordinateOpen A K N).hom ≫
          (C.openExtension Q.i Q.open_i).hom.app _ ≫
          (S'.openExtension Q.i Q.open_i).map (inner C t Q.f K N).hom =
        (t Q.Z).hom.app ((S.openExtension Q.i Q.open_i).obj K, (S.pull Q.p).obj N) ≫
          (Functor.uncurry.obj (T' Q.Z)).map
            (Prod.mkHom ((C.openExtension Q.i Q.open_i).hom.app K)
              ((C.directAdjunction Q.p).left.hom.app N)) ≫
          (coordinateOpen A' ((V Q.X).obj K) ((V Q.Y).obj N)).hom)
    (K : B Q.X) (N : B Q.Y) :
    (V Q.Y).map (A.projectionComponent K N) ≫
        (target C t Q.f Q.compactification K N).hom =
      (source C t Q.f Q.compactification K N).hom ≫
        A'.projectionComponent ((V Q.X).obj K) ((V Q.Y).obj N) := by
  let J := S.openExtension Q.i Q.open_i
  let J' := S'.openExtension Q.i Q.open_i
  let R := S.direct Q.p
  let R' := S'.direct Q.p
  let Y' := Functor.uncurry.obj (T' Q.Y)
  let Z' := Functor.uncurry.obj (T' Q.Z)
  let p := (S.pullDirectAdjunction Q.p).rightAdjointProjectionMap (coordinateTensor A).hom
  let p' := (S'.pullDirectAdjunction Q.p).rightAdjointProjectionMap (coordinateTensor A').hom
  let j := (C.openExtension Q.i Q.open_i).app K
  let n := (C.directAdjunction Q.p).left.app N
  let s := coordinateSupport A
  let s' := coordinateSupport A'
  let e1 := (t Q.Y).app (R.obj (J.obj K), N) ≪≫
    Y'.mapIso (Iso.prod ((C.directAdjunction Q.p).right.app (J.obj K) ≪≫ R'.mapIso j)
      (Iso.refl _))
  let e2 := (C.directAdjunction Q.p).right.app _ ≪≫ R'.mapIso
    ((t Q.Z).app (J.obj K, (S.pull Q.p).obj N) ≪≫ Z'.mapIso (Iso.prod j n))
  let e3 := (C.directAdjunction Q.p).right.app _ ≪≫ R'.mapIso
    ((C.openExtension Q.i Q.open_i).app _ ≪≫
      J'.mapIso (inner C t Q.f K N))
  have hs (U : B Q.X) :
      (V Q.Y).map (s.hom.app U) ≫
          (C.directAdjunction Q.p).right.hom.app (J.obj U) ≫
          R'.map ((C.openExtension Q.i Q.open_i).hom.app U) =
        (C.supportAdjunction Q.f Q.compactification).left.hom.app U ≫
          s'.hom.app ((V Q.X).obj U) := by
    dsimp only [s, s']
    rw [coordinateSupport_eq, coordinateSupport_eq]
    exact factoredSupportSquare C Q.i Q.p Q.open_i Q.proper_p Q.f Q.factorization U
  have h0 : (V Q.Y).map (((T Q.Y).map (s.hom.app K)).app N) ≫ e1.hom =
      (source C t Q.f Q.compactification K N).hom ≫
        ((T' Q.Y).map (s'.hom.app ((V Q.X).obj K))).app ((V Q.Y).obj N) := by
    rw [← uncurryMapLeft (T Q.Y) (s.hom.app K) N,
      ← uncurryMapLeft (T' Q.Y) (s'.hom.app ((V Q.X).obj K)) ((V Q.Y).obj N)]
    have ht := (t Q.Y).hom.naturality (Prod.mkHom (s.hom.app K) (𝟙 N))
    dsimp only [Functor.comp_map, Functor.prod_map] at ht
    simp only [CategoryTheory.Functor.map_id] at ht
    simp only [e1, source, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Category.assoc]
    rw [reassoc_of% ht]
    have hsk := hs K
    dsimp only [Y', J, R, R', j] at hsk ⊢
    simp only [← Functor.map_comp, prod_comp, Category.comp_id]
    simpa only [Iso.app_hom] using congrArg
      (fun z ↦ (t Q.Y).hom.app ((S.support Q.f Q.compactification).obj K, N) ≫
        (Functor.uncurry.obj (T' Q.Y)).map (Prod.mkHom z (𝟙 ((V Q.Y).obj N)))) hsk
  have h1 : (V Q.Y).map ((p.app (J.obj K)).app N) ≫ e2.hom =
      e1.hom ≫ (p'.app (J'.obj ((V Q.X).obj K))).app ((V Q.Y).obj N) := by
    have hn := fun {U W : B' Q.Y} (a : U ⟶ W) (L : B' Q.Y) ↦
      tensorPullback_naturality (S'.pull Q.p) (T' Q.Y) (T' Q.Z)
        (coordinateTensor A').hom a L
    have hp := (S.pullDirectAdjunction Q.p).map_rightAdjointProjectionMap_app_app_comp_counit
      (coordinateTensor A).hom (J.obj K) N
    have hp' := (S'.pullDirectAdjunction Q.p).map_rightAdjointProjectionMap_app_app_comp_counit
      (coordinateTensor A').hom ((V Q.Z).obj (J.obj K)) ((V Q.Y).obj N)
    have h := coefficientProjection (S.pullDirectAdjunction Q.p)
      (S'.pullDirectAdjunction Q.p) (V Q.Y) (V Q.Z) (C.directAdjunction Q.p)
      (Functor.uncurry.obj (T Q.Y)) (Functor.uncurry.obj (T Q.Z))
      Y' Z' (t Q.Y) (t Q.Z)
      (fun M N ↦ ((coordinateTensor A).hom.app M).app N)
      (fun M N ↦ ((coordinateTensor A').hom.app M).app N)
      hn square (J.obj K) N ((p.app (J.obj K)).app N)
      ((p'.app ((V Q.Z).obj (J.obj K))).app ((V Q.Y).obj N))
      (by simpa [p] using hp)
      (by simpa [p', Z'] using hp')
    have hn' : Y'.map (Prod.mkHom (R'.map j.hom) (𝟙 ((V Q.Y).obj N))) ≫
        (p'.app (J'.obj ((V Q.X).obj K))).app ((V Q.Y).obj N) =
      (p'.app ((V Q.Z).obj (J.obj K))).app ((V Q.Y).obj N) ≫
        R'.map (Z'.map (Prod.mkHom j.hom (𝟙 ((S'.pull Q.p).obj ((V Q.Y).obj N))))) := by
      simpa [Y', Z', R', J, J'] using
        congrArg (fun z ↦ z.app ((V Q.Y).obj N)) (p'.naturality j.hom)
    simp only [e1, e2, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Functor.map_comp, Category.assoc]
    have hh := congrArg (fun z ↦ z ≫ R'.map
      (Z'.map (Prod.mkHom j.hom (𝟙 _)))) h
    have hny := congrArg (fun z ↦ (t Q.Y).hom.app (R.obj (J.obj K), N) ≫
      Y'.map (Prod.mkHom ((C.directAdjunction Q.p).right.hom.app (J.obj K))
        (𝟙 ((V Q.Y).obj N))) ≫ z) hn'
    dsimp only [J, J', R, R', Y', Z', j, n] at hh hny ⊢
    simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
      prod_comp, Category.comp_id, Category.id_comp, Iso.app_hom] at hh hny ⊢
    rw [hh]
    exact hny.symm
  have h2 : (V Q.Y).map (R.map (coordinateOpen A K N).hom) ≫ e3.hom =
      e2.hom ≫ R'.map (coordinateOpen A' ((V Q.X).obj K) ((V Q.Y).obj N)).hom := by
    have hn := (C.directAdjunction Q.p).right.hom.naturality (coordinateOpen A K N).hom
    dsimp only [Functor.comp_map] at hn
    simp only [e2, e3, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod_hom, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn]
    dsimp only [R', J', Z', j, n, J] at ⊢
    simp only [← Functor.map_comp, ho K N, Iso.app_hom]
    rfl
  have h3 : (V Q.Y).map (s.inv.app _) ≫
        (target C t Q.f Q.compactification K N).hom =
      e3.hom ≫ s'.inv.app
        (((T' Q.X).obj ((V Q.X).obj K)).obj ((S'.pull Q.f).obj ((V Q.Y).obj N))) := by
    have hh := hs (((T Q.X).obj K).obj ((S.pull Q.f).obj N))
    have hn := s'.inv.naturality (inner C t Q.f K N).hom
    dsimp only [Functor.comp_map] at hn
    simp only [target, e3, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    apply (cancel_epi ((V Q.Y).map (s.hom.app _))).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    dsimp only [J, J', R, R'] at hh hn ⊢
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hh, hn]
    simp
  rw [coordinateProjection A, coordinateProjection A']
  simp only [Functor.map_comp, Category.assoc]
  rw [h3, reassoc_of% h2, reassoc_of% h1, reassoc_of% h0]

end CompactCoefficientTransport

attribute [local irreducible] sfRationalTriangulationDatum sfIntegralConstructible
  ScalarLocalization.composition

private theorem properTensorPullback_heq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)]
    (M N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    HEq (((properTensorPullback H.integralExchange f).hom.app M).app N)
      ((canonicalIntegralPullbackTensor C.l E f.hom.left M N).hom) := by
  let : ∀ x : (compactSupportProperSquare f).Z.obj.left,
      Invertible (C.l : (compactSupportProperSquare f).Z.obj.left.residueField x) := by
    change ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)
    infer_instance
  let : ∀ y : (compactSupportProperSquare f).Y.obj.left,
      Invertible (C.l : (compactSupportProperSquare f).Y.obj.left.residueField y) := by
    change ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)
    infer_instance
  exact (normalizedTensorPullback_heq
    (H.integralExchange (compactSupportProperSquare f)).stage.tensorPullback
    (H.integralExchange (compactSupportProperSquare f)).properPull
    (H.integralExchange (compactSupportProperSquare f)).tensorBar
    (H.integralExchange (compactSupportProperSquare f)).tensorY M N).trans
      (H.integralTensorPullbackNormalization (compactSupportProperSquare f) M N)

private theorem properTensorPullback_rational_heq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)]
    (M N : sfRationalConstructibleCategory C.l E Y.obj.left) :
    HEq (((properTensorPullback H.rationalExchange f).hom.app M).app N)
      ((canonicalRationalPullbackTensor C.l E f.hom.left M N).hom) := by
  let : ∀ x : (compactSupportProperSquare f).Z.obj.left,
      Invertible (C.l : (compactSupportProperSquare f).Z.obj.left.residueField x) := by
    change ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)
    infer_instance
  let : ∀ y : (compactSupportProperSquare f).Y.obj.left,
      Invertible (C.l : (compactSupportProperSquare f).Y.obj.left.residueField y) := by
    change ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)
    infer_instance
  exact (normalizedTensorPullback_heq
    (H.rationalExchange (compactSupportProperSquare f)).stage.tensorPullback
    (H.rationalExchange (compactSupportProperSquare f)).properPull
    (H.rationalExchange (compactSupportProperSquare f)).tensorBar
    (H.rationalExchange (compactSupportProperSquare f)).tensorY M N).trans
      (H.rationalTensorPullbackNormalization (compactSupportProperSquare f) M N)

attribute [local irreducible] properTensorPullback

attribute [local irreducible] constructibleIntegralTensor rationalDerivedTensor
  constructibleIntegralPullback rationalDerivedPullback canonicalIntegralPullbackTensor
  canonicalRationalPullbackTensor sfRationalConstructibleLocalization

private theorem rationalProperTensorSquare
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)]
    (M N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (sfRationalConstructibleLocalization C.l E X.obj.left).map
        (((properTensorPullback H.integralExchange f).hom.app M).app N) ≫
      (rationalProjectionTensorComparison H X).hom.app
        ((H.integral.pull f).obj M, (H.integral.pull f).obj N) ≫
      (Functor.uncurry.obj (H.rationalTensor X)).map
        (Prod.mkHom ((H.rationalization.directAdjunction f).left.hom.app M)
          ((H.rationalization.directAdjunction f).left.hom.app N)) =
    (H.rationalization.directAdjunction f).left.hom.app
        (((H.integralTensor Y).obj M).obj N) ≫
      (H.rational.pull f).map ((rationalProjectionTensorComparison H Y).hom.app (M, N)) ≫
      (((properTensorPullback H.rationalExchange f).hom.app
        ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj M)).app
          ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj N)) := by
  exact rationalProjectionPullTensorSquare H f (properTensorPullback H.integralExchange f)
    (properTensorPullback H.rationalExchange f) M N (properTensorPullback_heq H f M N)
    (properTensorPullback_rational_heq H f _ _)

private theorem rationalOpenTensorSquare
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (Q : SixFunctorCompactifiedSquare D)
    [∀ x : Q.X.obj.left, Invertible (C.l : Q.X.obj.left.residueField x)]
    [∀ y : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField y)]
    (M N : sfIntegralConstructibleCategory C.l E Q.Z.obj.left) :
    (sfRationalConstructibleLocalization C.l E Q.X.obj.left).map
        ((((H.integralExchange Q).openTensorPullback).hom.app M).app N) ≫
      (rationalProjectionTensorComparison H Q.X).hom.app
        ((H.integral.pull Q.i).obj M, (H.integral.pull Q.i).obj N) ≫
      (Functor.uncurry.obj (H.rationalTensor Q.X)).map
        (Prod.mkHom ((H.rationalization.directAdjunction Q.i).left.hom.app M)
          ((H.rationalization.directAdjunction Q.i).left.hom.app N)) =
    (H.rationalization.directAdjunction Q.i).left.hom.app
        (((H.integralTensor Q.Z).obj M).obj N) ≫
      (H.rational.pull Q.i).map ((rationalProjectionTensorComparison H Q.Z).hom.app (M, N)) ≫
      ((((H.rationalExchange Q).openTensorPullback).hom.app
        ((sfRationalConstructibleLocalization C.l E Q.Z.obj.left).obj M)).app
          ((sfRationalConstructibleLocalization C.l E Q.Z.obj.left).obj N)) := by
  exact rationalProjectionPullTensorSquare H Q.i (H.integralExchange Q).openTensorPullback
    (H.rationalExchange Q).openTensorPullback M N
    (H.integralOpenTensorPullbackNormalization Q M N)
    (H.rationalOpenTensorPullbackNormalization Q _ _)

attribute [local irreducible] rationalProjectionTensorComparison
  coordinateTensor coordinateOpen coordinateSupport

/-- The compact-support component square for the canonical tensor comparison.
Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-rational-projection-tensor-compatibility-compact).
(blueprint: lem-sf-rational-projection-tensor-compatibility).

Proof: expand the compactification projection as the counit mate followed by the
open projection. Use the unit and counit equations of the coefficient comparison,
the normalized tensor-pullback comparisons on the integral models, and the
pure-tensor formula for the canonical localization tensor. Pasting the proper
and open squares gives the displayed equality; all endpoint maps are the
specified comparison isomorphisms. -/
theorem rationalProjectionTensorCompatibility_compactSupport
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E) :
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (sfRationalConstructibleLocalization C.l E Y.obj.left).map
            (compactSupportProjectionComponent H.integralExchange f c K L) ≫
          (target H.rationalization
            (rationalProjectionTensorComparison H) f c K L).hom =
        (source H.rationalization
          (rationalProjectionTensorComparison H) f c K L).hom ≫
          compactSupportProjectionComponent H.rationalExchange f c
            ((sfRationalConstructibleLocalization C.l E X.obj.left).obj K)
            ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj L) := by
  intro X Y f c K L
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let residues (W : SixFunctorSpace D) :
      ∀ x : W.obj.left, Invertible (C.l : W.obj.left.residueField x) := fun x ↦
    let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ W.obj.hom.appTop ≫
      W.obj.left.Γevaluation x).hom
    (Eq.mp (congrArg IsUnit (map_natCast φ C.l))
      ((isUnit_iff_ne_zero.mpr
        (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : C.l.Prime)
          C.different.symm)).map φ)).invertible
  let Q := compactSupportProjectionSquare f c
  let := Q.proper_p
  let := residues Q.X
  let := residues Q.Z
  let := residues Q.Y
  have ho := coefficientOpenSquare (H.integralExchange Q) (H.rationalExchange Q)
    H.rationalization (rationalProjectionTensorComparison H) (rationalOpenTensorSquare H Q)
  have hp (M N : sfIntegralConstructibleCategory C.l E Q.Y.obj.left) :=
    rationalProjectionPullTensorSquare H Q.p (coordinateTensor (H.integralExchange Q))
      (coordinateTensor (H.rationalExchange Q)) M N
      ((coordinateTensor_heq (H.integralExchange Q) M N).trans
        (H.integralTensorPullbackNormalization Q M N))
      ((coordinateTensor_heq (H.rationalExchange Q) _ _).trans
        (H.rationalTensorPullbackNormalization Q _ _))
  have hc := coefficientCompactSquare (H.integralExchange Q) (H.rationalExchange Q)
    H.rationalization (rationalProjectionTensorComparison H) hp ho K L
  exact hc

/-- The proper counit component square for the canonical tensor comparison.
Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-rational-projection-tensor-compatibility-proper).
(blueprint: lem-sf-rational-projection-tensor-compatibility).

Proof: expand the proper projection as the right-adjoint projection mate. The
counit equation for the coefficient comparison and the normalized tensor
pullback comparison identify its transpose with the localization of the
integral transpose. Cancel the displayed endpoint isomorphisms and transpose
back, obtaining the proper square. -/
theorem rationalProjectionTensorCompatibility_proper
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E) :
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (sfRationalConstructibleLocalization C.l E Y.obj.left).map
            (compactSupportProperProjection H.integralExchange f K L) ≫
          (properTarget H.rationalization
            (rationalProjectionTensorComparison H) f K L).hom =
        (properSource H.rationalization
          (rationalProjectionTensorComparison H) f K L).hom ≫
          compactSupportProperProjection H.rationalExchange f
            ((sfRationalConstructibleLocalization C.l E X.obj.left).obj K)
            ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj L) := by
  intro X Y f _ K L
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let residues (W : SixFunctorSpace D) :
      ∀ x : W.obj.left, Invertible (C.l : W.obj.left.residueField x) := fun x ↦
    let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ W.obj.hom.appTop ≫
      W.obj.left.Γevaluation x).hom
    (Eq.mp (congrArg IsUnit (map_natCast φ C.l))
      ((isUnit_iff_ne_zero.mpr
        (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : C.l.Prime)
          C.different.symm)).map φ)).invertible
  let := residues X
  let := residues Y
  have h := properCoefficientProjection H.integralExchange H.rationalExchange
    H.rationalization (rationalProjectionTensorComparison H) f
    (rationalProperTensorSquare H f) K L
  exact h

/-- One normalized tensor comparison carries both the compact-support projection
and the proper counit mate. This concerns individual arrows only, without assuming
or asserting any compactification, composition, or pentagon law.

Source: thm-sf-pf-field.proof.md, Compatibility, and the final coherence sentence
of fix-prop-projection-formula.proof.md.
(blueprint: lem-sf-rational-projection-tensor-compatibility).

Proof: use the unchanged integral object formula and pure-tensor morphism formula
of rationalDerivedTensor_existsUnique. They give a natural tensor comparison with
identity components on the integral models, independently of a compactification.
The canonicalRationalPullbackTensor_existsUnique formula identifies the localization
of each integral proper/open tensor-pullback comparison with the rational one.
The rationalModelNormalization field makes the prescribed operation comparisons
identity components on these same models, so these squares use those comparisons.
Transpose the proper projection under the prescribed pull/direct adjunction.
The unit and counit equations of H.rationalization identify its transpose with the
localized integral transpose. For the open projection, transpose under the open
adjunction, use its unit equation and the open tensor-pullback normalization.
Invert the resulting equality of the specified open-projection isomorphisms.
The pullComposition equation identifies the last pullback-composition factor.
Paste these two squares and use the support factorization normalization to obtain
the compact-support square below. The proper square is the proper transpose
calculation alone. All endpoint maps are the displayed operation comparisons.
The tensor endpoint comparison is constructed from the proved functor equality
above. Zero objects, empty opens and identity proper maps use the same formulas;
the proper and compact-support projection components need not be invertible,
and localization faithfulness is not required. -/
theorem rationalProjectionTensorCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E) :
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (sfRationalConstructibleLocalization C.l E Y.obj.left).map
            (compactSupportProjectionComponent H.integralExchange f c K L) ≫
          (target H.rationalization
            (rationalProjectionTensorComparison H) f c K L).hom =
        (source H.rationalization
          (rationalProjectionTensorComparison H) f c K L).hom ≫
          compactSupportProjectionComponent H.rationalExchange f c
            ((sfRationalConstructibleLocalization C.l E X.obj.left).obj K)
            ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj L)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (sfRationalConstructibleLocalization C.l E Y.obj.left).map
            (compactSupportProperProjection H.integralExchange f K L) ≫
          (properTarget H.rationalization
            (rationalProjectionTensorComparison H) f K L).hom =
        (properSource H.rationalization
          (rationalProjectionTensorComparison H) f K L).hom ≫
          compactSupportProperProjection H.rationalExchange f
            ((sfRationalConstructibleLocalization C.l E X.obj.left).obj K)
            ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj L)) := by
  exact ⟨rationalProjectionTensorCompatibility_compactSupport H,
    rationalProjectionTensorCompatibility_proper H⟩

end WeilConjectures
