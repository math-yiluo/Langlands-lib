/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionCoefficientTransport.RationalProjectionTensorCompatibility
public import WeilConjectures.SixFunctors.ProjectionCoefficientTransport.ProjectionMateFactors
public import WeilConjectures.SixFunctors.Common.CommonProjectionTensorComparison
import WeilConjectures.SixFunctors.Common.CommonProjectionOpenPullbackTensor

/-! # Common-stage preservation of a projection factor

Source: thm-sf-pf-field.proof.md, Compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] ScalarLocalization.category
open ProjectionCoefficientTransport
set_option allowUnsafeReducibility true in
attribute [local reducible] SixFunctorCompactifiedSquare.compactification
  sixFunctorFactorCompactification middleObject

attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear
  rationalDerivedTensor commonStageTensorComparison operationStageTransitionIso
  sfRationalScalarExtension sfConstructibleIntegralScalarExtension
  sfIntegralScalarComp sfIntegralScalarUnit

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

section CoefficientCalculus

variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
  {V : ∀ X, B X ⥤ B' X}

private theorem support_identification_preserved
    (c : SixFunctorCoefficientComparison S S' V)
    {X Y Z : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (hi : IsOpenImmersion i.hom.left) (hp : IsProper p.hom.left)
    (f : X ⟶ Y) (h : f = i ≫ p) (K : B X) :
    (V Y).map ((sixFunctorFactoredSupportIdentification S i p hi hp f h).hom.app K) ≫
        (c.directAdjunction p).right.hom.app ((S.openExtension i hi).obj K) ≫
        (S'.direct p).map ((c.openExtension i hi).hom.app K) =
      (c.supportAdjunction f (sixFunctorFactorCompactification i p hi hp f h)).left.hom.app K ≫
        (sixFunctorFactoredSupportIdentification S' i p hi hp f h).hom.app ((V X).obj K) := by
  subst f
  have : IsProper p.hom.left := hp
  simp only [sixFunctorFactoredSupportIdentification, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (c.properIdentity p ((S.openExtension i hi).obj K))]
  have hn := (c.supportAdjunction p (.ofIsProper p.hom.left)).left.hom.naturality
    ((S.openIdentification i hi).hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← (S'.properIdentity p).hom.naturality]
  rw [← (S'.support p (.ofIsProper p.hom.left)).map_comp_assoc, c.openIdentification,
    (S'.support p (.ofIsProper p.hom.left)).map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (c.composition i p (sixFunctorOpenCompactification i hi)
    (.ofIsProper p.hom.left) (sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl) K)]

private def normalizedOpenProjection
    {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    ((T Q.Z).obj ((S.openExtension Q.i Q.open_i).obj K)).obj ((S.pull Q.p).obj N) ≅
      (S.openExtension Q.i Q.open_i).obj (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) :=
  eqToIso (by rw [A.tensorBar, A.openExtension, A.properPull]; rfl) ≪≫
    (A.stage.openProjection.app K).app N ≪≫
    eqToIso (by rw [A.openExtension, A.tensorX, A.pull]; rfl)

private theorem normalizedOpenProjection_inv
    {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    (normalizedOpenProjection A K N).inv =
      sixFunctorOpenProjectionInverse S T Q A.openTensorPullback K N := by
  have h : HEq (normalizedOpenProjection A K N).inv
      ((A.stage.openProjection.inv.app K).app N) := by
    simp only [normalizedOpenProjection, Iso.trans_inv, eqToIso.inv,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  exact eq_of_heq (h.trans (A.openProjectionNormalization K N))

private theorem iso_inv_app_heq
    {CX CY : Type*} [Category* CX] [Category* CY]
    {F G F' G' : CX ⥤ CY} (hF : F = F') (hG : G = G')
    (a : F ≅ G) (b : F' ≅ G') (h : HEq a b) {x y : CX} (hxy : x = y) :
    HEq (a.inv.app x) (b.inv.app y) := by
  subst F'
  subst G'
  cases eq_of_heq h
  subst y
  rfl

private theorem factor_transport
    {CX CY : Type*} [Category* CX] [Category* CY]
    (F F₀ : CX ⥤ CY) (hF : F = F₀)
    {X X₀ Y Y₀ : CX} {Z Z₀ : CY} (hX : X = X₀) (hY : Y₀ = Y)
    (g : X₀ ≅ Y₀) (a : F₀.obj Y₀ ⟶ Z₀) (b : F.obj Y ⟶ Z)
    (ha : HEq a b) (hZ : Z₀ = Z) :
    eqToHom (show F.obj X = F₀.obj X₀ by rw [hF, hX]) ≫
        F₀.map g.hom ≫ a ≫ eqToHom hZ =
      F.map ((eqToIso hX ≪≫ g ≪≫ eqToIso hY).hom) ≫ b := by
  subst F₀
  subst X₀
  subst Y₀
  subst Z₀
  rw [eq_of_heq ha]
  simp

private theorem openFactor_eq
    {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    openFactor A K N =
      (S.direct Q.p).map (normalizedOpenProjection A K N).hom ≫
        (sixFunctorFactoredSupportIdentification S Q.i Q.p Q.open_i Q.proper_p
          Q.f Q.factorization).inv.app (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) := by
  have hσ := iso_inv_app_heq A.compactSupport
    (by rw [A.openExtension, A.properPush])
    A.stage.compactSupportIdentification
    (sixFunctorFactoredSupportIdentification S Q.i Q.p Q.open_i Q.proper_p
      Q.f Q.factorization) A.compactSupportNormalization
    (show ((A.stage.tensorX.obj K).obj (A.stage.pull.obj N)) =
      (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) by rw [A.tensorX, A.pull])
  exact factor_transport (S.direct Q.p) A.stage.properPush A.properPush.symm
    (by rw [A.tensorBar, A.openExtension, A.properPull]; rfl)
    (by rw [A.openExtension, A.tensorX, A.pull]; rfl)
    ((A.stage.openProjection.app K).app N) _ _ hσ
    (by rw [A.compactSupport, A.tensorX, A.pull])

private theorem transpose_preserved
    {CX CY CX' CY' : Type*}
    [Category* CX] [Category* CY] [Category* CX'] [Category* CY']
    {L : CX ⥤ CY} {R : CY ⥤ CX} {L' : CX' ⥤ CY'} {R' : CY' ⥤ CX'}
    {a : L ⊣ R} {a' : L' ⊣ R'} {c : CX ⥤ CX'} {d : CY ⥤ CY'}
    (e : CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison
      a a' c d)
    {X : CX} {Y : CY} {X' : CX'} {Y' : CY'}
    (x : c.obj X ≅ X') (y : d.obj Y ≅ Y')
    (f : X ⟶ R.obj Y) (f' : X' ⟶ R'.obj Y')
    (h : c.map f ≫ e.right.hom.app Y ≫ R'.map y.hom = x.hom ≫ f') :
    d.map ((a.homEquiv _ _).symm f) ≫ y.hom =
      e.left.hom.app X ≫ L'.map x.hom ≫ (a'.homEquiv _ _).symm f' := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hc : d.map (a.counit.app Y) =
      e.left.hom.app (R.obj Y) ≫ L'.map (e.right.hom.app Y) ≫
        a'.counit.app (d.obj Y) := by
    rw [e.counit]
    simp
  rw [hc]
  simp only [Category.assoc]
  have hn := e.left.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hn' := a'.counit.naturality y.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn'
  rw [← hn']
  rw [← L'.map_comp_assoc, ← L'.map_comp_assoc]
  simp only [Category.assoc]
  rw [h, L'.map_comp]
  simp only [Category.assoc]

private theorem pull_factorization_preserved
    (c : SixFunctorCoefficientComparison S S' V)
    {X Y Z : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (f : X ⟶ Y) (h : f = i ≫ p) (N : B Y) :
    (V X).map
        ((eqToIso (congrArg (fun e ↦ S.pull e) h) ≪≫ S.pullComposition i p).hom.app N) ≫
        (c.directAdjunction i).left.hom.app ((S.pull p).obj N) ≫
        (S'.pull i).map ((c.directAdjunction p).left.hom.app N) =
      (c.directAdjunction f).left.hom.app N ≫
        (eqToIso (congrArg (fun e ↦ S'.pull e) h) ≪≫ S'.pullComposition i p).hom.app
          ((V Y).obj N) := by
  subst f
  simpa using c.pullComposition i p N

private theorem openProjectionInverse_preserved
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {Q : SixFunctorCompactifiedSquare D}
    (c : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (K : B Q.X) (N : B Q.Y)
    (hμ : ∀ (M L : B Q.Z),
      (V Q.X).map ((A.openTensorPullback.inv.app M).app L) ≫
          (c.directAdjunction Q.i).left.hom.app (((T Q.Z).obj M).obj L) ≫
          (S'.pull Q.i).map ((t Q.Z).hom.app (M, L)) =
        (t Q.X).hom.app ((S.pull Q.i).obj M, (S.pull Q.i).obj L) ≫
          (Functor.uncurry.obj (T' Q.X)).map
            (Prod.mkHom ((c.directAdjunction Q.i).left.hom.app M)
              ((c.directAdjunction Q.i).left.hom.app L)) ≫
          (A'.openTensorPullback.inv.app ((V Q.Z).obj M)).app ((V Q.Z).obj L)) :
    (V Q.Z).map (sixFunctorOpenProjectionInverse S T Q A.openTensorPullback K N) ≫
        (t Q.Z).hom.app ((S.openExtension Q.i Q.open_i).obj K, (S.pull Q.p).obj N) ≫
        (Functor.uncurry.obj (T' Q.Z)).map
          (Prod.mkHom ((c.openExtension Q.i Q.open_i).hom.app K)
            ((c.directAdjunction Q.p).left.hom.app N)) =
      (c.openExtension Q.i Q.open_i).hom.app
          (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) ≫
        (S'.openExtension Q.i Q.open_i).map (inner c t Q.f K N).hom ≫
        sixFunctorOpenProjectionInverse S' T' Q A'.openTensorPullback
          ((V Q.X).obj K) ((V Q.Y).obj N) := by
  let J := S.openExtension Q.i Q.open_i
  let J' := S'.openExtension Q.i Q.open_i
  let U := S.pull Q.i
  let U' := S'.pull Q.i
  let TX := Functor.uncurry.obj (T Q.X)
  let TX' := Functor.uncurry.obj (T' Q.X)
  let TZ' := Functor.uncurry.obj (T' Q.Z)
  let L := (S.pull Q.p).obj N
  let L' := (S'.pull Q.p).obj ((V Q.Y).obj N)
  let v := (eqToIso (congrArg (fun e ↦ S.pull e) Q.factorization) ≪≫
    S.pullComposition Q.i Q.p).hom.app N
  let v' := (eqToIso (congrArg (fun e ↦ S'.pull e) Q.factorization) ≪≫
    S'.pullComposition Q.i Q.p).hom.app ((V Q.Y).obj N)
  let m := Prod.mkHom ((S.openAdjunction Q.i Q.open_i).unit.app K) v
  let m' := Prod.mkHom
    ((S'.openAdjunction Q.i Q.open_i).unit.app ((V Q.X).obj K)) v'
  let q := Prod.mkHom ((c.openExtension Q.i Q.open_i).hom.app K)
    ((c.directAdjunction Q.p).left.hom.app N)
  let x := inner c t Q.f K N
  let y := (t Q.Z).app (J.obj K, L) ≪≫ TZ'.mapIso
    (Iso.prod ((c.openExtension Q.i Q.open_i).app K)
      ((c.directAdjunction Q.p).left.app N))
  let τ := TX.map m ≫ (A.openTensorPullback.inv.app (J.obj K)).app L
  let τ' := TX'.map m' ≫ (A'.openTensorPullback.inv.app (J'.obj ((V Q.X).obj K))).app L'
  have hu : (V Q.X).map ((S.openAdjunction Q.i Q.open_i).unit.app K) ≫
      (c.directAdjunction Q.i).left.hom.app (J.obj K) ≫
      U'.map ((c.openExtension Q.i Q.open_i).hom.app K) =
        (S'.openAdjunction Q.i Q.open_i).unit.app ((V Q.X).obj K) := by
    simpa only [c.openAdjunction_left, c.openAdjunction_right] using
      (c.openAdjunction Q.i Q.open_i).unit K
  have hv := pull_factorization_preserved c Q.i Q.p Q.f Q.factorization N
  have hm : Prod.mkHom ((V Q.X).map m.1) ((V Q.X).map m.2) ≫
        Prod.mkHom ((c.directAdjunction Q.i).left.hom.app (J.obj K))
          ((c.directAdjunction Q.i).left.hom.app L) ≫
        Prod.mkHom (U'.map q.1) (U'.map q.2) =
      Prod.mkHom (𝟙 ((V Q.X).obj K)) ((c.directAdjunction Q.f).left.hom.app N) ≫ m' := by
    apply Prod.hom_ext
    · simpa only [prod_comp_fst, Category.id_comp, Category.assoc] using hu
    · simpa only [prod_comp_snd, Category.assoc] using hv
  have ht : (V Q.X).map τ ≫
      (c.directAdjunction Q.i).left.hom.app (((T Q.Z).obj (J.obj K)).obj L) ≫
        U'.map y.hom = x.hom ≫ τ' := by
    have hnat := (Functor.uncurry.map A'.openTensorPullback.inv).naturality q
    have htn := (t Q.X).hom.naturality m
    change (V Q.X).map (TX.map m) ≫ (t Q.X).hom.app (U.obj (J.obj K), U.obj L) =
      (t Q.X).hom.app (K, (S.pull Q.f).obj N) ≫
        TX'.map (Prod.mkHom ((V Q.X).map m.1) ((V Q.X).map m.2)) at htn
    have hnat' : TX'.map (Prod.mkHom (U'.map q.1) (U'.map q.2)) ≫
        (A'.openTensorPullback.inv.app (J'.obj ((V Q.X).obj K))).app L' =
      (A'.openTensorPullback.inv.app ((V Q.Z).obj (J.obj K))).app ((V Q.Z).obj L) ≫
        U'.map (TZ'.map q) := by
      simpa [TX', TZ', U', J', L', Functor.uncurry, Functor.whiskeringLeft₂,
        Functor.postcompose₂, Functor.whiskeringLeft, Functor.whiskeringRight,
        Functor.map_comp, Category.assoc] using hnat
    simp only [τ, y, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.prod_hom,
      Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hμ (J.obj K) L), reassoc_of% htn]
    rw [← hnat']
    rw [← TX'.map_comp_assoc, ← TX'.map_comp_assoc]
    simp only [Category.assoc]
    rw [hm, TX'.map_comp]
    simp only [x, ProjectionCoefficientTransport.inner, TX', τ', Iso.trans_hom,
      Functor.mapIso_hom,
      Iso.prod_hom, Iso.app_hom, Iso.refl_hom, Category.assoc]
  have he := transpose_preserved (c.openAdjunction Q.i Q.open_i) x y τ τ' (by
    simpa only [c.openAdjunction_right, TX, TX', TZ', Functor.uncurry_obj_obj,
      Functor.id_obj] using ht)
  simp only [c.openAdjunction_left] at he
  have hτ : sixFunctorOpenProjectionInverse S T Q A.openTensorPullback K N =
      ((S.openAdjunction Q.i Q.open_i).homEquiv _ _).symm τ := by
    dsimp [τ, TX, m, sixFunctorOpenProjectionInverse]
    rw [← Adjunction.homEquiv_naturality_left_symm]
    congr 1
    simp [NatTrans.naturality_assoc, Category.assoc, v, J, L]
  have hτ' : sixFunctorOpenProjectionInverse S' T' Q A'.openTensorPullback
        ((V Q.X).obj K) ((V Q.Y).obj N) =
      ((S'.openAdjunction Q.i Q.open_i).homEquiv _ _).symm τ' := by
    dsimp [τ', TX', m', sixFunctorOpenProjectionInverse]
    rw [← Adjunction.homEquiv_naturality_left_symm]
    congr 1
    simp [NatTrans.naturality_assoc, Category.assoc, v', J', L']
  rw [hτ, hτ']
  simpa only [x, y, TX, TX', TZ', J, J', L, L', Functor.uncurry_obj_obj,
    Functor.id_obj, Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
    Iso.app_hom,
    Category.assoc] using he

private theorem inverse_square
    {CX : Type*} [Category* CX] {A B A' B' : CX}
    (a : A ≅ B) (b : A' ≅ B') (c : A ≅ A') (d : B ≅ B')
    (h : a.inv ≫ c.hom = d.hom ≫ b.inv) :
    a.hom ≫ d.hom = c.hom ≫ b.hom := by
  apply (cancel_epi a.inv).1
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem openFactor_preserved_of_openProjection
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {Q : SixFunctorCompactifiedSquare D}
    (c : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (K : B Q.X) (N : B Q.Y)
    (hγ : (V Q.Z).map (normalizedOpenProjection A K N).hom ≫
        (c.openExtension Q.i Q.open_i).hom.app
          (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) ≫
        (S'.openExtension Q.i Q.open_i).map (inner c t Q.f K N).hom =
      (t Q.Z).hom.app ((S.openExtension Q.i Q.open_i).obj K, (S.pull Q.p).obj N) ≫
        (Functor.uncurry.obj (T' Q.Z)).map
          (Prod.mkHom ((c.openExtension Q.i Q.open_i).hom.app K)
            ((c.directAdjunction Q.p).left.hom.app N)) ≫
        (normalizedOpenProjection A' ((V Q.X).obj K) ((V Q.Y).obj N)).hom) :
    (V Q.Y).map (openFactor A K N) ≫ (target c t Q.f Q.compactification K N).hom =
      (middle c t Q K N).hom ≫ openFactor A' ((V Q.X).obj K) ((V Q.Y).obj N) := by
  let σ := sixFunctorFactoredSupportIdentification S Q.i Q.p Q.open_i Q.proper_p
    Q.f Q.factorization
  let σ' := sixFunctorFactoredSupportIdentification S' Q.i Q.p Q.open_i Q.proper_p
    Q.f Q.factorization
  let M := ((T Q.X).obj K).obj ((S.pull Q.f).obj N)
  let M' := ((T' Q.X).obj ((V Q.X).obj K)).obj ((S'.pull Q.f).obj ((V Q.Y).obj N))
  let J := S.openExtension Q.i Q.open_i
  let J' := S'.openExtension Q.i Q.open_i
  let R := S.direct Q.p
  let R' := S'.direct Q.p
  let e := (c.directAdjunction Q.p).right.app (J.obj M) ≪≫
    R'.mapIso ((c.openExtension Q.i Q.open_i).app M)
  have hs : (V Q.Y).map (σ.inv.app M) ≫
      (c.supportAdjunction Q.f Q.compactification).left.hom.app M =
      e.hom ≫ σ'.inv.app ((V Q.X).obj M) := by
    have h : (V Q.Y).map (σ.hom.app M) ≫ e.hom =
        (c.supportAdjunction Q.f Q.compactification).left.hom.app M ≫
          σ'.hom.app ((V Q.X).obj M) := by
      simpa only [σ, σ', e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Category.assoc] using
        support_identification_preserved c Q.i Q.p Q.open_i Q.proper_p
          Q.f Q.factorization M
    apply (cancel_epi ((V Q.Y).map (σ.hom.app M))).1
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    rw [← Category.assoc, h]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    rw [(V Q.Y).map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hs' : (V Q.Y).map (σ.inv.app M) ≫
      (target c t Q.f Q.compactification K N).hom =
      (c.directAdjunction Q.p).right.hom.app (J.obj M) ≫
        R'.map ((c.openExtension Q.i Q.open_i).hom.app M ≫
          J'.map (inner c t Q.f K N).hom) ≫ σ'.inv.app M' := by
    change (V Q.Y).map (σ.inv.app M) ≫
      ((c.supportAdjunction Q.f Q.compactification).left.hom.app M ≫
        (S'.support Q.f Q.compactification).map (inner c t Q.f K N).hom) = _
    rw [reassoc_of% hs]
    have hn := σ'.inv.naturality (inner c t Q.f K N).hom
    dsimp only [Functor.comp_map] at hn
    rw [← hn]
    simp only [e, R', J', M', Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Functor.map_comp, Category.assoc]
  rw [openFactor_eq A, openFactor_eq A', Functor.map_comp, Category.assoc, hs']
  have hn := (c.directAdjunction Q.p).right.hom.naturality
    (normalizedOpenProjection A K N).hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← R'.map_comp_assoc, hγ]
  simp only [middle, R', σ', M', Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]

private theorem openFactor_preserved
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {Q : SixFunctorCompactifiedSquare D}
    (c : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (K : B Q.X) (N : B Q.Y) (hμ : OpenPullbackTensorSquare c t A A') :
    (V Q.Y).map (openFactor A K N) ≫ (target c t Q.f Q.compactification K N).hom =
      (middle c t Q K N).hom ≫ openFactor A' ((V Q.X).obj K) ((V Q.Y).obj N) := by
  unfold OpenPullbackTensorSquare at hμ
  apply openFactor_preserved_of_openProjection c t A A' K N
  let a := (V Q.Z).mapIso (normalizedOpenProjection A K N)
  let b := normalizedOpenProjection A' ((V Q.X).obj K) ((V Q.Y).obj N)
  let x := (t Q.Z).app
      ((S.openExtension Q.i Q.open_i).obj K,
        (S.pull Q.p).obj N) ≪≫
    (Functor.uncurry.obj (T' Q.Z)).mapIso
      (Iso.prod ((c.openExtension Q.i Q.open_i).app K)
        ((c.directAdjunction Q.p).left.app N))
  let y := (c.openExtension Q.i Q.open_i).app
      (((T Q.X).obj K).obj
        ((S.pull Q.f).obj N)) ≪≫
    (S'.openExtension Q.i Q.open_i).mapIso (inner c t Q.f K N)
  have hi : a.inv ≫ x.hom = y.hom ≫ b.inv := by
    simpa only [a, b, x, y, Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_hom, Iso.prod_hom,
      Iso.trans_hom, normalizedOpenProjection_inv, Category.assoc] using
      openProjectionInverse_preserved c t A A' K N
        hμ
  simpa only [a, b, x, y, Functor.mapIso_hom, Iso.trans_hom, Iso.prod_hom, Iso.app_hom,
    Category.assoc] using inverse_square a b x y hi

end CoefficientCalculus

set_option backward.isDefEq.respectTransparency false in
/-- Finite-stage inclusion preserves the open projection factor and the final
support identification, through the same canonical tensorator.

Source: thm-sf-pf-field.proof.md, Compatibility, and steps 2--4 of
lem-sf-common-projection-tensor-compatibility.
(blueprint: lem-sf-common-projection-open-factor).

Proof: first compare the inverse open projection. By openProjectionNormalization
it is open extension applied to the pullback compositor followed by the transpose
of the tensor of the open unit with identity and the inverse canonical open
pullback/tensor comparison. The finite representative equation for
canonicalCommonStagePullbackTensor identifies the two tensor/pullback maps on
included inputs. The coefficient open-adjunction unit equation and the
pullComposition equation identify the remaining maps and their prescribed
operation comparisons. Equality under the open adjunction Hom equivalence gives
the square for the inverse open projection; conjugating with its inverse gives
the forward square. Apply proper direct image to this square, using naturality
of its coefficient comparison. Finally expand the inverse support identification
as inverse composition, proper and open identifications. The coefficient laws
for these three maps identify the final support comparison with target, including
its inner pullback comparison. This proves the displayed square. No proper
counit projection mate occurs in this argument. Empty opens, zero inputs and
identity extensions obey the same adjunction and compositor equations. -/
theorem commonProjectionOpenFactor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Q.X.obj.left E)
    (N : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Q.Y.obj.left E) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) E).map
        (openFactor ((H.coefficientStages E).rationalExchange Q) K N) ≫
        (target (H.commonStageComparison E) (commonProjectionTensorComparison H E)
          Q.f Q.compactification K N).hom =
        (middle (H.commonStageComparison E) (commonProjectionTensorComparison H E)
          Q K N).hom ≫
        openFactor (H.commonStageExchange Q)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Q.X.obj.left) E).obj K)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) E).obj N) := by
  exact openFactor_preserved (H.commonStageComparison E) (commonProjectionTensorComparison H E)
    ((H.coefficientStages E).rationalExchange Q) (H.commonStageExchange Q) K N
    (commonProjectionOpenPullbackTensor H E Q)

end WeilConjectures
