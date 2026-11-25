/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
public import Mathlib.CategoryTheory.Products.Basic

/-! # A mixed tensor square with coherent stage endpoints -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace WeilConjectures

private theorem mixed_component
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (R : C ⥤ D) (R' : E ⥤ F) (S : C ⥤ E) (T : D ⥤ F)
    (U : C × C ⥤ C) (V : D × D ⥤ D)
    (U' : E × E ⥤ E) (V' : F × F ⥤ F)
    (b : R ⋙ T ≅ S ⋙ R')
    (t : U ⋙ S ≅ S.prod S ⋙ U') (q : V ⋙ T ≅ T.prod T ⋙ V')
    (mu : U ⋙ R ≅ R.prod R ⋙ V) (nu : U' ⋙ R' ≅ R'.prod R' ⋙ V')
    (square : ∀ M N,
      T.map (mu.hom.app (M, N)) ≫ q.hom.app (R.obj M, R.obj N) ≫
          V'.map (Prod.mkHom (b.hom.app M) (b.hom.app N)) =
        b.hom.app (U.obj (M, N)) ≫ R'.map (t.hom.app (M, N)) ≫
          nu.hom.app (S.obj M, S.obj N))
    (M N : C) (M₀ N₀ : D) (M₁ N₁ : E) (M₂ N₂ : F)
    (pM : M₀ ≅ R.obj M) (pN : N₀ ≅ R.obj N)
    (xM : S.obj M ≅ M₁) (xN : S.obj N ≅ N₁)
    (yM : T.obj M₀ ≅ M₂) (yN : T.obj N₀ ≅ N₂)
    (pM' : M₂ ≅ R'.obj M₁) (pN' : N₂ ≅ R'.obj N₁)
    (cohM : T.map pM.hom ≫ b.hom.app M ≫ R'.map xM.hom = yM.hom ≫ pM'.hom)
    (cohN : T.map pN.hom ≫ b.hom.app N ≫ R'.map xN.hom = yN.hom ≫ pN'.hom) :
    let a := b.app (U.obj (M, N)) ≪≫
      R'.mapIso (t.app (M, N) ≪≫ U'.mapIso (Iso.prod xM xN))
    let z := (q.app (M₀, N₀) ≪≫ V'.mapIso (Iso.prod yM yN)) ≪≫
      V'.mapIso (Iso.prod pM' pN')
    a.hom ≫ nu.hom.app (M₁, N₁) ≫ z.inv =
      T.map (mu.hom.app (M, N) ≫ V.map (Prod.mkHom pM.inv pN.inv)) := by
  have hs :
      T.map (mu.hom.app (M, N) ≫ V.map (Prod.mkHom pM.inv pN.inv)) ≫
          q.hom.app (M₀, N₀) ≫
          V'.map (Prod.mkHom yM.hom yN.hom) ≫
          V'.map (Prod.mkHom pM'.hom pN'.hom) =
        b.hom.app (U.obj (M, N)) ≫ R'.map (t.hom.app (M, N)) ≫
          R'.map (U'.map (Prod.mkHom xM.hom xN.hom)) ≫ nu.hom.app (M₁, N₁) := by
    have hM : T.map pM.inv ≫ yM.hom ≫ pM'.hom =
        b.hom.app M ≫ R'.map xM.hom := by
      rw [← cohM]
      simp only [← T.map_comp_assoc, Iso.inv_hom_id, T.map_id, Category.id_comp]
    have hN : T.map pN.inv ≫ yN.hom ≫ pN'.hom =
        b.hom.app N ≫ R'.map xN.hom := by
      rw [← cohN]
      simp only [← T.map_comp_assoc, Iso.inv_hom_id, T.map_id, Category.id_comp]
    have hq := q.hom.naturality (Prod.mkHom pM.inv pN.inv)
    have hn := nu.hom.naturality (Prod.mkHom xM.hom xN.hom)
    simp only [Functor.comp_map, Functor.prod_map] at hq hn
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hq]
    simp only [← V'.map_comp, prod_comp, hM, hN]
    have hp : Prod.mkHom (b.hom.app M ≫ R'.map xM.hom)
        (b.hom.app N ≫ R'.map xN.hom) =
        Prod.mkHom (b.hom.app M) (b.hom.app N) ≫
          Prod.mkHom (R'.map xM.hom) (R'.map xN.hom) := rfl
    rw [hp, V'.map_comp, reassoc_of% (square M N), hn]
  intro a z
  rw [← Category.assoc]
  apply (Iso.comp_inv_eq z).2
  simpa only [a, z, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Iso.prod_hom, Category.assoc] using hs.symm

/-- The mixed tensor square transports a conjugate with coherent pullback endpoints.

Source: lemma-section-normal-bundle--1, common-stage subargument, steps 3–5.
Proof: Use tensor comparison naturality on the inverse endpoint maps. Pullback tower
coherence cancels these inverses. Apply the mixed scalar square, followed by naturality
of the tensor/pullback isomorphism along the source associators. Finally cancel the
invertible target endpoint. The two input coherence equations come from the specified
stage-system pair functor coherence law.
(blueprint: lem-weil-mixed-tensor-stage-component). -/
theorem mixedTensorStageComponent
    {I : Type*} [Preorder I]
    {C : I → Type*} [∀ i, Category* (C i)]
    {D : I → Type*} [∀ i, Category* (D i)]
    (SX : StageSystem C) (SY : StageSystem D)
    (R : ∀ i, C i ⥤ D i) (TX : ∀ i, C i × C i ⥤ C i)
    (TY : ∀ i, D i × D i ⥤ D i)
    (p : ∀ {i j : I} (h : i ≤ j), R i ⋙ SY.T h ≅ SX.T h ⋙ R j)
    (coh : StageSystem.pairFunctorCoherent SX SY R p)
    (tX : ∀ {i j : I} (h : i ≤ j), TX i ⋙ SX.T h ≅
      (SX.T h).prod (SX.T h) ⋙ TX j)
    (tY : ∀ {i j : I} (h : i ≤ j), TY i ⋙ SY.T h ≅
      (SY.T h).prod (SY.T h) ⋙ TY j)
    (mu : ∀ i, TX i ⋙ R i ≅ (R i).prod (R i) ⋙ TY i)
    (square : ∀ {i j : I} (h : i ≤ j) (M N : C i),
      (SY.T h).map ((mu i).hom.app (M, N)) ≫
          (tY h).hom.app ((R i).obj M, (R i).obj N) ≫
          (TY j).map (Prod.mkHom ((p h).hom.app M) ((p h).hom.app N)) =
        (p h).hom.app ((TX i).obj (M, N)) ≫
          (R j).map ((tX h).hom.app (M, N)) ≫
          (mu j).hom.app ((SX.T h).obj M, (SX.T h).obj N))
    (P Q : SX.PairCategory)
    (qP : ∀ (H : I) (h : P.stage ≤ H),
      (SY.T h).obj ((R P.stage).obj P.obj) ≅ (R H).obj (P.toStage h))
    (qQ : ∀ (H : I) (h : Q.stage ≤ H),
      (SY.T h).obj ((R Q.stage).obj Q.obj) ≅ (R H).obj (Q.toStage h))
    (hqP : ∀ H h, qP H h = (p h).app P.obj)
    (hqQ : ∀ H h, qQ H h = (p h).app Q.obj)
    (H K : I) (hP : P.stage ≤ H) (hQ : Q.stage ≤ H) (k : H ≤ K) :
    let PH := P.toStage hP
    let QH := Q.toStage hQ
    let a := (p k).app ((TX H).obj (PH, QH)) ≪≫
      (R K).mapIso ((tX k).app (PH, QH) ≪≫
        (TX K).mapIso (Iso.prod ((SX.assoc hP k).app P.obj)
          ((SX.assoc hQ k).app Q.obj)))
    let z := ((tY k).app ((SY.T hP).obj ((R P.stage).obj P.obj),
        (SY.T hQ).obj ((R Q.stage).obj Q.obj)) ≪≫
      (TY K).mapIso (Iso.prod ((SY.assoc hP k).app ((R P.stage).obj P.obj))
        ((SY.assoc hQ k).app ((R Q.stage).obj Q.obj)))) ≪≫
      (TY K).mapIso (Iso.prod (qP K (hP.trans k)) (qQ K (hQ.trans k)))
    a.hom ≫ (mu K).hom.app (P.toStage (hP.trans k), Q.toStage (hQ.trans k)) ≫ z.inv =
      (SY.T k).map ((mu H).hom.app (PH, QH) ≫
        (TY H).map (Prod.mkHom (qP H hP).inv (qQ H hQ).inv)) := by
  have coP := coh hP k P.obj
  have coQ := coh hQ k Q.obj
  have ePH := congrArg Iso.hom (hqP H hP)
  have ePK := congrArg Iso.hom (hqP K (hP.trans k))
  have eQH := congrArg Iso.hom (hqQ H hQ)
  have eQK := congrArg Iso.hom (hqQ K (hQ.trans k))
  simp only [Iso.app_hom] at ePH ePK eQH eQK
  rw [← ePH, ← ePK] at coP
  rw [← eQH, ← eQK] at coQ
  exact mixed_component (R H) (R K) (SX.T k) (SY.T k)
    (TX H) (TY H) (TX K) (TY K) (p k) (tX k) (tY k)
    (mu H) (mu K) (square k)
    (P.toStage hP) (Q.toStage hQ)
    ((SY.T hP).obj ((R P.stage).obj P.obj))
    ((SY.T hQ).obj ((R Q.stage).obj Q.obj))
    (P.toStage (hP.trans k)) (Q.toStage (hQ.trans k))
    ((SY.T (hP.trans k)).obj ((R P.stage).obj P.obj))
    ((SY.T (hQ.trans k)).obj ((R Q.stage).obj Q.obj))
    (qP H hP) (qQ H hQ)
    ((SX.assoc hP k).app P.obj) ((SX.assoc hQ k).app Q.obj)
    ((SY.assoc hP k).app ((R P.stage).obj P.obj))
    ((SY.assoc hQ k).app ((R Q.stage).obj Q.obj))
    (qP K (hP.trans k)) (qQ K (hQ.trans k)) coP coQ

end WeilConjectures
