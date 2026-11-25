/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.Supporting.Tensor.RepresentativeTensorFixedData
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex

/-! # Cancellation of normalized tensor representative cubes

Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-representative-tensor-cube).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
open CategoryTheory.Functor

namespace WeilConjectures

private noncomputable def scalarUncurryRealization
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (F : C ⥤ D) (S : D × D ⥤ D)
    (e : (postcompose₂.obj F).obj T ≅
      (((whiskeringLeft₂ D).obj F).obj F).obj (curry.obj S)) :
    uncurry.obj T ⋙ F ≅ (F.prod F) ⋙ S :=
  finiteScalarUncurryPostcomposeIso T F ≪≫ uncurry.mapIso e ≪≫
    isoWhiskerLeft (F.prod F) (currying.counitIso.app S)

private theorem scalarUncurryRealization_hom_app
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (F : C ⥤ D) (S : D × D ⥤ D)
    (e : (postcompose₂.obj F).obj T ≅
      (((whiskeringLeft₂ D).obj F).obj F).obj (curry.obj S)) (M N : C) :
    (scalarUncurryRealization T F S e).hom.app (M, N) =
      (e.hom.app M).app N := by
  simp [scalarUncurryRealization, finiteScalarUncurryPostcomposeIso]

private theorem scalarCurryComparison_app
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C × C ⥤ C) (S : D × D ⥤ D)
    (φ : T ⋙ F ⟶ (F.prod F) ⋙ S) (M N : C) :
    ((curry.map φ ≫ (curryObjProdComp F F S).hom).app M).app N =
      φ.app (M, N) := by
  simp only [NatTrans.comp_app, curry_map_app_app, curryObjProdComp_hom_app_app]
  exact CategoryTheory.Category.comp_id _

private theorem pairMap_comp
    {C D : Type*} [Category C] [Category D] (T : C × C ⥤ D)
    {P Q R P' Q' R' : C} (f : P ⟶ Q) (g : Q ⟶ R)
    (f' : P' ⟶ Q') (g' : Q' ⟶ R') :
    T.map (Prod.mkHom (f ≫ g) (f' ≫ g')) =
      T.map (Prod.mkHom f f') ≫ T.map (Prod.mkHom g g') :=
  T.map_comp (Prod.mkHom f f') (Prod.mkHom g g')

private theorem scalarTensorSquare
    {K H K' H' D E D' E' : Type*}
    [Category K] [Category H] [Category K'] [Category H']
    [Category D] [Category E] [Category D'] [Category E']
    (q : K ⥤ D) (s : H ⥤ E) (q' : K' ⥤ D') (s' : H' ⥤ E')
    (A : K ⥤ H) (B : K' ⥤ H') (U : K ⥤ K') (V : H ⥤ H')
    (F : D ⥤ E) (G : D' ⥤ E') (EY : D ⥤ D') (EX : E ⥤ E')
    (f : q ⋙ F ≅ A ⋙ s) (g : q' ⋙ G ≅ B ⋙ s')
    (eY : q ⋙ EY ≅ U ⋙ q') (eX : s ⋙ EX ≅ V ⋙ s')
    (c : U ⋙ B ≅ A ⋙ V) (alpha : EY ⋙ G ≅ F ⋙ EX)
    (PK : ObjectProperty K) (PH : ObjectProperty H)
    (PK' : ObjectProperty K') (PH' : ObjectProperty H')
    (hA : ∀ P, PK P → PH (A.obj P))
    (hU : ∀ P, PK P → PK' (U.obj P))
    (hV : ∀ P, PH P → PH' (V.obj P))
    (hB : ∀ P, PK' P → PH' (B.obj P))
    (tK : K × K ⥤ K) (tH : H × H ⥤ H)
    (tK' : K' × K' ⥤ K') (tH' : H' × H' ⥤ H')
    (TK : D × D ⥤ D) (TH : E × E ⥤ E)
    (TK' : D' × D' ⥤ D') (TH' : E' × E' ⥤ E')
    (rK : (PK.ι.prod PK.ι) ⋙ tK ⋙ q ≅ ((PK.ι ⋙ q).prod (PK.ι ⋙ q)) ⋙ TK)
    (rH : (PH.ι.prod PH.ι) ⋙ tH ⋙ s ≅ ((PH.ι ⋙ s).prod (PH.ι ⋙ s)) ⋙ TH)
    (rK' : (PK'.ι.prod PK'.ι) ⋙ tK' ⋙ q' ≅
      ((PK'.ι ⋙ q').prod (PK'.ι ⋙ q')) ⋙ TK')
    (rH' : (PH'.ι.prod PH'.ι) ⋙ tH' ⋙ s' ≅
      ((PH'.ι ⋙ s').prod (PH'.ι ⋙ s')) ⋙ TH')
    (mF : tK ⋙ A ⟶ (A.prod A) ⋙ tH)
    (mG : tK' ⋙ B ⟶ (B.prod B) ⋙ tH')
    (bY : tK ⋙ U ⟶ (U.prod U) ⋙ tK')
    (bX : tH ⋙ V ⟶ (V.prod V) ⋙ tH')
    (phiF : TK ⋙ F ⟶ (F.prod F) ⋙ TH)
    (phiG : TK' ⋙ G ⟶ (G.prod G) ⋙ TH')
    (tauY : TK ⋙ EY ≅ (EY.prod EY) ⋙ TK')
    (tauX : TH ⋙ EX ≅ (EX.prod EX) ⋙ TH')
    (hf : ∀ (P Q : K) (hp : PK P) (hq : PK Q),
      F.map (rK.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ phiF.app (q.obj P, q.obj Q) ≫
        TH.map (Prod.mkHom (f.hom.app P) (f.hom.app Q)) =
      f.hom.app (tK.obj (P, Q)) ≫ s.map (mF.app (P, Q)) ≫
        rH.hom.app (⟨A.obj P, hA P hp⟩, ⟨A.obj Q, hA Q hq⟩))
    (hg : ∀ (P Q : K') (hp : PK' P) (hq : PK' Q),
      G.map (rK'.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ phiG.app (q'.obj P, q'.obj Q) ≫
        TH'.map (Prod.mkHom (g.hom.app P) (g.hom.app Q)) =
      g.hom.app (tK'.obj (P, Q)) ≫ s'.map (mG.app (P, Q)) ≫
        rH'.hom.app (⟨B.obj P, hB P hp⟩, ⟨B.obj Q, hB Q hq⟩))
    (hy : ∀ (P Q : K) (hp : PK P) (hq : PK Q),
      EY.map (rK.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ tauY.hom.app (q.obj P, q.obj Q) ≫
        TK'.map (Prod.mkHom (eY.hom.app P) (eY.hom.app Q)) =
      eY.hom.app (tK.obj (P, Q)) ≫ q'.map (bY.app (P, Q)) ≫
        rK'.hom.app (⟨U.obj P, hU P hp⟩, ⟨U.obj Q, hU Q hq⟩))
    (hx : ∀ (P Q : H) (hp : PH P) (hq : PH Q),
      EX.map (rH.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ tauX.hom.app (s.obj P, s.obj Q) ≫
        TH'.map (Prod.mkHom (eX.hom.app P) (eX.hom.app Q)) =
      eX.hom.app (tH.obj (P, Q)) ≫ s'.map (bX.app (P, Q)) ≫
        rH'.hom.app (⟨V.obj P, hV P hp⟩, ⟨V.obj Q, hV Q hq⟩))
    (hc : ∀ P : K,
      EX.map (f.hom.app P) ≫ eX.hom.app (A.obj P) ≫ s'.map (c.inv.app P) =
      alpha.inv.app (q.obj P) ≫ G.map (eY.hom.app P) ≫ g.hom.app (U.obj P))
    (ht : ∀ P Q : K,
      V.map (mF.app (P, Q)) ≫ bX.app (A.obj P, A.obj Q) ≫
        tH'.map (Prod.mkHom (c.inv.app P) (c.inv.app Q)) =
      c.inv.app (tK.obj (P, Q)) ≫ B.map (bY.app (P, Q)) ≫
        mG.app (U.obj P, U.obj Q))
    (P Q : K) (hp : PK P) (hq : PK Q) :
    EX.map (phiF.app (q.obj P, q.obj Q)) ≫
        tauX.hom.app (F.obj (q.obj P), F.obj (q.obj Q)) =
      alpha.inv.app (TK.obj (q.obj P, q.obj Q)) ≫
        G.map (tauY.hom.app (q.obj P, q.obj Q)) ≫
        phiG.app (EY.obj (q.obj P), EY.obj (q.obj Q)) ≫
        TH'.map (Prod.mkHom (alpha.hom.app (q.obj P)) (alpha.hom.app (q.obj Q))) := by
  let d (Z : K) : EX.obj (F.obj (q.obj Z)) ≅ s'.obj (B.obj (U.obj Z)) :=
    EX.mapIso (f.app Z) ≪≫ eX.app (A.obj Z) ≪≫ s'.mapIso (c.symm.app Z)
  let pre := EX.map (F.map (rK.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)))
  let post := TH'.mapIso (Iso.prod (d P) (d Q))
  apply (cancel_epi pre).mp
  apply (cancel_mono post.hom).mp
  have hd (Z : K) : (d Z).hom =
      alpha.inv.app (q.obj Z) ≫ G.map (eY.hom.app Z) ≫ g.hom.app (U.obj Z) := hc Z
  have hdp (Z : K) : alpha.hom.app (q.obj Z) ≫ (d Z).hom =
      G.map (eY.hom.app Z) ≫ g.hom.app (U.obj Z) := by
    rw [hd, Iso.hom_inv_id_app_assoc]
  have hnX := tauX.hom.naturality (Prod.mkHom (f.hom.app P) (f.hom.app Q))
  have hnG := phiG.naturality (Prod.mkHom (eY.hom.app P) (eY.hom.app Q))
  have hnA := alpha.inv.naturality (rK.hom.app (⟨P, hp⟩, ⟨Q, hq⟩))
  have hnE := eX.hom.naturality (mF.app (P, Q))
  have hnB := g.hom.naturality (bY.app (P, Q))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj,
    Functor.prod_obj, ObjectProperty.ι_obj] at hnX hnG hnA hnE hnB
  have hnR := rH'.hom.naturality (Prod.mkHom
    (ObjectProperty.homMk (c.inv.app P) :
      (⟨V.obj (A.obj P), hV _ (hA _ hp)⟩ : PH'.FullSubcategory) ⟶
        ⟨B.obj (U.obj P), hB _ (hU _ hp)⟩)
    (ObjectProperty.homMk (c.inv.app Q) :
      (⟨V.obj (A.obj Q), hV _ (hA _ hq)⟩ : PH'.FullSubcategory) ⟶
        ⟨B.obj (U.obj Q), hB _ (hU _ hq)⟩))
  dsimp only [Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
    ObjectProperty.homMk] at hnR
  have hpost : post.hom =
      TH'.map (Prod.mkHom (EX.map (f.hom.app P)) (EX.map (f.hom.app Q))) ≫
        TH'.map (Prod.mkHom (eX.hom.app (A.obj P)) (eX.hom.app (A.obj Q))) ≫
        TH'.map (Prod.mkHom (s'.map (c.inv.app P)) (s'.map (c.inv.app Q))) := by
    change TH'.map (Prod.mkHom
      (EX.map (f.hom.app P) ≫ eX.hom.app (A.obj P) ≫ s'.map (c.inv.app P))
      (EX.map (f.hom.app Q) ≫ eX.hom.app (A.obj Q) ≫ s'.map (c.inv.app Q))) = _
    rw [pairMap_comp, pairMap_comp]
  have hl : pre ≫ EX.map (phiF.app (q.obj P, q.obj Q)) ≫
      tauX.hom.app (F.obj (q.obj P), F.obj (q.obj Q)) ≫ post.hom =
      EX.map (f.hom.app (tK.obj (P, Q))) ≫ eX.hom.app (A.obj (tK.obj (P, Q))) ≫
        s'.map (V.map (mF.app (P, Q)) ≫ bX.app (A.obj P, A.obj Q) ≫
          tH'.map (Prod.mkHom (c.inv.app P) (c.inv.app Q))) ≫
        rH'.hom.app (⟨B.obj (U.obj P), hB _ (hU _ hp)⟩,
          ⟨B.obj (U.obj Q), hB _ (hU _ hq)⟩) := by
    dsimp only [pre]
    rw [hpost]
    rw [← reassoc_of% hnX, ← EX.map_comp_assoc, ← EX.map_comp_assoc]
    simp only [Category.assoc]
    rw [hf]
    simp only [EX.map_comp, Category.assoc]
    rw [reassoc_of% (hx (A.obj P) (A.obj Q) (hA P hp) (hA Q hq)),
      ← hnR, reassoc_of% hnE]
    simp only [s'.map_comp, Category.assoc]
  have hr : pre ≫ (alpha.inv.app (TK.obj (q.obj P, q.obj Q)) ≫
      G.map (tauY.hom.app (q.obj P, q.obj Q)) ≫
      phiG.app (EY.obj (q.obj P), EY.obj (q.obj Q)) ≫
      TH'.map (Prod.mkHom (alpha.hom.app (q.obj P)) (alpha.hom.app (q.obj Q)))) ≫
        post.hom =
      EX.map (f.hom.app (tK.obj (P, Q))) ≫ eX.hom.app (A.obj (tK.obj (P, Q))) ≫
        s'.map (c.inv.app (tK.obj (P, Q)) ≫ B.map (bY.app (P, Q)) ≫
          mG.app (U.obj P, U.obj Q)) ≫
        rH'.hom.app (⟨B.obj (U.obj P), hB _ (hU _ hp)⟩,
          ⟨B.obj (U.obj Q), hB _ (hU _ hq)⟩) := by
    dsimp only [pre]
    simp only [Category.assoc]
    change _ ≫ _ ≫ _ ≫ _ ≫
      (TH'.map (Prod.mkHom (alpha.hom.app (q.obj P)) (alpha.hom.app (q.obj Q))) ≫
        TH'.map (Prod.mkHom (d P).hom (d Q).hom)) = _
    rw [← TH'.map_comp]
    change _ ≫ _ ≫ _ ≫ _ ≫ TH'.map (Prod.mkHom
      (alpha.hom.app (q.obj P) ≫ (d P).hom)
      (alpha.hom.app (q.obj Q) ≫ (d Q).hom)) = _
    rw [hdp, hdp, pairMap_comp]
    rw [← reassoc_of% hnG, reassoc_of% hnA,
      ← G.map_comp_assoc, ← G.map_comp_assoc]
    simp only [Category.assoc]
    rw [hy]
    simp only [G.map_comp, Category.assoc]
    rw [hg (U.obj P) (U.obj Q) (hU P hp) (hU Q hq),
      reassoc_of% hnB, ← reassoc_of% hc]
    simp only [s'.map_comp, Category.assoc]
  rw [ht] at hl
  simpa only [Category.assoc] using hl.trans hr.symm

private theorem scalarCurriedSquare
    {D E D' E' : Type*}
    [Category D] [Category E] [Category D'] [Category E']
    (F : D ⥤ E) (G : D' ⥤ E') (EY : D ⥤ D') (EX : E ⥤ E')
    (alpha : EY ⋙ G ≅ F ⋙ EX)
    (TY : D ⥤ D ⥤ D) (TX : E ⥤ E ⥤ E)
    (SY : D' × D' ⥤ D') (SX : E' × E' ⥤ E')
    (phiF : (postcompose₂.obj F).obj TY ⟶
      (((whiskeringLeft₂ E).obj F).obj F).obj TX)
    (phiG : SY ⋙ G ⟶ (G.prod G) ⋙ SX)
    (tauY : (postcompose₂.obj EY).obj TY ≅
      (((whiskeringLeft₂ D').obj EY).obj EY).obj (curry.obj SY))
    (tauX : (postcompose₂.obj EX).obj TX ≅
      (((whiskeringLeft₂ E').obj EX).obj EX).obj (curry.obj SX))
    (M N : D)
    (h : EX.map (((finiteScalarUncurryPostcomposeIso TY F).hom ≫ uncurry.map phiF).app
          (M, N)) ≫
        (scalarUncurryRealization TX EX SX tauX).hom.app (F.obj M, F.obj N) =
      alpha.inv.app ((uncurry.obj TY).obj (M, N)) ≫
        G.map ((scalarUncurryRealization TY EY SY tauY).hom.app (M, N)) ≫
        phiG.app (EY.obj M, EY.obj N) ≫
        SX.map (Prod.mkHom (alpha.hom.app M) (alpha.hom.app N))) :
    EX.map ((phiF.app M).app N) ≫ ((tauX.hom.app (F.obj M)).app (F.obj N)) =
      alpha.inv.app ((TY.obj M).obj N) ≫
        G.map ((tauY.hom.app M).app N) ≫
        ((curry.map phiG ≫ (curryObjProdComp G G SX).hom).app (EY.obj M)).app (EY.obj N) ≫
        ((curry.obj SX).map (alpha.hom.app M)).app _ ≫
        ((curry.obj SX).obj _).map (alpha.hom.app N) := by
  simp only [scalarCurryComparison_app]
  simpa only [NatTrans.comp_app, finiteScalarUncurryPostcomposeIso_hom_app,
    Category.id_comp, uncurry_map_app, scalarUncurryRealization_hom_app, uncurry_obj_obj,
    Functor.curry_obj_map_app, Functor.curry_obj_obj_map, ← SX.map_comp,
    CategoryTheory.prod_comp, Category.comp_id, Category.id_comp, Category.assoc] using h

private theorem scalarCurriedTensorSquare
    {K H K' H' D E D' E' : Type*}
    [Category K] [Category H]
    [Category K'] [Category H']
    [Category D] [Category E] [Category D'] [Category E']
    (q : K ⥤ D) (s : H ⥤ E)
    (q' : K' ⥤ D') (s' : H' ⥤ E')
    (A : K ⥤ H) (B : K' ⥤ H')
    (U : K ⥤ K') (V : H ⥤ H')
    (F : D ⥤ E) (G : D' ⥤ E') (EY : D ⥤ D') (EX : E ⥤ E')
    (f : q ⋙ F ≅ A ⋙ s) (g : q' ⋙ G ≅ B ⋙ s')
    (eY : q ⋙ EY ≅ U ⋙ q') (eX : s ⋙ EX ≅ V ⋙ s')
    (c : U ⋙ B ≅ A ⋙ V) (alpha : EY ⋙ G ≅ F ⋙ EX)
    (PK : ObjectProperty K) (PH : ObjectProperty H)
    (PK' : ObjectProperty K') (PH' : ObjectProperty H')
    (hA : ∀ P, PK P → PH (A.obj P))
    (hU : ∀ P, PK P → PK' (U.obj P))
    (hV : ∀ P, PH P → PH' (V.obj P))
    (hB : ∀ P, PK' P → PH' (B.obj P))
    (tK : K × K ⥤ K) (tH : H × H ⥤ H)
    (tK' : K' × K' ⥤ K') (tH' : H' × H' ⥤ H')
    (TY : D ⥤ D ⥤ D) (TX : E ⥤ E ⥤ E)
    (TK' : D' × D' ⥤ D') (TH' : E' × E' ⥤ E')
    (rK : (PK.ι.prod PK.ι) ⋙ tK ⋙ q ≅
      ((PK.ι ⋙ q).prod (PK.ι ⋙ q)) ⋙ uncurry.obj TY)
    (rH : (PH.ι.prod PH.ι) ⋙ tH ⋙ s ≅
      ((PH.ι ⋙ s).prod (PH.ι ⋙ s)) ⋙ uncurry.obj TX)
    (rK' : (PK'.ι.prod PK'.ι) ⋙ tK' ⋙ q' ≅
      ((PK'.ι ⋙ q').prod (PK'.ι ⋙ q')) ⋙ TK')
    (rH' : (PH'.ι.prod PH'.ι) ⋙ tH' ⋙ s' ≅
      ((PH'.ι ⋙ s').prod (PH'.ι ⋙ s')) ⋙ TH')
    (mF : tK ⋙ A ⟶ (A.prod A) ⋙
      tH)
    (mG : tK' ⋙ B ⟶ (B.prod B) ⋙ tH')
    (bY : tK ⋙ U ⟶ (U.prod U) ⋙ tK')
    (bX : tH ⋙ V ⟶ (V.prod V) ⋙ tH')
    (phiF : (postcompose₂.obj F).obj TY ⟶
      (((whiskeringLeft₂ E).obj F).obj F).obj TX)
    (phiG : TK' ⋙ G ⟶ (G.prod G) ⋙ TH')
    (tauY : (postcompose₂.obj EY).obj TY ≅
      (((whiskeringLeft₂ D').obj EY).obj EY).obj (curry.obj TK'))
    (tauX : (postcompose₂.obj EX).obj TX ≅
      (((whiskeringLeft₂ E').obj EX).obj EX).obj (curry.obj TH'))
    (hf : ∀ (P Q : K) (hp : PK P) (hq : PK Q),
      F.map (rK.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ (phiF.app (q.obj P)).app (q.obj Q) ≫
        (uncurry.obj TX).map (Prod.mkHom (f.hom.app P) (f.hom.app Q)) =
      f.hom.app (tK.obj (P, Q)) ≫ s.map (mF.app (P, Q)) ≫
        rH.hom.app (⟨A.obj P, hA P hp⟩, ⟨A.obj Q, hA Q hq⟩))
    (hg : ∀ (P Q : K') (hp : PK' P) (hq : PK' Q),
      G.map (rK'.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ phiG.app (q'.obj P, q'.obj Q) ≫
        TH'.map (Prod.mkHom (g.hom.app P) (g.hom.app Q)) =
      g.hom.app (tK'.obj (P, Q)) ≫ s'.map (mG.app (P, Q)) ≫
        rH'.hom.app (⟨B.obj P, hB P hp⟩, ⟨B.obj Q, hB Q hq⟩))
    (hy : ∀ (P Q : K) (hp : PK P) (hq : PK Q),
      EY.map (rK.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ (tauY.hom.app (q.obj P)).app (q.obj Q) ≫
        TK'.map (Prod.mkHom (eY.hom.app P) (eY.hom.app Q)) =
      eY.hom.app (tK.obj (P, Q)) ≫ q'.map (bY.app (P, Q)) ≫
        rK'.hom.app (⟨U.obj P, hU P hp⟩, ⟨U.obj Q, hU Q hq⟩))
    (hx : ∀ (P Q : H) (hp : PH P) (hq : PH Q),
      EX.map (rH.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ (tauX.hom.app (s.obj P)).app (s.obj Q) ≫
        TH'.map (Prod.mkHom (eX.hom.app P) (eX.hom.app Q)) =
      eX.hom.app (tH.obj (P, Q)) ≫ s'.map (bX.app (P, Q)) ≫
        rH'.hom.app (⟨V.obj P, hV P hp⟩, ⟨V.obj Q, hV Q hq⟩))
    (hc : ∀ P : K,
      EX.map (f.hom.app P) ≫ eX.hom.app (A.obj P) ≫ s'.map (c.inv.app P) =
      alpha.inv.app (q.obj P) ≫ G.map (eY.hom.app P) ≫ g.hom.app (U.obj P))
    (ht : ∀ P Q : K,
      V.map (mF.app (P, Q)) ≫ bX.app (A.obj P, A.obj Q) ≫
        tH'.map (Prod.mkHom (c.inv.app P) (c.inv.app Q)) =
      c.inv.app (tK.obj (P, Q)) ≫ B.map (bY.app (P, Q)) ≫
        mG.app (U.obj P, U.obj Q))
    (P Q : K) (hp : PK P) (hq : PK Q) :
    EX.map ((phiF.app (q.obj P)).app (q.obj Q)) ≫
        (tauX.hom.app (F.obj (q.obj P))).app (F.obj (q.obj Q)) =
      alpha.inv.app ((TY.obj (q.obj P)).obj (q.obj Q)) ≫
        G.map ((tauY.hom.app (q.obj P)).app (q.obj Q)) ≫
        ((curry.map phiG ≫ (curryObjProdComp G G TH').hom).app
          (EY.obj (q.obj P))).app (EY.obj (q.obj Q)) ≫
        ((curry.obj TH').map (alpha.hom.app (q.obj P))).app _ ≫
        ((curry.obj TH').obj _).map (alpha.hom.app (q.obj Q)) := by
  have h := scalarTensorSquare q s q' s' A B U V F G EY EX f g eY eX c alpha
    PK PH PK' PH' hA hU hV hB tK tH
    tK' tH' (uncurry.obj TY) (uncurry.obj TX) TK' TH' rK rH rK' rH' mF mG bY bX
    ((finiteScalarUncurryPostcomposeIso TY F).hom ≫ uncurry.map phiF) phiG
    (scalarUncurryRealization TY EY TK' tauY)
    (scalarUncurryRealization TX EX TH' tauX)
    (by
      intro P Q hp hq
      simpa only [NatTrans.comp_app,
        finiteScalarUncurryPostcomposeIso_hom_app, Category.id_comp, uncurry_map_app]
        using hf P Q hp hq)
    hg
    (by
      intro P Q hp hq
      simpa only [scalarUncurryRealization_hom_app]
        using hy P Q hp hq)
    (by
      intro P Q hp hq
      simpa only [scalarUncurryRealization_hom_app]
        using hx P Q hp hq)
    hc ht P Q hp hq
  exact scalarCurriedSquare F G EY EX alpha TY TX TK' TH' phiF phiG tauY tauX
    (q.obj P) (q.obj Q) h

/-- The two tensor presentations and their specified realization equation.
All data are supplied explicitly; the last field is their compatibility proof.
Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-representative-tensor-cube). -/
structure ScalarTensorRepresentativeData
    (K H D D' : Type*) [Category K] [Category H] [Category D] [Category D']
    extends TensorFixedRepresentativeData K D where
  q' : H ⥤ D'
  U : K ⥤ H
  E : D ⥤ D'
  e : q ⋙ E ≅ U ⋙ q'
  P' : ObjectProperty H
  preserves : ∀ Z, P Z → P' (U.obj Z)
  t' : H × H ⥤ H
  T' : D' × D' ⥤ D'
  r' : (P'.ι.prod P'.ι) ⋙ t' ⋙ q' ≅ ((P'.ι ⋙ q').prod (P'.ι ⋙ q')) ⋙ T'
  b : t ⋙ U ⟶ (U.prod U) ⋙ t'
  tau : (postcompose₂.obj E).obj T ≅
    (((whiskeringLeft₂ D').obj E).obj E).obj (curry.obj T')
  normalization : ∀ (Z W : K) (hz : P Z) (hw : P W),
    E.map (r.hom.app (⟨Z, hz⟩, ⟨W, hw⟩)) ≫
        (tau.hom.app (q.obj Z)).app (q.obj W) ≫
        T'.map (Prod.mkHom (e.hom.app Z) (e.hom.app W)) =
      e.hom.app (t.obj (Z, W)) ≫
        q'.map (b.app (Z, W)) ≫
        r'.hom.app (⟨U.obj Z, preserves Z hz⟩, ⟨U.obj W, preserves W hw⟩)

/-- Two normalized representative realizations turn an ordinary chain square into
exactly the curried derived tensor square. Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-representative-tensor-cube).

Proof: uncurry the realization maps. Precompose with the source tensor
representative and postcompose with the target tensor of the exact pullback
factors followed by the ordinary comparison. Naturality moves these factors
through the tensor comparisons. The four representative equations identify the
two resulting paths with the ordinary chain square. Cancel the two isomorphisms
and express the components in curried notation. The argument does not use
nonzero objects, faithfulness of localization, or boundedness of complexes. -/
theorem finiteScalarRepresentativeTensorCube
    {K H K' H' D E D' E' : Type*}
    [Category K] [Category H]
    [Category K'] [Category H'] [Category D] [Category E] [Category D'] [Category E']
    (Y : ScalarTensorRepresentativeData K K' D D')
    (X : ScalarTensorRepresentativeData H H' E E')
    (A : K ⥤ H) (B : K' ⥤ H')
    (F : D ⥤ E) (G : D' ⥤ E')
    (f : Y.q ⋙ F ≅ A ⋙ X.q) (g : Y.q' ⋙ G ≅ B ⋙ X.q')
    (c : Y.U ⋙ B ≅ A ⋙ X.U) (alpha : Y.E ⋙ G ≅ F ⋙ X.E)
    (hA : ∀ P, Y.P P → X.P (A.obj P))
    (hB : ∀ P, Y.P' P → X.P' (B.obj P))
    (mF : Y.t ⋙ A ⟶
      (A.prod A) ⋙ X.t)
    (mG : Y.t' ⋙ B ⟶ (B.prod B) ⋙ X.t')
    (phiF : (postcompose₂.obj F).obj Y.T ⟶
      (((whiskeringLeft₂ E).obj F).obj F).obj X.T)
    (phiG : Y.T' ⋙ G ⟶ (G.prod G) ⋙ X.T')
    (hf : ∀ (P Q : K) (hp : Y.P P) (hq : Y.P Q),
      F.map (Y.r.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
          (phiF.app (Y.q.obj P)).app (Y.q.obj Q) ≫
          (uncurry.obj X.T).map (Prod.mkHom (f.hom.app P) (f.hom.app Q)) =
        f.hom.app (Y.t.obj (P, Q)) ≫
          X.q.map (mF.app (P, Q)) ≫
          X.r.hom.app (⟨A.obj P, hA P hp⟩, ⟨A.obj Q, hA Q hq⟩))
    (hg : ∀ (P Q : K') (hp : Y.P' P) (hq : Y.P' Q),
      G.map (Y.r'.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
          phiG.app (Y.q'.obj P, Y.q'.obj Q) ≫
          X.T'.map (Prod.mkHom (g.hom.app P) (g.hom.app Q)) =
        g.hom.app (Y.t'.obj (P, Q)) ≫ X.q'.map (mG.app (P, Q)) ≫
          X.r'.hom.app (⟨B.obj P, hB P hp⟩, ⟨B.obj Q, hB Q hq⟩))
    (hc : ∀ P : K,
      X.E.map (f.hom.app P) ≫ X.e.hom.app (A.obj P) ≫ X.q'.map (c.inv.app P) =
        alpha.inv.app (Y.q.obj P) ≫ G.map (Y.e.hom.app P) ≫ g.hom.app (Y.U.obj P))
    (ht : ∀ P Q : K,
      X.U.map (mF.app (P, Q)) ≫ X.b.app (A.obj P, A.obj Q) ≫
          X.t'.map (Prod.mkHom (c.inv.app P) (c.inv.app Q)) =
        c.inv.app ((Y.t).obj (P, Q)) ≫
          B.map (Y.b.app (P, Q)) ≫ mG.app (Y.U.obj P, Y.U.obj Q))
    (P Q : K) (hp : Y.P P) (hq : Y.P Q) :
    X.E.map ((phiF.app (Y.q.obj P)).app (Y.q.obj Q)) ≫
        (X.tau.hom.app (F.obj (Y.q.obj P))).app (F.obj (Y.q.obj Q)) =
      alpha.inv.app ((Y.T.obj (Y.q.obj P)).obj (Y.q.obj Q)) ≫
        G.map ((Y.tau.hom.app (Y.q.obj P)).app (Y.q.obj Q)) ≫
        ((curry.map phiG ≫ (curryObjProdComp G G X.T').hom).app
          (Y.E.obj (Y.q.obj P))).app (Y.E.obj (Y.q.obj Q)) ≫
        ((curry.obj X.T').map (alpha.hom.app (Y.q.obj P))).app _ ≫
        ((curry.obj X.T').obj _).map (alpha.hom.app (Y.q.obj Q)) := by
  exact scalarCurriedTensorSquare Y.q X.q Y.q' X.q' A B Y.U X.U F G Y.E X.E
    f g Y.e X.e c alpha Y.P X.P Y.P' X.P' hA Y.preserves X.preserves hB
    Y.t X.t Y.t' X.t' Y.T X.T Y.T' X.T' Y.r X.r Y.r' X.r' mF mG Y.b X.b phiF phiG
    Y.tau X.tau hf hg Y.normalization X.normalization hc ht P Q hp hq

end WeilConjectures
