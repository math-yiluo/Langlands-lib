/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Whiskering
/-! # Transport of counit-normalized scalar comparisons
Source: adjunction conjugation in Zheng, Lemma 5.22.
(blueprint: lem-sf-scalar-comparison-transport)
-/
@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
namespace WeilConjectures.ExceptionalScalarTransport
section
universe a b c d x y p q av bv cv dv xv yv pv qv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {P : Type p} [Category.{pv} P] {Q : Type q} [Category.{qv} Q]
  {F : A ⥤ B} {G : B ⥤ A} {F' : X ⥤ Y} {G' : Y ⥤ X}
  {H : C ⥤ D} {I : D ⥤ C} {H' : P ⥤ Q} {I' : Q ⥤ P}
  (adj : F ⊣ G) (adj' : F' ⊣ G') (hadj : H ⊣ I) (hadj' : H' ⊣ I')
  {ex : A ⥤ X} {ey : B ⥤ Y} {rx : C ⥤ P} {ry : D ⥤ Q}
  {SX : A ⥤ C} {SY : B ⥤ D} {TX : X ⥤ P} {TY : Y ⥤ Q}
  (fE : F ⋙ ey ≅ ex ⋙ F') (gE : G ⋙ ex ≅ ey ⋙ G')
  (fL : H ⋙ ry ≅ rx ⋙ H') (gL : I ⋙ rx ≅ ry ⋙ I')
  (sx : SX ⋙ rx ≅ ex ⋙ TX) (sy : SY ⋙ ry ≅ ey ⋙ TY)
  (q₀ : F ⋙ SY ≅ SX ⋙ H) (b₀ : G ⋙ SX ⟶ SY ⋙ I)
  (q₁ : F' ⋙ TY ≅ TX ⋙ H') (b₁ : G' ⋙ TX ⟶ TY ⋙ I')
  (hc : ∀ N, q₀.hom.app (G.obj N) ≫ H.map (b₀.app N) ≫
    hadj.counit.app (SY.obj N) = SY.map (adj.counit.app N))
  (hcE : ∀ N, fE.hom.app (G.obj N) ≫ F'.map (gE.hom.app N) ≫
    adj'.counit.app (ey.obj N) = ey.map (adj.counit.app N))
  (hcL : ∀ N, fL.hom.app (I.obj N) ≫ H'.map (gL.hom.app N) ≫
    hadj'.counit.app (ry.obj N) = ry.map (hadj.counit.app N))
  (hqr : ∀ K, ry.map (q₀.hom.app K) ≫ fL.hom.app (SX.obj K) ≫
    H'.map (sx.hom.app K) = sy.hom.app (F.obj K) ≫ TY.map (fE.hom.app K) ≫
      q₁.hom.app (ex.obj K))
  (hbr : ∀ N, rx.map (b₀.app N) ≫ gL.hom.app (SY.obj N) ≫
    I'.map (sy.hom.app N) = sx.hom.app (G.obj N) ≫ TX.map (gE.hom.app N) ≫
      b₁.app (ey.obj N))
include hc hcE hcL hqr hbr in
private theorem transportCounit (N : B) :
    q₁.hom.app (G'.obj (ey.obj N)) ≫ H'.map (b₁.app (ey.obj N)) ≫
      hadj'.counit.app (TY.obj (ey.obj N)) = TY.map (adj'.counit.app (ey.obj N)) := by
  apply (cancel_epi (sy.hom.app (F.obj (G.obj N)) ≫
    TY.map (fE.hom.app (G.obj N)) ≫ TY.map (F'.map (gE.hom.app N)))).mp
  have hq := q₁.hom.naturality (gE.hom.app N)
  have hf := fL.hom.naturality (b₀.app N)
  have hs := sy.hom.naturality (adj.counit.app N)
  have he := hadj'.counit.naturality (sy.hom.app N)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hq hf hs he
  simp only [Category.assoc]
  calc
    _ = sy.hom.app (F.obj (G.obj N)) ≫ TY.map (fE.hom.app (G.obj N)) ≫
        q₁.hom.app (ex.obj (G.obj N)) ≫
        H'.map (TX.map (gE.hom.app N)) ≫ H'.map (b₁.app (ey.obj N)) ≫
        hadj'.counit.app (TY.obj (ey.obj N)) := by rw [reassoc_of% hq]
    _ = ry.map (q₀.hom.app (G.obj N)) ≫ fL.hom.app (SX.obj (G.obj N)) ≫
        H'.map (sx.hom.app (G.obj N)) ≫ H'.map (TX.map (gE.hom.app N)) ≫
        H'.map (b₁.app (ey.obj N)) ≫ hadj'.counit.app (TY.obj (ey.obj N)) := by
      rw [← reassoc_of% (hqr (G.obj N))]
    _ = ry.map (q₀.hom.app (G.obj N)) ≫ fL.hom.app (SX.obj (G.obj N)) ≫
        H'.map (rx.map (b₀.app N)) ≫ H'.map (gL.hom.app (SY.obj N)) ≫
        H'.map (I'.map (sy.hom.app N)) ≫ hadj'.counit.app (TY.obj (ey.obj N)) := by
      rw [← H'.map_comp_assoc, ← H'.map_comp_assoc, Category.assoc, ← hbr]
      simp only [H'.map_comp, Category.assoc]
    _ = ry.map (q₀.hom.app (G.obj N)) ≫ ry.map (H.map (b₀.app N)) ≫
        fL.hom.app (I.obj (SY.obj N)) ≫ H'.map (gL.hom.app (SY.obj N)) ≫
        hadj'.counit.app (ry.obj (SY.obj N)) ≫ sy.hom.app N := by
      rw [← reassoc_of% hf, he]
    _ = ry.map (q₀.hom.app (G.obj N)) ≫ ry.map (H.map (b₀.app N)) ≫
        ry.map (hadj.counit.app (SY.obj N)) ≫ sy.hom.app N := by
      rw [reassoc_of% (hcL (SY.obj N))]
    _ = ry.map (SY.map (adj.counit.app N)) ≫ sy.hom.app N := by
      rw [← ry.map_comp_assoc, ← ry.map_comp_assoc, Category.assoc, hc]
    _ = sy.hom.app (F.obj (G.obj N)) ≫ TY.map (ey.map (adj.counit.app N)) := hs
    _ = _ := by
      rw [← hcE]
      simp only [TY.map_comp]
end

section
universe a b x y p q av bv xv yv pv qv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {P : Type p} [Category.{pv} P] {Q : Type q} [Category.{qv} Q]
  {F : X ⥤ Y} {G : Y ⥤ X} (adj : F ⊣ G)
  {H : P ⥤ Q} {I : Q ⥤ P} (adj' : H ⊣ I)
  {TX : X ⥤ P} {TY : Y ⥤ Q}
  (eY : B ≌ Y) (q : F ⋙ TY ≅ TX ⋙ H) (b : G ⋙ TX ⟶ TY ⋙ I)
  (h : ∀ K : B, q.hom.app (G.obj (eY.functor.obj K)) ≫
    H.map (b.app (eY.functor.obj K)) ≫
    adj'.counit.app (TY.obj (eY.functor.obj K)) =
    TY.map (adj.counit.app (eY.functor.obj K)))
include h in
private theorem counit_of_image (N : Y) :
    q.hom.app (G.obj N) ≫ H.map (b.app N) ≫ adj'.counit.app (TY.obj N) =
      TY.map (adj.counit.app N) := by
  let K := eY.inverse.obj N
  let e := eY.counitIso.app N
  have hh := h K
  have hnq := q.hom.naturality (G.map e.hom)
  have hnb := b.naturality e.hom
  have hnc := adj.counit.naturality e.hom
  have hnl := adj'.counit.naturality (TY.map e.hom)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hnq hnb hnc hnl
  apply (cancel_epi (TY.map (F.map (G.map e.hom)))).mp
  calc
    _ = q.hom.app (G.obj (eY.functor.obj K)) ≫
        H.map (TX.map (G.map e.hom)) ≫ H.map (b.app N) ≫
        adj'.counit.app (TY.obj N) := by rw [reassoc_of% hnq]
    _ = q.hom.app (G.obj (eY.functor.obj K)) ≫
        H.map (b.app (eY.functor.obj K)) ≫ H.map (I.map (TY.map e.hom)) ≫
        adj'.counit.app (TY.obj N) := by
      rw [← H.map_comp_assoc, hnb]
      simp only [Functor.map_comp, Category.assoc, K]
    _ = TY.map (adj.counit.app (eY.functor.obj K)) ≫ TY.map e.hom := by
      rw [hnl]
      simpa only [Category.assoc, K] using congrArg (fun z ↦ z ≫ TY.map e.hom) hh
    _ = _ := by
      simpa only [TY.map_comp, K] using congrArg TY.map hnc.symm
end

section
universe c d cv dv
variable {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
private theorem cancelIsos (S : C ⥤ D) {X Y : C} {A B : D}
    (r : A ≅ S.obj X) (e : X ≅ Y) (k : A ⟶ B) :
    k = r.hom ≫ S.map e.hom ≫ S.map e.inv ≫ r.inv ≫ k := by
  simp only [← S.map_comp_assoc, Iso.hom_inv_id, S.map_id,
    Category.id_comp, Iso.hom_inv_id_assoc]
end

section
universe a b c d x y p q av bv cv dv xv yv pv qv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {P : Type p} [Category.{pv} P] {Q : Type q} [Category.{qv} Q]
  {F : A ⥤ B} {G : B ⥤ A} {F' : X ⥤ Y} {G' : Y ⥤ X}
  {H : C ⥤ D} {I : D ⥤ C} {H' : P ⥤ Q} {I' : Q ⥤ P}
  (adj : F ⊣ G) (adj' : F' ⊣ G') (hadj : H ⊣ I) (hadj' : H' ⊣ I')
  (ex : A ≌ X) (ey : B ≌ Y) {rx : C ⥤ P} {ry : D ⥤ Q}
  {SX : A ⥤ C} {SY : B ⥤ D} {TX : X ⥤ P} {TY : Y ⥤ Q}
  (fE : F ⋙ ey.functor ≅ ex.functor ⋙ F')
  (gE : G ⋙ ex.functor ≅ ey.functor ⋙ G')
  (fL : H ⋙ ry ≅ rx ⋙ H') (gL : I ⋙ rx ≅ ry ⋙ I')
  (sx : SX ⋙ rx ≅ ex.functor ⋙ TX) (sy : SY ⋙ ry ≅ ey.functor ⋙ TY)
  (q₀ : F ⋙ SY ≅ SX ⋙ H) (b₀ : G ⋙ SX ≅ SY ⋙ I)
  (hc : ∀ N, q₀.hom.app (G.obj N) ≫ H.map (b₀.hom.app N) ≫
    hadj.counit.app (SY.obj N) = SY.map (adj.counit.app N))
  (hcE : ∀ N, fE.hom.app (G.obj N) ≫ F'.map (gE.hom.app N) ≫
    adj'.counit.app (ey.functor.obj N) = ey.functor.map (adj.counit.app N))
  (hcL : ∀ N, fL.hom.app (I.obj N) ≫ H'.map (gL.hom.app N) ≫
    hadj'.counit.app (ry.obj N) = ry.map (hadj.counit.app N))

include adj hadj hc hcE hcL

/-- Descend scalar mates through equivalences, preserving both reduction squares and
counit normalization.
Source: Zheng, Lemma 5.22, categorical adjunction transport.
Proof: conjugate q and b with the three given squares and descend along source whiskering,
which is fully faithful because the source functor is an equivalence. Cancel inverse
factors to prove the reduction equations. Cancel the invertible left reduction factors
in the desired counit equation and use naturality and the three given counit identities.
This proves it on the source equivalence image; naturality and its counit isomorphism
extend the equation to every target object.
(blueprint: lem-sf-scalar-comparison-transport). -/
theorem transportComparisons :
    ∃ (q : F' ⋙ TY ≅ TX ⋙ H') (b : G' ⋙ TX ≅ TY ⋙ I'),
      (∀ N, q.hom.app (G'.obj N) ≫ H'.map (b.hom.app N) ≫
        hadj'.counit.app (TY.obj N) = TY.map (adj'.counit.app N)) ∧
      (∀ K, ry.map (q₀.hom.app K) ≫ fL.hom.app (SX.obj K) ≫
        H'.map (sx.hom.app K) = sy.hom.app (F.obj K) ≫ TY.map (fE.hom.app K) ≫
          q.hom.app (ex.functor.obj K)) ∧
      (∀ N, rx.map (b₀.hom.app N) ≫ gL.hom.app (SY.obj N) ≫
        I'.map (sy.hom.app N) = sx.hom.app (G.obj N) ≫ TX.map (gE.hom.app N) ≫
          b.hom.app (ey.functor.obj N)) := by
  let qp : ex.functor ⋙ (F' ⋙ TY) ≅ ex.functor ⋙ (TX ⋙ H') :=
    isoWhiskerRight fE.symm TY ≪≫ isoWhiskerLeft F sy.symm ≪≫
      isoWhiskerRight q₀ ry ≪≫ isoWhiskerLeft SX fL ≪≫ isoWhiskerRight sx H'
  let bp : ey.functor ⋙ (G' ⋙ TX) ≅ ey.functor ⋙ (TY ⋙ I') :=
    isoWhiskerRight gE.symm TX ≪≫ isoWhiskerLeft G sx.symm ≪≫
      isoWhiskerRight b₀ rx ≪≫ isoWhiskerLeft SY gL ≪≫ isoWhiskerRight sy I'
  let q : F' ⋙ TY ≅ TX ⋙ H' :=
    ((whiskeringLeft _ _ _).obj ex.functor).preimageIso qp
  let b : G' ⋙ TX ≅ TY ⋙ I' :=
    ((whiskeringLeft _ _ _).obj ey.functor).preimageIso bp
  have hq (K) : q.hom.app (ex.functor.obj K) = qp.hom.app K :=
    congrArg (fun z ↦ z.app K)
      (((whiskeringLeft _ _ _).obj ex.functor).map_preimage qp.hom)
  have hb (N) : b.hom.app (ey.functor.obj N) = bp.hom.app N :=
    congrArg (fun z ↦ z.app N)
      (((whiskeringLeft _ _ _).obj ey.functor).map_preimage bp.hom)
  have hqr (K) : ry.map (q₀.hom.app K) ≫ fL.hom.app (SX.obj K) ≫
      H'.map (sx.hom.app K) = sy.hom.app (F.obj K) ≫ TY.map (fE.hom.app K) ≫
        q.hom.app (ex.functor.obj K) := by
    rw [hq]
    dsimp only [qp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app]
    simpa only [Category.assoc, Iso.app_hom, Iso.app_inv, Functor.comp_obj] using
      cancelIsos TY (sy.app (F.obj K)) (fE.app K)
        (ry.map (q₀.hom.app K) ≫ fL.hom.app (SX.obj K) ≫ H'.map (sx.hom.app K))
  have hbr (N) : rx.map (b₀.hom.app N) ≫ gL.hom.app (SY.obj N) ≫
      I'.map (sy.hom.app N) = sx.hom.app (G.obj N) ≫ TX.map (gE.hom.app N) ≫
        b.hom.app (ey.functor.obj N) := by
    rw [hb]
    dsimp only [bp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app]
    simpa only [Category.assoc, Iso.app_hom, Iso.app_inv, Functor.comp_obj] using
      cancelIsos TX (sx.app (G.obj N)) (gE.app N)
        (rx.map (b₀.hom.app N) ≫ gL.hom.app (SY.obj N) ≫ I'.map (sy.hom.app N))
  refine ⟨q, b, ?_, hqr, hbr⟩
  exact counit_of_image adj' hadj' ey q b.hom
    (transportCounit adj adj' hadj hadj' fE gE fL gL sx sy q₀ b₀.hom q b.hom
      hc hcE hcL hqr hbr)
end
end WeilConjectures.ExceptionalScalarTransport
