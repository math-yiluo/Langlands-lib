/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorChainComposition
import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeSquare
import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorCompositorFactors

/-! # Pullback composition on flat K-flat tensor representatives

Source: Stacks Project, Tags 07A4 and 00YV.
(blueprint: lem-pur-finite-pullback-tensor-composition-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
section TensorSquare
variable {K H D E : Type*} [Category K] [Category H] [Category D] [Category E]
private theorem normalized_tensor_square
    (q : K ⥤ D) (q' : H ⥤ E) (t : K → K → K) (t' : H → H → H)
    (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (U V : K ⥤ H) (F G : D ⥤ E)
    (eF : q ⋙ F ⟶ U ⋙ q') (eG : q ⋙ G ⟶ V ⋙ q')
    (nF : T ⋙ F ⟶ F.prod F ⋙ T') (nG : T ⋙ G ⟶ G.prod G ⋙ T')
    (bF : ∀ P Q, U.obj (t (P) (Q)) ⟶ t' (U.obj P) (U.obj Q))
    (bG : ∀ P Q, V.obj (t (P) (Q)) ⟶ t' (V.obj P) (V.obj Q))
    (c : F ⟶ G) (a : U ⟶ V) (P Q : K)
    (am : t' (U.obj P) (U.obj Q) ⟶ t' (V.obj P) (V.obj Q))
    (r : q.obj (t (P) (Q)) ≅ T.obj (q.obj P, q.obj Q))
    (rU : q'.obj (t' (U.obj P) (U.obj Q)) ≅
      T'.obj (q'.obj (U.obj P), q'.obj (U.obj Q)))
    (rV : q'.obj (t' (V.obj P) (V.obj Q)) ≅
      T'.obj (q'.obj (V.obj P), q'.obj (V.obj Q)))
    [IsIso (eG.app P)] [IsIso (eG.app Q)]
    (hnF : F.map r.hom ≫ nF.app (q.obj P, q.obj Q) ≫
      T'.map (Prod.mkHom (eF.app P) (eF.app Q)) =
        eF.app (t (P) (Q)) ≫ q'.map (bF P Q) ≫ rU.hom)
    (hnG : G.map r.hom ≫ nG.app (q.obj P, q.obj Q) ≫
      T'.map (Prod.mkHom (eG.app P) (eG.app Q)) =
        eG.app (t (P) (Q)) ≫ q'.map (bG P Q) ≫ rV.hom)
    (hcP : c.app (q.obj P) ≫ eG.app P = eF.app P ≫ q'.map (a.app P))
    (hcQ : c.app (q.obj Q) ≫ eG.app Q = eF.app Q ≫ q'.map (a.app Q))
    (hcT : c.app (q.obj (t (P) (Q))) ≫ eG.app (t (P) (Q)) =
      eF.app (t (P) (Q)) ≫ q'.map (a.app (t (P) (Q))))
    (ha : bF P Q ≫ am =
      a.app (t (P) (Q)) ≫ bG P Q)
    (hr : q'.map (am) ≫ rV.hom =
      rU.hom ≫ T'.map (Prod.mkHom (q'.map (a.app P)) (q'.map (a.app Q)))) :
    nF.app (q.obj P, q.obj Q) ≫ T'.map (Prod.mkHom (c.app (q.obj P)) (c.app (q.obj Q))) =
      c.app (T.obj (q.obj P, q.obj Q)) ≫ nG.app (q.obj P, q.obj Q) := by
  have : IsIso (Prod.mkHom (eG.app P) (eG.app Q)) :=
    ⟨⟨Prod.mkHom (inv (eG.app P)) (inv (eG.app Q)),
      by ext <;> simp, by ext <;> simp⟩⟩
  apply (cancel_epi (F.map r.hom)).1
  apply (cancel_mono (T'.map (Prod.mkHom (eG.app P) (eG.app Q)))).1
  simp only [Category.assoc]
  rw [← T'.map_comp]
  have hp : Prod.mkHom (c.app (q.obj P)) (c.app (q.obj Q)) ≫
      Prod.mkHom (eG.app P) (eG.app Q) =
      Prod.mkHom (eF.app P) (eF.app Q) ≫
        Prod.mkHom (q'.map (a.app P)) (q'.map (a.app Q)) := by
    ext <;> first | exact hcP | exact hcQ
  rw [hp, T'.map_comp]
  calc
    _ = (F.map r.hom ≫ nF.app (q.obj P, q.obj Q) ≫
        T'.map (Prod.mkHom (eF.app P) (eF.app Q))) ≫
        T'.map (Prod.mkHom (q'.map (a.app P)) (q'.map (a.app Q))) := by
      simp only [Category.assoc]
    _ = eF.app (t (P) (Q)) ≫ q'.map (bF P Q) ≫
        rU.hom ≫ T'.map (Prod.mkHom (q'.map (a.app P)) (q'.map (a.app Q))) := by
      rw [hnF]; simp only [Category.assoc]
    _ = eF.app (t (P) (Q)) ≫
        q'.map (bF P Q ≫ am) ≫ rV.hom := by
      rw [q'.map_comp]; simp only [Category.assoc, hr]
    _ = (c.app (q.obj (t (P) (Q))) ≫ eG.app (t (P) (Q))) ≫
        q'.map (bG P Q) ≫ rV.hom := by
      rw [ha, q'.map_comp, hcT]; simp only [Category.assoc]
    _ = c.app (q.obj (t (P) (Q))) ≫ G.map r.hom ≫
        nG.app (q.obj P, q.obj Q) ≫ T'.map (Prod.mkHom (eG.app P) (eG.app Q)) := by
      simp only [Category.assoc]
      rw [← hnG]
    _ = _ := by
      have hn := c.naturality r.hom
      change F.map r.hom ≫ c.app (T.obj (q.obj P, q.obj Q)) =
        c.app (q.obj (t (P) (Q))) ≫ G.map r.hom at hn
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ nG.app (q.obj P, q.obj Q) ≫
          T'.map (Prod.mkHom (eG.app P) (eG.app Q))) hn.symm

private theorem composite_tensor_square
    {L Z : Type*} [Category L] [Category Z]
    (q : K ⥤ D) (q' : H ⥤ E) (q'' : L ⥤ Z)
    (t : K → K → K) (t' : H → H → H) (t'' : L → L → L)
    (T : D × D ⥤ D) (T' : E × E ⥤ E) (T'' : Z × Z ⥤ Z)
    (U : K ⥤ H) (V : H ⥤ L) (F : D ⥤ E) (G : E ⥤ Z)
    (eF : q ⋙ F ⟶ U ⋙ q') (eG : q' ⋙ G ⟶ V ⋙ q'')
    (nF : T ⋙ F ⟶ F.prod F ⋙ T') (nG : T' ⋙ G ⟶ G.prod G ⋙ T'')
    (bF : ∀ P Q, U.obj (t (P) (Q)) ⟶ t' (U.obj P) (U.obj Q))
    (bG : ∀ P Q, V.obj (t' (P) (Q)) ⟶ t'' (V.obj P) (V.obj Q))
    (P Q : K)
    (r : q.obj (t (P) (Q)) ≅ T.obj (q.obj P, q.obj Q))
    (r' : q'.obj (t' (U.obj P) (U.obj Q)) ≅
      T'.obj (q'.obj (U.obj P), q'.obj (U.obj Q)))
    (r'' : q''.obj (t'' (V.obj (U.obj P)) (V.obj (U.obj Q))) ≅
      T''.obj (q''.obj (V.obj (U.obj P)), q''.obj (V.obj (U.obj Q))))
    (hF : F.map r.hom ≫ nF.app (q.obj P, q.obj Q) ≫
      T'.map (Prod.mkHom (eF.app P) (eF.app Q)) =
        eF.app (t (P) (Q)) ≫ q'.map (bF P Q) ≫ r'.hom)
    (hG : G.map r'.hom ≫ nG.app (q'.obj (U.obj P), q'.obj (U.obj Q)) ≫
      T''.map (Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q))) =
        eG.app (t' (U.obj P) (U.obj Q)) ≫
          q''.map (bG (U.obj P) (U.obj Q)) ≫ r''.hom) :
    G.map (F.map r.hom) ≫
        (G.map (nF.app (q.obj P, q.obj Q)) ≫
          nG.app (F.obj (q.obj P), F.obj (q.obj Q))) ≫
        T''.map (Prod.mkHom
          (G.map (eF.app P) ≫ eG.app (U.obj P))
          (G.map (eF.app Q) ≫ eG.app (U.obj Q))) =
      (G.map (eF.app (t (P) (Q))) ≫ eG.app (U.obj (t (P) (Q)))) ≫
        q''.map (V.map (bF P Q) ≫ bG (U.obj P) (U.obj Q)) ≫ r''.hom := by
  have hp : Prod.mkHom
      (G.map (eF.app P) ≫ eG.app (U.obj P))
      (G.map (eF.app Q) ≫ eG.app (U.obj Q)) =
      Prod.mkHom (G.map (eF.app P)) (G.map (eF.app Q)) ≫
        Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q)) := rfl
  have hn := nG.naturality (Prod.mkHom (eF.app P) (eF.app Q))
  change G.map (T'.map (Prod.mkHom (eF.app P) (eF.app Q))) ≫
      nG.app (q'.obj (U.obj P), q'.obj (U.obj Q)) =
    nG.app (F.obj (q.obj P), F.obj (q.obj Q)) ≫
      T''.map (Prod.mkHom (G.map (eF.app P)) (G.map (eF.app Q))) at hn
  simp only [hp, T''.map_comp, Category.assoc]
  have hn' := congrArg
    (fun z ↦ z ≫ T''.map (Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q)))) hn
  simp only [Category.assoc] at hn'
  rw [← hn']
  have he := eG.naturality (bF P Q)
  change G.map (q'.map (bF P Q)) ≫
      eG.app (t' (U.obj P) (U.obj Q)) =
    eG.app (U.obj (t (P) (Q))) ≫ q''.map (V.map (bF P Q)) at he
  calc
    _ = G.map (F.map r.hom ≫ nF.app (q.obj P, q.obj Q) ≫
        T'.map (Prod.mkHom (eF.app P) (eF.app Q))) ≫
        nG.app (q'.obj (U.obj P), q'.obj (U.obj Q)) ≫
        T''.map (Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q))) := by
      simp only [G.map_comp, Category.assoc]
    _ = G.map (eF.app (t (P) (Q))) ≫ G.map (q'.map (bF P Q)) ≫
        G.map r'.hom ≫ nG.app (q'.obj (U.obj P), q'.obj (U.obj Q)) ≫
        T''.map (Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q))) := by
      rw [hF]; simp only [G.map_comp, Category.assoc]
    _ = G.map (eF.app (t (P) (Q))) ≫ G.map (q'.map (bF P Q)) ≫
        eG.app (t' (U.obj P) (U.obj Q)) ≫
        q''.map (bG (U.obj P) (U.obj Q)) ≫ r''.hom := by
      rw [hG]
    _ = _ := by
      simpa only [Category.assoc, q''.map_comp] using congrArg
        (fun z ↦ G.map (eF.app (t (P) (Q))) ≫ z ≫
          q''.map (bG (U.obj P) (U.obj Q)) ≫ r''.hom) he

end TensorSquare

namespace WeilConjectures
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf finiteIntrinsicDerivedTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open FinitePullbackTensorRep
open CategoryTheory.Functor

private theorem representative_naturality (W : Scheme.{u}) (n : ℕ)
    (P Q P' Q' : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) P)
    (hQ : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) Q)
    (hP' : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) P')
    (hQ' : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) Q')
    (a : P ⟶ P') (b : Q ⟶ Q') :
    DerivedCategory.Q.map ((totalTensor l E W n).map (Prod.mkHom a b)) ≫
        (representative l E W n P' Q' hP' hQ').hom =
      (representative l E W n P Q hP hQ).hom ≫
        (finiteIntrinsicDerivedTensor l E W n).map
          (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) := by
  let p := proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n)
  let i := p.ι ⋙ DerivedCategory.Q
  let r := (pullbackTensorFiniteModel l E W n).representative ≪≫
    isoWhiskerLeft (i.prod i) (pullbackTensorFiniteModelIso l E W n)
  unfold representative
  exact r.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := ⟨P', hP'⟩) a)
      (ObjectProperty.homMk (X := ⟨Q, hQ⟩) (Y := ⟨Q', hQ'⟩) b))

private theorem constructionIso_app {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finitePullbackTensorConstructionIso l E f n).hom.app (M, N) =
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom := by
  unfold finitePullbackTensorConstructionIso finitePullbackTensorConstruction
  rfl

/-- Composition coherence restricted to the specified flat K-flat complexes.
Source: Stacks 07A4, lemma-pullback-tensor-product, and 00YV, composition of
inverse images (blueprint: lem-pur-finite-pullback-tensor-composition-representatives).
Proof: use the canonical total-tensor normalization square for f, h and h ≫ f.
Pullback preserves flat K-flat complexes, so the square for h applies to the
termwise pullbacks of P and Q. On each bidegree summand the direct pullback
of x tensor y and the iterated pullback both map to h*f*x tensor h*f*y.
The ordinary adjunction compositor identifies the unit sections in these two
expressions. Bilinearity, sheafification and the direct-sum total injections
prove equality of the chain maps. Apply the derived quotient and insert the
recorded tensor-model and unit-normalized realization isomorphisms. Naturality
cancels the realization conjugations, and the derived ordinary compositor is
sfIntrinsicDerivedPullbackComp. This gives the displayed equation only on
localized flat K-flat pairs; no extension to arbitrary derived objects is used. -/
theorem finitePullbackTensor_composition_representatives {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) P)
    (hQ : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) Q) :
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    ((@finitePullbackTensorConstruction l _ E _ _ _ Z Y (h ≫ f) n hZ hY) M N).hom ≫
      (finiteIntrinsicDerivedTensor l E Z n).map
        (Prod.mkHom
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app M)
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app N)) =
    (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) ≫
      (finiteDerivedPullback l E n h).map
        ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ Z X h n hZ hX)
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)).hom := by
  let F := finiteDerivedPullback l E n f
  let H := finiteDerivedPullback l E n h
  let K := finiteDerivedPullback l E n (h ≫ f)
  let TY := finiteIntrinsicDerivedTensor l E Y n
  let TX := finiteIntrinsicDerivedTensor l E X n
  let TZ := finiteIntrinsicDerivedTensor l E Z n
  let U := pull l E f n
  let V := pull l E h n
  let W := pull l E (h ≫ f) n
  let μf := finitePullbackTensorConstructionIso l E f n
  let μh := finitePullbackTensorConstructionIso l E h n
  let μk := finitePullbackTensorConstructionIso l E (h ≫ f) n
  let eF := (factors l E f n).hom
  let eH := (factors l E h n).hom
  let eK := (factors l E (h ≫ f) n).hom
  let e : DerivedCategory.Q ⋙ (F ⋙ H) ⟶ (U ⋙ V) ⋙ DerivedCategory.Q :=
    whiskerRight eF H ≫ whiskerLeft U eH
  let μ : TY ⋙ (F ⋙ H) ⟶ (F ⋙ H).prod (F ⋙ H) ⋙ TZ :=
    whiskerRight μf.hom H ≫ whiskerLeft (F.prod F) μh.hom
  let c := sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f
  let a := complexComp l E f h n
  obtain ⟨hFP, hFQ, hf⟩ := square l E f n P Q hP hQ
  obtain ⟨hHFP, hHFQ, hh⟩ := square l E h n (U.obj P) (U.obj Q) hFP hFQ
  obtain ⟨hKP, hKQ, hk⟩ := square l E (h ≫ f) n P Q hP hQ
  rw [← constructionIso_app] at hf hh hk
  have hi := composite_tensor_square
    (quotient l E Y n) (quotient l E X n) (quotient l E Z n)
    (tensor l E Y n) (tensor l E X n) (tensor l E Z n) TY TX TZ U V F H
    eF eH μf.hom μh.hom (comparison l E f n) (comparison l E h n) P Q
    (representative l E Y n P Q hP hQ)
    (representative l E X n (U.obj P) (U.obj Q) hFP hFQ)
    (representative l E Z n (V.obj (U.obj P)) (V.obj (U.obj Q)) hHFP hHFQ) hf hh
  have : IsIso (e.app P) := by
    change IsIso (H.map ((factors l E f n).hom.app P) ≫
      (factors l E h n).hom.app (U.obj P))
    infer_instance
  have : IsIso (e.app Q) := by
    change IsIso (H.map ((factors l E f n).hom.app Q) ≫
      (factors l E h n).hom.app (U.obj Q))
    infer_instance
  have hc := normalized_tensor_square (quotient l E Y n) (quotient l E Z n)
    (tensor l E Y n) (tensor l E Z n) TY TZ W (U ⋙ V) K (F ⋙ H) eK e
    μk.hom μ (comparison l E (h ≫ f) n)
    (fun A B ↦ V.map (comparison l E f n A B) ≫ comparison l E h n (U.obj A) (U.obj B))
    c.hom a.hom P Q
    ((totalTensor l E Z n).map (Prod.mkHom (a.hom.app P) (a.hom.app Q)))
    (representative l E Y n P Q hP hQ)
    (representative l E Z n (W.obj P) (W.obj Q) hKP hKQ)
    (representative l E Z n (V.obj (U.obj P)) (V.obj (U.obj Q)) hHFP hHFQ)
    hk (by
      dsimp only [Functor.comp_obj, Functor.comp_map, Functor.prod] at hi ⊢
      simpa only [e, μ, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
        Functor.prod, Category.assoc] using hi)
    (by simpa only [e, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Category.assoc] using compositor_fac l E f h n P)
    (by simpa only [e, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Category.assoc] using compositor_fac l E f h n Q)
    (by simpa only [e, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Category.assoc] using compositor_fac l E f h n (tensor l E Y n P Q))
    (chain_composition l E f h n P Q)
    (representative_naturality l E Z n (W.obj P) (W.obj Q)
      (V.obj (U.obj P)) (V.obj (U.obj Q)) hKP hKQ hHFP hHFQ
      (a.hom.app P) (a.hom.app Q))
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.prod] at hc
  simpa only [μk, μf, μh, μ, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, Functor.prod, quotient, constructionIso_app] using hc

end WeilConjectures
