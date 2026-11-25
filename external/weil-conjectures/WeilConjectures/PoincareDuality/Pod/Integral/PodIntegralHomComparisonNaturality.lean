/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase

/-! # Naturality of the integral pullback Hom comparison

Source: Stacks Project, Tag 0GMX; blueprint main-20261015
theorem-poincare-duality-frobenius--2, Steps 8--11
(blueprint: stage3-derived-automorphism-continuation-a-integral-naturality).

The naturality field of `podIntegralHomComparison_laws`, left as a statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

private theorem ambientEvaluation_naturality
    {D : Type u} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q P' Q' : D)
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫
      S.evaluation P' Q' = S.evaluation P' Q ≫ g := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by
    ext <;> simp
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, he]
  exact Category.assoc _ _ _

private theorem ambientInverseTranspose_naturality
    {D : Type u} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (L L' P Q P' Q' : D)
    (f : L' ⟶ L) (a : P' ⟶ P) (b : Q ⟶ Q')
    (phi : L ⟶ H.obj (op P, Q)) :
    (S.transpose L' P' Q').symm (f ≫ phi ≫ H.map (Prod.mkHom a.op b)) =
      S.tensor.map (Prod.mkHom f a) ≫ (S.transpose L P Q).symm phi ≫ b := by
  let := S.monoidal
  have he (T P Q : D) (psi : T ⟶ H.obj (op P, Q)) :
      (S.transpose T P Q).symm psi =
        S.tensor.map (Prod.mkHom psi (𝟙 P)) ≫ S.evaluation P Q := by
    have ht : S.tensor.map (Prod.mkHom psi (𝟙 P)) =
        (@MonoidalCategory.tensorRight D _ S.monoidal P).map psi :=
      @MonoidalCategory.tensorHom_id D _ S.monoidal T _ psi P
    rw [ht]
    exact (S.adjunction P).homEquiv_counit (g := psi)
  rw [he, he, Category.assoc]
  have hn := S.tensor.map (Prod.mkHom (f ≫ phi) (𝟙 P')) ≫=
    ambientEvaluation_naturality S P Q P' Q' a b
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id, Category.id_comp, Category.assoc] using hn

private theorem integralTranspose_normalization
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (L : sfIntegralConstructibleCategory l E W)
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (f : (constructibleIntegralTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2) :
    ((podIntegralClosed l E W).transpose L P f).hom =
      (pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ f.hom) := by
  exact eq_of_heq ((podIntegralClosed_existsUnique l E W).exists.choose_spec L P f)

private theorem integralInverseTranspose_normalization
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (L : sfIntegralConstructibleCategory l E W)
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (phi : L ⟶ (constructibleIntegralHom l E W).obj P) :
    podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫
        (((podIntegralClosed l E W).transpose L P).symm phi).hom =
      ((pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj).symm phi.hom := by
  apply ((pullbackTensorCalculus l E W).integralClosed.transpose _ _ _).injective
  rw [← integralTranspose_normalization, AddEquiv.apply_symm_apply,
    Equiv.apply_symm_apply]

private theorem completedTensorUnit_naturality
    (W : Scheme.{u}) (M N M' N' : DerivedCategory (integralTowerModules l E W))
    (f : M ⟶ M') (h : N ⟶ N') :
    (pullbackTensorCalculus l E W).integralClosed.tensor.map (Prod.mkHom f h) ≫
        podCompletedTensorUnit l E W M' N' =
      podCompletedTensorUnit l E W M N ≫
        (integralCompletedTensor l E W).map (Prod.mkHom f h) := by
  let := (pullbackTensorCalculus l E W).integralClosed.monoidal
  simpa [podCompletedTensorUnit, CoefficientClosedStructure.tensor, Category.assoc] using
    ((Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft _ (pullbackTensorCalculus l E W).adjunction.unit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (pullbackTensorCalculus l E W).reductionTensor.hom
        (coefficientSequenceLimit l E W) ≫
      (pullbackTensorIntegralTensorModel l E W).inv).naturality (Prod.mkHom f h)

private theorem integralInverseTranspose_naturality
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (L L' : sfIntegralConstructibleCategory l E W)
    (P P' : (constructibleIntegralHomPairs l E W).FullSubcategory) (f : L' ⟶ L)
    (h : P ⟶ P') (phi : L ⟶ (constructibleIntegralHom l E W).obj P) :
    ((podIntegralClosed l E W).transpose L' P').symm
        (f ≫ phi ≫ (constructibleIntegralHom l E W).map h) =
      (constructibleIntegralTensor l E W).map (Prod.mkHom f h.hom.1.unop) ≫
        ((podIntegralClosed l E W).transpose L P).symm phi ≫ h.hom.2 := by
  have ha := ambientInverseTranspose_naturality
    (pullbackTensorCalculus l E W).integralClosed L.obj L'.obj
      P.obj.1.unop.obj P.obj.2.obj P'.obj.1.unop.obj P'.obj.2.obj
      f.hom h.hom.1.unop.hom h.hom.2.hom phi.hom
  apply ((podIntegralClosed l E W).transpose L' P').injective
  apply ObjectProperty.hom_ext
  rw [integralTranspose_normalization, integralTranspose_normalization]
  change _ = (pullbackTensorCalculus l E W).integralClosed.transpose _ _ _
    (podCompletedTensorUnit l E W _ _ ≫
      ((integralCompletedTensor l E W).map (Prod.mkHom f.hom h.hom.1.unop.hom) ≫
        (((podIntegralClosed l E W).transpose L P).symm phi).hom ≫ h.hom.2.hom))
  have hu := integralInverseTranspose_normalization l E W L P phi
  have hn := completedTensorUnit_naturality l E W L'.obj P'.obj.1.unop.obj
    L.obj P.obj.1.unop.obj f.hom h.hom.1.unop.hom
  have heq : podCompletedTensorUnit l E W L'.obj P'.obj.1.unop.obj ≫
      (integralCompletedTensor l E W).map (Prod.mkHom f.hom h.hom.1.unop.hom) ≫
      (((podIntegralClosed l E W).transpose L P).symm phi).hom ≫ h.hom.2.hom =
      (pullbackTensorCalculus l E W).integralClosed.tensor.map
        (Prod.mkHom f.hom h.hom.1.unop.hom) ≫
      ((pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj).symm phi.hom ≫ h.hom.2.hom := by
    calc
      _ = (pullbackTensorCalculus l E W).integralClosed.tensor.map
          (Prod.mkHom f.hom h.hom.1.unop.hom) ≫
          (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫
            (((podIntegralClosed l E W).transpose L P).symm phi).hom) ≫ h.hom.2.hom := by
        simpa only [Category.assoc] using congrArg (fun k ↦ k ≫
          (((podIntegralClosed l E W).transpose L P).symm phi).hom ≫ h.hom.2.hom) hn.symm
      _ = _ := by rw [hu]
  exact congrArg ((pullbackTensorCalculus l E W).integralClosed.transpose
    L'.obj P'.obj.1.unop.obj P'.obj.2.obj)
      ((integralInverseTranspose_normalization l E W L' P'
        (f ≫ phi ≫ (constructibleIntegralHom l E W).map h)).trans
        (ha.trans heq.symm))

private theorem integralEvaluation_naturality
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (P Q : (constructibleIntegralHomPairs l E W).FullSubcategory) (h : P ⟶ Q) :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom ((constructibleIntegralHom l E W).map h)
          (𝟙 Q.obj.1.unop)) ≫ (podIntegralClosed l E W).evaluation Q =
      (constructibleIntegralTensor l E W).map
        (Prod.mkHom (𝟙 ((constructibleIntegralHom l E W).obj P)) h.hom.1.unop) ≫
        (podIntegralClosed l E W).evaluation P ≫ h.hom.2 := by
  have hh := integralInverseTranspose_naturality l E W
    ((constructibleIntegralHom l E W).obj P)
    ((constructibleIntegralHom l E W).obj P) P Q (𝟙 _) h (𝟙 _)
  simp only [Category.id_comp] at hh
  dsimp only [PodPartialClosed.evaluation]
  rw [hh.symm]
  apply ((podIntegralClosed l E W).transpose _ Q).injective
  rw [(podIntegralClosed l E W).parameter_naturality]
  simp only [AddEquiv.apply_symm_apply, Category.comp_id]

/-- Naturality component of the integral pullback Hom compatibility.
Source: Stacks 0GMX; node lem-pod-derived-automorphism-hom-evaluation, steps 8--11.
Proof: both sides are maps into `H_X(FQ)`; compare their inverse transposes. The
transposition of `podIntegralClosed` is the completion-unit precomposition
followed by the ordinary tensor-Hom adjunction
(lem-pod-reindexing-completed-evaluation-reflection), hence natural in the
permitted pair as well as in the parameter, so evaluation is dinatural:
`T(H(a,b),1) ≫ ev_Q = T(1,a) ≫ ev_P ≫ b` for `(a,b) : P ⟶ Q`. With the
naturality of `μ` (lem-pur-derived-pullback-tensor-iso) the inverse transpose of
the left side becomes `T(1,Fa) ≫ μ⁻¹ ≫ F(ev_P) ≫ F b`. The right side gives
`T(1,Fa) ≫ T(c_P,1) ≫ ev ≫ F b` by the same dinaturality on `X`, and
`T(c_P,1) ≫ ev = μ⁻¹ ≫ F(ev_P)` is the evaluation equation. The transposes
agree, so the maps agree.
(blueprint: stage3-derived-automorphism-continuation-a-integral-naturality). -/
theorem podIntegralHomComparison_naturality :
    ∀ (P Q : (constructibleIntegralHomPairs l E Y).FullSubcategory) (f : P ⟶ Q),
      (constructibleIntegralPullback l E g).map
          ((constructibleIntegralHom l E Y).map f) ≫
        podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) Q =
      podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) P ≫
        (constructibleIntegralHom l E X).map
          ((podPairPullback (constructibleIntegralPullback l E g)
            (constructibleIntegralHomPairs l E Y) (constructibleIntegralHomPairs l E X)
            (podIntegralPairs_pullback l E g)).map f) := by
  intro P Q f
  let F := constructibleIntegralPullback l E g
  let H := constructibleIntegralHom l E Y
  let T := constructibleIntegralTensor l E X
  let S := podIntegralClosed l E X
  let B := podPairPullback F (constructibleIntegralHomPairs l E Y)
    (constructibleIntegralHomPairs l E X) (podIntegralPairs_pullback l E g)
  let μ := canonicalIntegralPullbackTensor l E g
  let c := podIntegralHomComparison l E g
  change F.map (H.map f) ≫ c Q = c P ≫ (constructibleIntegralHom l E X).map (B.map f)
  apply (S.transpose (F.obj (H.obj P)) (B.obj Q)).symm.injective
  have hp (L L' : sfIntegralConstructibleCategory l E X)
      (R : (constructibleIntegralHomPairs l E X).FullSubcategory) (a : L' ⟶ L)
      (z : (constructibleIntegralTensor l E X).obj (L, R.obj.1.unop) ⟶ R.obj.2) :
      (S.transpose L' R).symm (a ≫ S.transpose L R z) =
        T.map (Prod.mkHom a (𝟙 _)) ≫ z := by
    apply (S.transpose L' R).injective
    rw [S.parameter_naturality, AddEquiv.apply_symm_apply]
  have hr := integralInverseTranspose_naturality l E X
    (F.obj (H.obj P)) (F.obj (H.obj P)) (B.obj P) (B.obj Q)
    (𝟙 _) (B.map f) (c P)
  simp only [Category.id_comp] at hr
  rw [hr]
  dsimp only [c, podIntegralHomComparison, podPartialHomComparison]
  rw [hp, AddEquiv.symm_apply_apply]
  obtain ⟨eI, heI⟩ := (derivedPullbackTensorIso l E g 0 (AlgebraicClosure ℚ_[l])).2.2.2.2.2.1
  have hn₁ : T.map (Prod.mkHom (F.map (H.map f)) (𝟙 (F.obj Q.obj.1.unop))) ≫
      (μ (H.obj Q) Q.obj.1.unop).inv =
      (μ (H.obj P) Q.obj.1.unop).inv ≫ F.map
        ((constructibleIntegralTensor l E Y).map (Prod.mkHom (H.map f) (𝟙 _))) := by
    dsimp only [μ]
    rw [← heI, ← heI, Iso.app_inv, Iso.app_inv]
    simpa [Functor.comp_map, Functor.prod_map, F, T] using
      eI.inv.naturality (Prod.mkHom (H.map f) (𝟙 Q.obj.1.unop))
  have hn₂ : T.map (Prod.mkHom (𝟙 (F.obj (H.obj P))) (F.map f.hom.1.unop)) ≫
      (μ (H.obj P) P.obj.1.unop).inv =
      (μ (H.obj P) Q.obj.1.unop).inv ≫ F.map
        ((constructibleIntegralTensor l E Y).map (Prod.mkHom (𝟙 _) f.hom.1.unop)) := by
    dsimp only [μ]
    rw [← heI, ← heI, Iso.app_inv, Iso.app_inv]
    simpa [Functor.comp_map, Functor.prod_map, F, T] using
      eI.inv.naturality (Prod.mkHom (𝟙 (H.obj P)) f.hom.1.unop)
  have he := integralEvaluation_naturality l E Y P Q f
  change T.map (Prod.mkHom (F.map (H.map f)) (𝟙 (F.obj Q.obj.1.unop))) ≫
      (μ (H.obj Q) Q.obj.1.unop).inv ≫ F.map ((podIntegralClosed l E Y).evaluation Q) =
    T.map (Prod.mkHom (𝟙 (F.obj (H.obj P))) (F.map f.hom.1.unop)) ≫
      ((μ (H.obj P) P.obj.1.unop).inv ≫
        F.map ((podIntegralClosed l E Y).evaluation P)) ≫ F.map f.hom.2
  rw [← Category.assoc, hn₁, Category.assoc, ← F.map_comp, he,
    F.map_comp, F.map_comp, ← Category.assoc, ← Category.assoc, ← hn₂]
  simp only [Category.assoc]

end WeilConjectures
