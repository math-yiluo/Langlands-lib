/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationCube

/-! # Finite evaluation of coherent pullback tensor representatives

The representative calculation in Stacks 07A4, with the sequence evaluation
and exact inverse-image normalizations of Stacks 0941 and 03D2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  pullbackTensorSequenceInverse
  pullbackTensorSystemComparison pullbackTensorInverseEvaluationComplex
  finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorCalculus pullbackTensorSequenceDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem finiteEvaluationComparison_app {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finitePullbackTensorConstructionIso l E f n).hom.app (M, N) =
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom := by
  unfold finitePullbackTensorConstructionIso finitePullbackTensorConstruction
  rfl

/-- Finite evaluation respects the coherent tensor/pullback comparison on K-flat pairs.
Source: Stacks, sites-cohomology.tex, Lemma 21.18.4 (Tag 07A4), together with
Tags 0941 and 03D2 (blueprint: lem-pur-completed-pullback-tensor-evaluation-representatives).
Proof: choose flat-term K-flat resolutions of the displayed coherent complexes.
Their quasi-isomorphisms give isomorphisms after the derived quotient. Naturality
of both paths lets us prove the square on these resolutions and transport it
back to the displayed pair. Evaluate the resolutions in sequence degree n.
Exact evaluation preserves their K-flat tensor models, and
exact constant-coefficient inverse image preserves K-flatness. Insert the
normalization of the coherent system comparison, the evaluation tensor models,
and the two prescribed exact-pullback factorization maps. The normalization he
identifies evaluation after pullback with pullback after evaluation; hc identifies
the finite ordinary inverse image with the intrinsic one on its adjunction unit.
On a total summand of bidegree (p,q), both ordinary composites send the evaluated
unit section of x tensor y to the tensor of the two evaluated unit sections.
This follows first from the unit formula of pullbackTensorSequenceCochain, then
from hc and the ordinary evaluation mate's unit formula. Tensor sheafification
and the total-summand inclusions determine the chain maps, so the composites
are equal, including their differentials. Apply the derived quotient to this
chain equality. Naturality of the tensor-model and exact-pullback factorizations
cancels the inserted intermediate maps, giving the displayed square. Only the
K-flat representative calculation is asserted here; descent to arbitrary
objects uses resolution isomorphisms and naturality separately. -/
theorem completedPullbackTensor_evaluation_representatives {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (A : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : A.val.obj (op U)),
      (c.hom.app A).val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (n + 1))))).unit.app A).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app A).val.app (op U) x)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f)
    (he : ∀ A : CochainComplex (coefficientSequenceModules l E Y) ℤ,
      e.hom.app (DerivedCategory.Q.obj A) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app A) ≫
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app A) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)))
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) Q) :
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSystemComparison l E f).hom.app (M,N)) ≫
      ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
        ((pullbackTensorSequenceDerived l E f).obj M,
          (pullbackTensorSequenceDerived l E f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (e.hom.app M)
          (e.hom.app N)) =
    e.hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M,N)) ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N)).hom := by
  have hn := (pullbackTensorCalculus l E Y).evaluationTensor_normalization
  have hx := (pullbackTensorCalculus l E X).evaluationTensor_normalization
  have h := completedPullbackTensor_evaluation_cube_model l E f n c hc e he
    hn hx P Q hP hQ
  simpa only [finiteEvaluationComparison_app l E f n] using h

private theorem evaluationNatTrans_ext_resolving
    {B : Type*} [Category* B] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (q : B ⥤ D) (P : ObjectProperty B)
    (res : ∀ X : D, ∃ Y : B, P Y ∧ Nonempty (q.obj Y ≅ X))
    {F G : D × D ⥤ E} (a b : F ⟶ G)
    (h : ∀ Y Z : B, P Y → P Z → a.app (q.obj Y, q.obj Z) =
      b.app (q.obj Y, q.obj Z)) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨Y, hY, ⟨eY⟩⟩ := res X.1
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := res X.2
  let e := Iso.prod eY eZ
  apply (cancel_epi (F.map e.hom)).1
  rw [a.naturality, b.naturality, h Y Z hY hZ]

/-- Extend the representative square using resolution isomorphisms and naturality. -/
private theorem completedPullbackTensor_evaluation_descent {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (A : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : A.val.obj (op U)),
      (c.hom.app A).val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (n + 1))))).unit.app A).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app A).val.app (op U) x)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f)
    (he : ∀ A : CochainComplex (coefficientSequenceModules l E Y) ℤ,
      e.hom.app (DerivedCategory.Q.obj A) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app A) ≫
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app A) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)))
    (res : ∀ A : coefficientSequenceDerived l E Y,
      ∃ P : CochainComplex (coefficientSequenceModules l E Y) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := coefficientSequenceTopology (ProEt.topology Y))
          (R := coefficientSequenceCommRingSheaf l E Y) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ A))
    (M N : coefficientSequenceDerived l E Y) :
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSystemComparison l E f).hom.app (M,N)) ≫
      ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
        ((pullbackTensorSequenceDerived l E f).obj M,
          (pullbackTensorSequenceDerived l E f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (e.hom.app M)
          (e.hom.app N)) =
    e.hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M,N)) ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N)).hom := by
  let F := pullbackTensorSequenceDerived l E f
  let VY := coefficientSequenceDerivedEvaluation l E Y n
  let VX := coefficientSequenceDerivedEvaluation l E X n
  let G := finiteDerivedPullback l E n f
  let TY := (pullbackTensorCalculus l E Y).systemClosed.tensor
  let TX := finiteIntrinsicDerivedTensor l E X n
  let μ := pullbackTensorSystemComparison l E f
  let τY := (pullbackTensorCalculus l E Y).evaluationTensor n
  let τX := (pullbackTensorCalculus l E X).evaluationTensor n
  let ν := finitePullbackTensorConstructionIso l E f n
  let a : TY ⋙ F ⋙ VX ⟶ (VY ⋙ G).prod (VY ⋙ G) ⋙ TX :=
    Functor.whiskerRight μ.hom VX ≫
      Functor.whiskerLeft (F.prod F) τX.hom ≫
      Functor.whiskerRight (NatTrans.prod e.hom e.hom) TX
  let b : TY ⋙ F ⋙ VX ⟶ (VY ⋙ G).prod (VY ⋙ G) ⋙ TX :=
    Functor.whiskerLeft TY e.hom ≫
      Functor.whiskerRight τY.hom G ≫
      Functor.whiskerLeft (VY.prod VY) ν.hom
  have ha (A B : coefficientSequenceDerived l E Y) :
      a.app (A,B) = VX.map (μ.hom.app (A,B)) ≫
        τX.hom.app (F.obj A,F.obj B) ≫
        TX.map (Prod.mkHom (e.hom.app A) (e.hom.app B)) := by
    rfl
  have hb (A B : coefficientSequenceDerived l E Y) :
      b.app (A,B) = e.hom.app (TY.obj (A,B)) ≫ G.map (τY.hom.app (A,B)) ≫
        (finitePullbackTensorConstruction l E f n (VY.obj A) (VY.obj B)).hom := by
    change e.hom.app (TY.obj (A,B)) ≫ G.map (τY.hom.app (A,B)) ≫
      (finitePullbackTensorConstructionIso l E f n).hom.app (VY.obj A,VY.obj B) = _
    exact congrArg (fun t => e.hom.app (TY.obj (A,B)) ≫
      G.map (τY.hom.app (A,B)) ≫ t)
      (finiteEvaluationComparison_app l E f n (VY.obj A) (VY.obj B))
  have hab : a = b := evaluationNatTrans_ext_resolving DerivedCategory.Q
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y))
    res a b (by
      intro P Q hP hQ
      have h := completedPullbackTensor_evaluation_representatives l E f n
        c hc e he P Q hP hQ
      exact (ha _ _).trans (h.trans (hb _ _).symm))
  exact (ha M N).symm.trans ((NatTrans.congr_app hab (M,N)).trans (hb M N))

end WeilConjectures
