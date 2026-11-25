/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatNormalization
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationGenerators
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationExt

/-! # The ordinary pullback tensor evaluation square

The unit-normalized sequence and finite total tensor maps agree after evaluation.
Source: Stacks Tags 07A4, 0941 and 03D2.
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
  pullbackTensorSequenceInverse pullbackTensorSystemComparison
  pullbackTensorInverseEvaluationComplex finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorCalculus pullbackTensorSequenceDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModulePullback

attribute [local instance] sfIntrinsicPullback_additive

attribute [local implicit_reducible] integralOperationsLevelPullback
  pullbackTensorSequenceDirect coefficientSequenceEvaluation pullbackTensorSequenceBase
  pullbackTensorSequenceCochain

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  sfIntrinsicPullback coefficientSequenceEvaluation coefficientEvaluationTensorIso
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceTopology
  SheafOfModules.monoidalCategory

private theorem cochain_comp3_section
    {T : Type*} [Category* T] {J : GrothendieckTopology T} {R : Sheaf J RingCat.{u + 1}}
    {A B C D : CochainComplex (SheafOfModules.{u + 1} R) ℤ}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (i : ℤ) (U : Tᵒᵖ)
    (x : (A.X i).val.obj U) :
    ((a ≫ b ≫ c).f i).val.app U x =
      (c.f i).val.app U ((b.f i).val.app U ((a.f i).val.app U x)) := by
  rfl

-- Section transports in the chosen evaluation functors have large implicit types.
/-- Ordinary total tensor commutes with the unit-normalized evaluation mate.
Source: Stacks, sites-cohomology.tex, Tag 07A4, final total-complex comparison;
Tags 0941 and 03D2 for evaluation and the adjunction mate
(blueprint: lem-pur-completed-pullback-tensor-evaluation-cochain).
Proof: precompose with the inverse evaluation mate and the inverse ordinary
Y tensor-evaluation comparison. Transpose each degree through the finite
inverse-image adjunction. Maps out of the resulting total tensor are determined
on the pure-tensor summands. Lift their two sections through the canonical
section transports of evaluation. The evaluation comparisons preserve these
generators; the sequence tensor comparison sends the sequence unit of their
tensor to the tensor of the sequence units. The mate equation identifies those
units with finite inverse-image units, and hc transports them to the intrinsic
units. The normalization hk sends their tensor to that same pair of units.
Thus both adjuncts agree on every generator. Injectivity of the adjunction,
total-tensor extensionality and degreewise extensionality give the chain equality.
This argument uses arbitrary unbounded complexes and no K-flat or derived data.
-/
theorem completedPullbackTensor_evaluation_cochain {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
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
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (k : ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj
      ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
        (integralCoefficientCommRingSheaf l E Y n)).obj
        ((((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P),
         (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q))) ≅
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
        ((((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)),
         (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q))))
    (hk : FinitePullbackTensorGenerators l E f n
      (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)
      (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q) k) :
    let F : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
        CochainComplex (coefficientSequenceModules l E X) ℤ :=
      (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    let V : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
        CochainComplex (normalizedDVRModules l E Y n) ℤ :=
      (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)
    let W : CochainComplex (coefficientSequenceModules l E X) ℤ ⥤
        CochainComplex (normalizedDVRModules l E X n) ℤ :=
      (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)
    let G : CochainComplex (normalizedDVRModules l E Y n) ℤ ⥤
        CochainComplex (normalizedDVRModules l E X n) ℤ :=
      (sfIntrinsicPullback
        (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ)
    let d (A : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
        W.obj (F.obj A) ⟶ G.obj (V.obj A) :=
      (pullbackTensorInverseEvaluationComplex l E f n).inv.app A ≫
      (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app (V.obj A)
    W.map ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)) ≫
      (coefficientEvaluationTensorIso l E X n (F.obj P) (F.obj Q)).hom ≫
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).map
        (Prod.mkHom (d P) (d Q)) =
    (d ((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)).obj (P, Q))) ≫
      G.map (coefficientEvaluationTensorIso l E Y n P Q).hom ≫ k.hom := by
  intro F V W G dH
  apply completedPullbackTensor_evaluation_ext l E f n c hc P Q _ _ k.hom
  intro p q i hpq U x y
  have hg := completedPullbackTensor_evaluation_generators l E f n c hc P Q
    p q i hpq U x y
  have hkg := (hk p q i hpq U
    (coefficientEvaluationSection l E Y (P.X p) n (op U) x)
    (coefficientEvaluationSection l E Y (Q.X q) n (op U) y)).symm
  have hh := hg.trans hkg
  let tY := coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology Y)) (coefficientSequenceCommRingSheaf l E Y)
  let b := (pullbackTensorSequenceCochain l E f).hom.app (P, Q)
  let w := (coefficientEvaluationTensorIso l E X n (F.obj P) (F.obj Q)).hom
  let z := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n)).map (Prod.mkHom (dH P) (dH Q))
  let sg := coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y) P Q p q i hpq (op (n, U)) x y
  let su := coefficientEvaluationSection l E X
    ((pullbackTensorSequenceInverse l E f).obj ((tY.obj (P, Q)).X i)) n
    (op ((proEtaleBaseChange f).obj U))
    (((pullbackTensorSequenceAdjunction l E f).unit.app
      ((tY.obj (P, Q)).X i)).val.app (op (n, U)) sg)
  have hcomp := cochain_comp3_section (W.map b) w z i
    (op ((proEtaleBaseChange f).obj U)) su
  exact hcomp.trans hh

end WeilConjectures
