/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedTensorHorizontalRepresentative

/-! # Transport of normalized tensor horizontality from representatives

Source: Stacks 06YS and 07A4.
(blueprint: lem-coef-normalized-tensor-horizontal-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w k
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard

private theorem transport_app_eq
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    {F G : C ⥤ D} (s t : F ⟶ G) {X Y : C} (e : X ≅ Y)
    (h : s.app X = t.app X) : s.app Y = t.app Y := by
  apply (cancel_epi (F.map e.hom)).1
  rw [s.naturality, t.naturality, h]

private noncomputable def transitionAdjunct
    {C : Type a} [Category.{v} C] {A : Type b} [Category.{w} A]
    {B : Type t} [Category.{u} B]
    (evm : C ⥤ A) (evn : C ⥤ B) {L : A ⥤ B} {U : B ⥤ A}
    (adj : L ⊣ U) (τ : evm ⟶ evn ⋙ U) : evm ⋙ L ⟶ evn where
  app X := (adj.homEquiv _ _).symm (τ.app X)
  naturality _ _ f :=
    adj.homEquiv_naturality_right_square (evm.map f) _ _ (evn.map f) (τ.naturality f)

private theorem tensor_transport
    {C : Type a} [Category.{v} C] {A : Type b} [Category.{w} A]
    {B : Type t} [Category.{u} B]
    (T : C × C ⥤ C) (Tm : A × A ⥤ A) (Tn : B × B ⥤ B)
    (evm : C ⥤ A) (evn : C ⥤ B) (L : A ⥤ B) (α : evm ⋙ L ⟶ evn)
    (μm : T ⋙ evm ⟶ evm.prod evm ⋙ Tm)
    (μn : T ⋙ evn ⟶ evn.prod evn ⋙ Tn)
    (β : Tm ⋙ L ⟶ L.prod L ⋙ Tn)
    {K : Type k} (q : K → C) (good : K → Prop)
    (resolve : ∀ X, ∃ P, good P ∧ Nonempty (q P ≅ X))
    (hrep : ∀ P V, good P → good V →
      L.map (μm.app (q P, q V)) ≫ β.app (evm.obj (q P), evm.obj (q V)) ≫
          Tn.map (Prod.mkHom (α.app (q P)) (α.app (q V))) =
        α.app (T.obj (q P, q V)) ≫ μn.app (q P, q V)) (X Y : C) :
    L.map (μm.app (X, Y)) ≫ β.app (evm.obj X, evm.obj Y) ≫
        Tn.map (Prod.mkHom (α.app X) (α.app Y)) =
      α.app (T.obj (X, Y)) ≫ μn.app (X, Y) := by
  let F := T ⋙ evm ⋙ L
  let G := evn.prod evn ⋙ Tn
  let s : F ⟶ G :=
    Functor.whiskerRight μm L ≫ Functor.whiskerLeft (evm.prod evm) β ≫
      Functor.whiskerRight (NatTrans.prod α α) Tn
  let t : F ⟶ G := Functor.whiskerLeft T α ≫ μn
  change s.app (X, Y) = t.app (X, Y)
  obtain ⟨P, hP, ⟨eP⟩⟩ := resolve X
  obtain ⟨V, hV, ⟨eV⟩⟩ := resolve Y
  exact transport_app_eq s t (Iso.prod eP eV) (hrep P V hP hV)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem resolve (N : coefficientSequenceDerived l E W) :
    ∃ A : CochainComplex (coefficientSequenceModules l E W) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) A ∧
      Nonempty (DerivedCategory.Q.obj A ≅ N) := by
  have := Localization.essSurj DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ))
  let B := DerivedCategory.Q.objPreimage N
  obtain ⟨A, p, hp, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) B
  have := hq
  exact ⟨A, hp, ⟨asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso N⟩⟩

set_option linter.unusedVariables false in
/-- Equality of the normalized tensor square on K-flat representatives transports to
all objects of the unbounded derived coefficient category.
Source: Stacks 06YS, 07A4; the resolving-representative transport in the proof of
Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-horizontal-transport).

Proof: resolve each derived object by a flat-term K-flat complex, apply the assumed
representative square, and cancel the epimorphic maps induced by the two resolution
isomorphisms. Naturality of the evaluation tensor and of the quotient adjunction
transports the equality along those isomorphisms. -/
theorem coefficientNormalizedTensorHorizontalTransport
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors)
    (hrep : ∀ (P V : CochainComplex (coefficientSequenceModules l E W) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) P →
      CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) V →
      ∀ {m n : ℕ} (h : n ≤ m),
        (coefficientFiniteQuotientDerived l E W h).map
            ((R.evaluationTensor m).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V)) ≫
          (Q.tensor h).hom.app
            ((coefficientSequenceDerivedEvaluation l E W m).obj (DerivedCategory.Q.obj P),
              (coefficientSequenceDerivedEvaluation l E W m).obj (DerivedCategory.Q.obj V)) ≫
          (R.finiteClosed n).tensor.map
            (Prod.mkHom
              (coefficientSequenceTransitionAdjoint l E W
                R.toCoefficientDerivedSystemTensors Q h (DerivedCategory.Q.obj P))
              (coefficientSequenceTransitionAdjoint l E W
                R.toCoefficientDerivedSystemTensors Q h (DerivedCategory.Q.obj V))) =
        coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
            (R.systemClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V)) ≫
          (R.evaluationTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V))
    (P V : coefficientSequenceDerived l E W) {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientDerived l E W h).map
        ((R.evaluationTensor m).hom.app (P, V)) ≫
      (Q.tensor h).hom.app
        ((coefficientSequenceDerivedEvaluation l E W m).obj P,
          (coefficientSequenceDerivedEvaluation l E W m).obj V) ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom
          (coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h P)
          (coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h V)) =
    coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
        (R.systemClosed.tensor.obj (P, V)) ≫
      (R.evaluationTensor n).hom.app (P, V) := by
  exact tensor_transport R.systemClosed.tensor (R.finiteClosed m).tensor
    (R.finiteClosed n).tensor (coefficientSequenceDerivedEvaluation l E W m)
    (coefficientSequenceDerivedEvaluation l E W n) (coefficientFiniteQuotientDerived l E W h)
    (transitionAdjunct _ _ (Q.adjunction h) (coefficientSequenceDerivedTransition l E W h))
    (R.evaluationTensor m).hom (R.evaluationTensor n).hom (Q.tensor h).hom
    DerivedCategory.Q.obj
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W))
    (resolve l E W) (fun A B hA hB ↦ hrep A B hA hB h) P V

end WeilConjectures
