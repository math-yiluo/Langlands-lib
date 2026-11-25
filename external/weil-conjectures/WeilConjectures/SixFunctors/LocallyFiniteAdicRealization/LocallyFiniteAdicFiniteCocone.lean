/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSystem
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRationalTensorCocone
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite native realization cocones

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

variable (C : CoefficientSystem l X)
variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]

/-- A finite-field realization cocone. Every comparison is specified before descent;
no functor on the pair category, Hom descent, or essential-image assertion is assumed.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-finite-cocone). -/
structure FiniteCoconeData where
  Φ : ∀ E : Index l (PadicAlgCl l),
    GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E ⥤
      DerivedCategory (ProEtale.AdicSheaf l X)
  [additive : ∀ E, (Φ E).Additive]
  [shift : ∀ E, (Φ E).CommShift ℤ]
  triangulated : ∀ E, (Φ E).IsTriangulated
  ι : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙ Φ L ≅ Φ E
  coherence : ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (h' : L ≤ M)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E),
    (Φ M).map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).assoc
          h h').hom.app K) ≫ (ι (h.trans h')).hom.app K =
      (ι h').hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj K) ≫
          (ι h).hom.app K
  [transitionShift : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
    NatTrans.CommShift (ι h).hom ℤ]
  integral : ∀ E : Index l (PadicAlgCl l),
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      Φ E ⋙ (sections l X).mapDerivedCategory ≅
      ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
        pbcDerivedExtend.{u} ((C.coefficient E).integralMap l X)

/-- The finite-stage completion-map equation, before pair-category descent.
Source: Bhatt--Scholze, Proposition 6.8.14, Remark 6.8.15
(blueprint: lem-sf-locally-finite-adic-finite-cocone). -/
@[irreducible] def FiniteCoconeData.normalized (A : FiniteCoconeData l X C) : Prop :=
  ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    HEq
      ((sections l X).mapDerivedCategory.map
        ((A.ι h).inv.app ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)))
      ((A.integral E).hom.app K ≫
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((C.coefficient L).integralMap l X) ((C.coefficient E).integralMap l X)
          (C.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((C.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj) ≫
        (A.integral L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
            E L h).obj K))

/-- The finite realization data with its completion-map equation.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-finite-cocone). -/
structure FiniteCocone extends FiniteCoconeData l X C where
  normalization : toFiniteCoconeData.normalized l X C

-- These are category aliases; expose only their wrappers to instance matching.
set_option allowUnsafeReducibility true in
attribute [local reducible] ringSheaf GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive
  GeneralAlgebraicallyClosedCoefficients.stageShift
  GeneralAlgebraicallyClosedCoefficients.stageShiftAdditive
  GeneralAlgebraicallyClosedCoefficients.stageZero
  GeneralAlgebraicallyClosedCoefficients.stagePretriangulated

private def nativeIntegralIso
    {A B D N : Type*} [Category A] [Category B] [Category D] [Category N]
    (Q : A ⥤ B) (J : B ⥤ D) (e : N ≌ D) {F : A ⥤ D} (f : Q ⋙ J ≅ F) :
    Q ⋙ (J ⋙ e.inverse) ⋙ e.functor ≅ F :=
  Functor.isoWhiskerLeft Q (Functor.associator J e.inverse e.functor) ≪≫
    (Functor.associator Q J (e.inverse ⋙ e.functor)).symm ≪≫
    Functor.isoWhiskerLeft (Q ⋙ J) e.counitIso ≪≫ Functor.rightUnitor _ ≪≫ f

private theorem nativeIntegralIso_hom
    {A B D N : Type*} [Category A] [Category B] [Category D] [Category N]
    (Q : A ⥤ B) (J : B ⥤ D) (e : N ≌ D) {F : A ⥤ D} (f : Q ⋙ J ≅ F) (K : A) :
    (nativeIntegralIso Q J e f).hom.app K =
      e.counitIso.hom.app (J.obj (Q.obj K)) ≫ f.hom.app K := by
  simp only [nativeIntegralIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj, Category.assoc,
    Category.id_comp, Category.comp_id]

private theorem nativeIntegralIso_inv
    {A B D N : Type*} [Category A] [Category B] [Category D] [Category N]
    (Q : A ⥤ B) (J : B ⥤ D) (e : N ≌ D) {F : A ⥤ D} (f : Q ⋙ J ≅ F) (K : A) :
    (nativeIntegralIso Q J e f).inv.app K =
      f.inv.app K ≫ e.counitIso.inv.app (J.obj (Q.obj K)) := by
  simp only [nativeIntegralIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_inv,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.comp_obj, Category.id_comp, Category.comp_id]

private def nativeTransitionIso
    {A B D N : Type*} [Category A] [Category B] [Category D] [Category N]
    (T : A ⥤ B) {F : A ⥤ D} {G : B ⥤ D} (e : N ≌ D) (b : F ≅ T ⋙ G) :
    T ⋙ (G ⋙ e.inverse) ≅ F ⋙ e.inverse :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight b.symm e.inverse

private theorem nativeTransitionIso_hom
    {A B D N : Type*} [Category A] [Category B] [Category D] [Category N]
    (T : A ⥤ B) {F : A ⥤ D} {G : B ⥤ D} (e : N ≌ D) (b : F ≅ T ⋙ G) (K : A) :
    (nativeTransitionIso T e b).hom.app K = e.inverse.map (b.inv.app K) := by
  simp only [nativeTransitionIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp]

private theorem nativeTransitionIso_inv
    {A B D N : Type*} [Category A] [Category B] [Category D] [Category N]
    (T : A ⥤ B) {F : A ⥤ D} {G : B ⥤ D} (e : N ≌ D) (b : F ≅ T ⋙ G) (K : A) :
    (nativeTransitionIso T e b).inv.app K = e.inverse.map (b.hom.app K) := by
  simp only [nativeTransitionIso, Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
    Functor.associator_hom_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.comp_id]

private theorem sixfold_reassoc
    {D : Type*} [Category D] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ : D}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃)
    (d : P₃ ⟶ P₄) (e : P₄ ⟶ P₅) (f : P₅ ⟶ P₆) :
    a ≫ b ≫ (c ≫ d) ≫ e ≫ f = (a ≫ b) ≫ c ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]

-- Keep the named equivalence available when elaborating its shift data.
set_option cleanup.letToHave false in
/-- The finite-field tensor realizations form a normalized coherent cocone.

Source: Bhatt--Scholze, Proposition 6.8.11(3), Proposition 6.8.14(2) and Remark 6.8.15;
native realization proof steps 3--4
(blueprint: lem-sf-locally-finite-adic-finite-cocone).

Proof in words: on the integral full subcategory use derived extension along the
specified integral coefficient map. Its explicit comparison for E ≤ L is inverse
balanced tensor transitivity followed by the completed scalar comparison. Finite-free
completion makes this an isomorphism. It respects the normalized integral shifts and
integral scalar associators. The integral tensor functor inverts the uniformizer,
hence kills uniformizer-torsion cones and factors through the raw rational localization.
The localization universal property lifts the integral comparisons uniquely. Their
component formula, naturality, and the localized integral associator prove the rational
field-tower equation. The localization counit fixes the shifts, so exactness descends
from integral-image triangles. Compose with the inverse of the derived native-section
equivalence to obtain the native functors and comparisons. Its counit supplies the
integral isomorphisms. Counit naturality and the literal-object transport formula for
the scalar transitions turn the lifted integral-component formula into exactly the
required HEq normalization. This constructs only the finite cocone; no common-stage
quotient or descent functor is used.
-/
theorem finiteCocone_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (C : CoefficientSystem l X) :
    letI := C.commutative
    letI := C.sectionsAdditive
    letI := C.sectionsLimits
    letI := C.sectionsColimits
    Nonempty (FiniteCocone l X C) := by
  letI := C.commutative
  letI := C.sectionsAdditive
  letI := C.sectionsLimits
  letI := C.sectionsColimits
  letI := ProEtale.nativeScalarForgetting_isEquivalence l X
  haveI : (sections l X).IsEquivalence := by
    unfold sections
    infer_instance
  let e : DerivedCategory.{u + 1} (ProEtale.AdicSheaf l X) ≌
      DerivedCategory.{u + 2} (pbcModules X (ringSheaf l X)) :=
    (Functor.mapDerivedCategory.{u + 1, u + 2} (sections l X)).asEquivalence
  let a : (Functor.mapDerivedCategory.{u + 1, u + 2} (sections l X)) ≅ e.functor :=
    eqToIso (by rfl)
  letI : e.functor.CommShift ℤ := Functor.CommShift.ofIso a ℤ
  haveI : NatTrans.CommShift a.hom ℤ := Functor.CommShift.ofIso_compatibility a ℤ
  haveI : e.functor.IsTriangulated := Functor.isTriangulated_of_iso a
  haveI : e.functor.Additive := Functor.additive_of_iso a
  haveI : e.inverse.Additive := Equivalence.inverse_additive e
  letI : e.inverse.CommShift ℤ := e.commShiftInverse ℤ
  letI : e.CommShift ℤ := e.commShift_of_functor ℤ
  haveI : e.inverse.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right e.counitIso).2 inferInstance
  haveI tensorAdditive (E : Index l (PadicAlgCl l)) :
      (rationalTensor l X C E).Additive := rationalTensor_additive l X C E
  letI tensorShift (E : Index l (PadicAlgCl l)) :
      (rationalTensor l X C E).CommShift ℤ := rationalTensor_shift l X C E
  haveI tensorTriangulated (E : Index l (PadicAlgCl l)) :
      (rationalTensor l X C E).IsTriangulated := rationalTensor_triangulated l X C E
  letI stageTransitionShift {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).CommShift
        ℤ := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift
      l (PadicAlgCl l) X E L h
  haveI tensorTransitionShift {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
      NatTrans.CommShift (rationalTensorTransition l X C h).hom ℤ :=
    rationalTensorTransition_shift l X C h
  let A : FiniteCoconeData l X C := {
    Φ := fun E ↦ rationalTensor l X C E ⋙ e.inverse
    additive := fun E ↦ by
      haveI := rationalTensor_additive l X C E
      constructor
      intro P Q f g
      simp only [Functor.comp_map, Functor.map_add]
    shift := fun E ↦ by
      haveI := rationalTensor_shift l X C E
      exact Functor.CommShift.comp (F := rationalTensor l X C E) (G := e.inverse) (A := ℤ)
    triangulated := fun E ↦ by infer_instance
    ι := fun h ↦ nativeTransitionIso _ e (rationalTensorTransition l X C h)
    transitionShift := fun h ↦ by
      dsimp only [nativeTransitionIso, Iso.trans_hom, Iso.symm_hom,
        Functor.isoWhiskerRight_hom]
      infer_instance
    coherence := by
      intro E L M h k K
      with_unfolding_all simp only [nativeTransitionIso_hom, Functor.comp_map]
      rw [← e.inverse.map_comp, ← e.inverse.map_comp,
        rationalTensorTransition_inv_tower l X C h k K]
    integral := fun E ↦ nativeIntegralIso (stageLocalization l X E)
      (rationalTensor l X C E) e (rationalTensorIntegral l X C E) }
  refine ⟨{ toFiniteCoconeData := A, normalization := ?_ }⟩
  unfold FiniteCoconeData.normalized
  intro E L h K
  -- Reduce the cocone projections directly before simplifying their components.
  with_unfolding_all simp only [A, nativeTransitionIso_inv,
    nativeIntegralIso_hom, nativeIntegralIso_inv]
  with_unfolding_all
    change HEq
      (e.functor.map (e.inverse.map
      ((rationalTensorTransition l X C h).hom.app ((stageLocalization l X E).obj K)))) _
  have hn := rationalTensorTransition_native_normalization l X C e h K
  have hb := congrArg Iso.inv (integralTensorBalancing_app l X C h K.obj)
  change (integralTensorBalancing l X C h).inv.app K.obj = _ at hb
  with_unfolding_all simp only [integralTensorComparison_app l X C h K, hb] at hn
  with_unfolding_all refine HEq.trans hn (heq_of_eq ?_)
  with_unfolding_all exact sixfold_reassoc _ _ _ _ _ _

end WeilConjectures.LocallyFiniteAdicRealization
