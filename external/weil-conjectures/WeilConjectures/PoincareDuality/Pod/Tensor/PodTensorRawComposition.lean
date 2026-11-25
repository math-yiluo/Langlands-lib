/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorTowerComposition

/-! # Composition of normalized strict tensor tower maps

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-composition-tensor-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Preserve sharing of the dependent functor and representative aliases.
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCompletedTensor
  completedIntegralCoefficientSheafUnrestricted Scheme.residueField
  sfIntegralConstructible podReindexCalculus isoReductionCompletedMap
  integralOperationsTensorTowerFunctor
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A functorial composition square, with its final arrow given explicitly.
Source: blueprint Steps 1 and 5; Stacks 015F, 07A4
(blueprint: def-pod-tensor-raw-composition). -/
def PodCompositionEquation
    {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {A B : C} {A' K L : D}
    (a : A' ⟶ G.obj A) (cf : A ⟶ B) (cg : G.obj B ⟶ K)
    (cc : A' ⟶ L) (d : L ⟶ K) : Prop :=
  a ≫ G.map cf ≫ cg = cc ≫ d

/-- The categorical equation underlying a Roos composition square.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: def-pod-tensor-raw-composition).
Naming the equation keeps the same composites shared during kernel checking. -/
def PodRoosCompositionEquation
    {C D T : Type*} [Category C] [Category D] [Category T]
    (G : C ⥤ D) (R : T ⥤ D)
    {A B : C} {A' : D} {t₃ t₄ : T}
    (a : A' ⟶ G.obj A) (cf : A ⟶ B) (cg : G.obj B ⟶ R.obj t₃)
    (cc : A' ⟶ R.obj t₄) (u : t₄ ⟶ t₃) : Prop :=
  PodCompositionEquation G a cf cg cc (R.map u)

/-- The exact equation for the explicit Roos composites of the tensor tower maps.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: def-pod-tensor-raw-composition).
This names the equation before substitution of the named chain maps. -/
def PodTensorRawComposition
    (A : PodReindexFamily l E)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [(isoReductionIntegralInverse l E f).Additive]
    [(isoReductionIntegralInverse l E h).Additive]
    [(isoReductionIntegralInverse l E (h ≫ f)).Additive]
    (P Q : (integralOperationsGoodComplex l E V).FullSubcategory)
    : Prop :=
    let α := NatIso.mapHomologicalComplex (A.composition h f) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h))
        (.up ℤ)).symm
    let FP := (podGoodReindex l E f (A.completion f)).obj P
    let FQ := (podGoodReindex l E f (A.completion f)).obj Q
    let CY := (integralOperationsTensorTowerFunctor l E V).obj (P.obj,Q.obj)
    let CW := (integralOperationsTensorTowerFunctor l E W).obj (FP.obj,FQ.obj)
    PodRoosCompositionEquation (isoReductionIntegralComplex l E h)
      integralOperationsRoosFunctor
      (α.hom.app (integralOperationsRoosFunctor.obj CY))
      (((A.completion f).roos CY).hom ≫
        integralOperationsRoosFunctor.map ((A.tensor f).tower P Q).hom)
      (((A.completion h).roos CW).hom ≫
        integralOperationsRoosFunctor.map ((A.tensor h).tower FP FQ).hom)
      (((A.completion (h ≫ f)).roos CY).hom ≫
        integralOperationsRoosFunctor.map ((A.tensor (h ≫ f)).tower P Q).hom)
      ((integralOperationsTensorTowerFunctor l E Z).map
        (Prod.mkHom (α.hom.app P.obj) (α.hom.app Q.obj)))

end WeilConjectures
