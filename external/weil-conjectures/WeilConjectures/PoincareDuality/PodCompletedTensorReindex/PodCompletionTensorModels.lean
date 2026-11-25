/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels

/-! # Normalized completed tensor reindexing models

Source: blueprint theorem-poincare-duality-frobenius--2 Steps 1 and 5;
Stacks 07A4, 0941 (blueprint: def-pod-completion-tensor-reindex-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- Relabel the actual good representatives using preservation of flat terms and K-flatness.
Source: Stacks 07A4 (blueprint: def-pod-completion-tensor-reindex-models). -/
def podGoodReindex (D : PodCompletionReindex l E g) :
    (integralOperationsGoodComplex l E Y).FullSubcategory ⥤
      (integralOperationsGoodComplex l E X).FullSubcategory :=
  (integralOperationsGoodComplex l E X).lift
    ((integralOperationsGoodComplex l E Y).ι ⋙ isoReductionIntegralComplex l E g)
    (fun P ↦ D.good P.obj P.property)

attribute [local irreducible] integralCompletedTensor
  sfIntegralConstructible podReindexCalculus podOrdinaryToCompleted
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The completed tensor comparison on constructible complete inputs, retaining its
strict tensor-summand map, inverse, complete Roos realization, and canonical-arrow equality.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: def-pod-completion-tensor-reindex-models). -/
structure PodCompletedTensorReindex {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) where
  /-- Exact relabelling preserves complete constructibility and its common interval. -/
  constructible : ∀ M : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E X ((podOrdinaryReindex l E g).obj M.obj)
  /-- Relabel every summand of the strict finite tensor-reduction tower. -/
  tower : ∀ P Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
    (podReindexTower l E g).obj
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
      (integralOperationsTensorTowerFunctor l E X).obj
        (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj)
  /-- The comparison on the complete constructible objects of the node. -/
  tensor : ∀ M N : sfIntegralConstructibleCategory l E Y,
    (podOrdinaryReindex l E g).obj ((integralCompletedTensor l E Y).obj (M.obj,N.obj)) ≅
      (integralCompletedTensor l E X).obj
        ((podOrdinaryReindex l E g).obj M.obj,(podOrdinaryReindex l E g).obj N.obj)

namespace PodCompletedTensorReindex

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)

/-- The forward map on every total tensor generator in every degree and quotient.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-tensor-reindex-models). -/
def Generators : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (n : ℕ) (p q : ℤ) (U : X.ProEt)
    (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))),
    ((((T.tower P Q).hom.app (op n)).f (p + q)).val.app (op U))
        (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      integralOperationsTotalTensorSection l E X n
        (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
        p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
          ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)

/-- The inverse is precisely reverse relabelling on the same tensor generators.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-tensor-reindex-models). -/
def InverseGenerators : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (n : ℕ) (p q : ℤ) (U : X.ProEt)
    (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))),
    ((((T.tower P Q).inv.app (op n)).f (p + q)).val.app (op U))
        (integralOperationsTotalTensorSection l E X n
          (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
          p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
            ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)) =
      integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
        (op ((proEtaleIsoPostcompose g).obj U)) x y

/-- Coherent naturality on entire strict towers, including all their transitions.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-tensor-reindex-models). -/
def TowerNaturality : Prop :=
  ∀ (P Q P' Q' : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (a : P ⟶ P') (b : Q ⟶ Q'),
    (podReindexTower l E g).map
        ((integralOperationsTensorTowerFunctor l E Y).map (Prod.mkHom a.hom b.hom)) ≫
        (T.tower P' Q').hom =
      (T.tower P Q).hom ≫ (integralOperationsTensorTowerFunctor l E X).map
        (Prod.mkHom ((podGoodReindex l E g D).map a).hom
          ((podGoodReindex l E g D).map b).hom)

/-- Naturality for all derived morphisms of both inputs.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-tensor-reindex-models). -/
def Naturality : Prop :=
  ∀ (M N M' N' : sfIntegralConstructibleCategory l E Y)
    (a : M ⟶ M') (b : N ⟶ N'),
    (podOrdinaryReindex l E g).map
        ((integralCompletedTensor l E Y).map (Prod.mkHom a.hom b.hom)) ≫
        (T.tensor M' N').hom =
      (T.tensor M N).hom ≫ (integralCompletedTensor l E X).map
        (Prod.mkHom ((podOrdinaryReindex l E g).map a.hom)
          ((podOrdinaryReindex l E g).map b.hom))

end PodCompletedTensorReindex

end WeilConjectures
