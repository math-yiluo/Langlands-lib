/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingStrictTensorTowersGenerators
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingStrictTensorTowersNaturality

/-! # Strict steps in normalized completed tensor reindexing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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

/-- Reindexing of the strict total-tensor tower, before any derived limit.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-strict-tensor-towers).

Proof: at level n use the sectionwise tensor comparison for exact inverse image,
then apply D.quotient to both factors. On each summand indexed by p+q=i this sends
x tensor y to D.quotient(x) tensor D.quotient(y). The balanced relation is preserved
by the projection-fixed coefficient map. The signed total differential commutes
with this map because the quotient maps are chain maps and reindexing is additive.
The reverse sectionwise comparison and inverse quotient maps give its inverse.
The quotient-transition squares in hD make these levelwise isomorphisms commute
with every tower transition: both orders have the same value on each tensor
summand. This gives a strict-tower isomorphism, including the zero tower.
For maps a,b of good representatives the same tensor calculation on each summand
proves the displayed naturality equation. This construction uses no completion,
no derived comparison, and no constructibility assertion. -/
theorem podReindexingStrictTensorTowers
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D) :
    ∃ τ : ∀ P Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (podReindexTower l E g).obj
            ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
          (integralOperationsTensorTowerFunctor l E X).obj
            (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj),
      (∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (n : ℕ) (p q : ℤ) (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
        (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        ((((τ P Q).hom.app (op n)).f (p + q)).val.app (op U))
            (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
              (op ((proEtaleIsoPostcompose g).obj U)) x y) =
          integralOperationsTotalTensorSection l E X n
            (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
            p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
              ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)) ∧
      (∀ (P Q P' Q' : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (a : P ⟶ P') (b : Q ⟶ Q'),
        (podReindexTower l E g).map
            ((integralOperationsTensorTowerFunctor l E Y).map (Prod.mkHom a.hom b.hom)) ≫
            (τ P' Q').hom =
          (τ P Q).hom ≫ (integralOperationsTensorTowerFunctor l E X).map
            (Prod.mkHom ((podGoodReindex l E g D).map a).hom
              ((podGoodReindex l E g D).map b).hom)) := by
  obtain ⟨τ, hgen⟩ := podReindexingStrictTensorTowersGenerators l E g D hD
  exact ⟨τ, hgen,
    podReindexingStrictTensorTowersNaturality l E g D hD.2.2.2.2.2.2.1 τ hgen⟩

end WeilConjectures
