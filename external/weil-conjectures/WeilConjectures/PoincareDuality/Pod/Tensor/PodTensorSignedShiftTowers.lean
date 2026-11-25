/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorFiniteSignedShifts
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorFiniteSignedShiftLaws
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorFiniteShiftTransitions

/-! # Assemble finite signed shifts into strict tensor tower maps

The quotient squares determine naturality. The tower components are the
explicit finite comparisons, and the derived fields remain parameters.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] podTensorFiniteShiftLeft podTensorFiniteShiftRight

/-- A tower isomorphism can be assembled from its components and adjacent squares.
Source: Mathlib's NatTrans.ofOpSequence and NatIso.ofComponents
(blueprint: def-pod-tensor-signed-shift-towers). -/
def podTowerIsoOfAdjacent {C : Type a} [Category.{b} C] {F G : ℕᵒᵖ ⥤ C}
    (e : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n))
    (he : ∀ n : ℕ, F.map (homOfLE (n.le_add_right 1)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ G.map (homOfLE (n.le_add_right 1)).op) : F ≅ G :=
  NatIso.ofComponents (fun n ↦ e n.unop)
    (fun f ↦ (NatTrans.ofOpSequence (fun n ↦ (e n).hom) he).naturality f)

/-- Assemble the sign-free finite comparisons into a comparison of strict towers.
The naturality proof uses only adjacent quotient squares; all components are the
explicit finite comparisons.
Source: Stacks 011G and 07A4 (blueprint: def-pod-tensor-signed-shift-towers). -/
def podTensorSignedShiftLeftTower (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (r : ℤ) :
    (integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj) ≅
      podShiftTower ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)) r := by
  exact podTowerIsoOfAdjacent
    (fun n ↦ podTensorFiniteShiftLeft l E W n P.obj Q.obj r) (by
      intro n
      simpa only [integralOperationsTensorTowerFunctor, podShiftTower,
        Functor.comp_map, Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
        using (podTensorFiniteShiftTransitions l E W).1 n P.obj Q.obj r)

/-- Assemble the signed finite comparisons into a comparison of strict towers.
Source: Stacks 011G and 07A4 (blueprint: def-pod-tensor-signed-shift-towers). -/
def podTensorSignedShiftRightTower (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (r : ℤ) :
    (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj⟦r⟧) ≅
      podShiftTower ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)) r := by
  exact podTowerIsoOfAdjacent
    (fun n ↦ podTensorFiniteShiftRight l E W n P.obj Q.obj r) (by
      intro n
      simpa only [integralOperationsTensorTowerFunctor, podShiftTower,
        Functor.comp_map, Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
        using (podTensorFiniteShiftTransitions l E W).2 n P.obj Q.obj r)

/-- The type of the derived first-factor shift fields, kept separate from strict data.
Source: Stacks 07A4 (blueprint: def-pod-tensor-signed-shift-towers). -/
abbrev PodTensorDerivedShiftLeft (W : Scheme.{u}) :=
  ∀ (M N M' : sfIntegralConstructibleCategory l E W) (r : ℤ) (_e : M'.obj ≅ M.obj⟦r⟧),
    (integralCompletedTensor l E W).obj (M'.obj, N.obj) ≅
      ((integralCompletedTensor l E W).obj (M.obj, N.obj))⟦r⟧

/-- The type of the derived second-factor shift fields.
Source: Stacks 07A4 (blueprint: def-pod-tensor-signed-shift-towers). -/
abbrev PodTensorDerivedShiftRight (W : Scheme.{u}) :=
  ∀ (M N N' : sfIntegralConstructibleCategory l E W) (r : ℤ) (_e : N'.obj ≅ N.obj⟦r⟧),
    (integralCompletedTensor l E W).obj (M.obj, N'.obj) ≅
      ((integralCompletedTensor l E W).obj (M.obj, N.obj))⟦r⟧

/-- Combine the constructed strict data with supplied derived shift fields.
Every non-proof field is explicit or is a parameter.
Source: Stacks 011G and 07A4 (blueprint: def-pod-tensor-signed-shift-towers). -/
def podTensorSignedShiftOfDerived (W : Scheme.{u})
    (L : PodTensorDerivedShiftLeft l E W) (R : PodTensorDerivedShiftRight l E W) :
    PodTensorSignedShift l E W where
  good := podTensorGoodShift l E W
  leftTower := podTensorSignedShiftLeftTower l E W
  rightTower := podTensorSignedShiftRightTower l E W
  left := L
  right := R

/-- The strict generator formulas are unaffected by the derived fields supplied later.
Source: Stacks 011G and 07A4 (blueprint: def-pod-tensor-signed-shift-towers). -/
theorem podTensorSignedShiftOfDerived_generators (W : Scheme.{u})
    (L : PodTensorDerivedShiftLeft l E W) (R : PodTensorDerivedShiftRight l E W) :
    (podTensorSignedShiftOfDerived l E W L R).Generators l E := by
  constructor
  · intro P Q n p q r U x y
    exact (podTensorFiniteSignedShiftGenerators l E W).1 P.obj Q.obj n p q r U x y
  · intro P Q n p q r U x y
    exact (podTensorFiniteSignedShiftGenerators l E W).2 P.obj Q.obj n p q r U x y

end WeilConjectures
