/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorSignedShiftTowers
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorFiniteShiftNaturality

/-! # Naturality of the strict left tensor shift
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
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

private theorem leftTower_component (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (r : ℤ) (n : ℕᵒᵖ) :
    (podTensorSignedShiftLeftTower l E W P Q r).hom.app n =
      (podTensorFiniteShiftLeft l E W n.unop P.obj Q.obj r).hom := by rfl

attribute [local irreducible] podTensorSignedShiftLeftTower
  podTensorFiniteShiftLeft integralOperationsTensorLevel

/-- The fixed strict left tensor shift is natural on pairs of good complexes.
Source: Stacks 011G and 07A4; finite signed tensor-shift naturality.
(blueprint: lem-pod-tensor-left-shift-naturality).

Proof: evaluate the naturality square at every tower level. Its components are
the fixed finite comparisons, and the tower functor acts levelwise. Each square
is therefore the corresponding finite-shift naturality equation. -/
theorem podTensorSignedShiftLeftTower_naturality (W : Scheme.{u})
    {P Q : (integralOperationsGoodComplex l E W).FullSubcategory ×
      (integralOperationsGoodComplex l E W).FullSubcategory} (f : P ⟶ Q) (r : ℤ) :
    (integralOperationsTensorTowerFunctor l E W).map (Prod.mkHom (f.1.hom⟦r⟧') f.2.hom) ≫
        (podTensorSignedShiftLeftTower l E W Q.1 Q.2 r).hom =
      (podTensorSignedShiftLeftTower l E W P.1 P.2 r).hom ≫
        whiskerRight ((integralOperationsTensorTowerFunctor l E W).map
          (Prod.mkHom f.1.hom f.2.hom)) (shiftFunctor _ r) := by
  apply NatTrans.ext
  funext n
  simp only [NatTrans.comp_app, leftTower_component]
  change (integralOperationsTensorLevel l E W n.unop).map
      (Prod.mkHom (f.1.hom⟦r⟧') f.2.hom) ≫
        (podTensorFiniteShiftLeft l E W n.unop Q.1.obj Q.2.obj r).hom =
    (podTensorFiniteShiftLeft l E W n.unop P.1.obj P.2.obj r).hom ≫
      ((integralOperationsTensorLevel l E W n.unop).map
        (Prod.mkHom f.1.hom f.2.hom))⟦r⟧'
  exact (podTensorFiniteShift_naturality l E W n.unop
    (Prod.mkHom f.1.hom f.2.hom) r).1

/-- Shift a good representative using its existing shift-stability theorem.
Source: Stacks 011G and 07A4
(blueprint: lem-pod-tensor-left-shift-naturality). -/
abbrev podTensorGoodShiftFunctor (W : Scheme.{u}) (r : ℤ) :
    (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      (integralOperationsGoodComplex l E W).FullSubcategory :=
  (integralOperationsGoodComplex l E W).lift
    ((integralOperationsGoodComplex l E W).ι ⋙ shiftFunctor _ r)
      (fun P ↦ podTensorGoodShift l E W P r)

/-- The existing tensor tower restricted to pairs of good representatives.
Source: Stacks 07A4 (blueprint: lem-pod-tensor-left-shift-naturality). -/
abbrev podTensorTowerOnGood (W : Scheme.{u}) :=
  ((integralOperationsGoodComplex l E W).ι.prod
    (integralOperationsGoodComplex l E W).ι) ⋙ integralOperationsTensorTowerFunctor l E W

/-- Shift every complex in a strict tower.
Source: Stacks 011G (blueprint: lem-pod-tensor-left-shift-naturality). -/
abbrev podTensorTowerShift {A : Type*} [Category A] [Preadditive A] (r : ℤ) :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  (whiskeringRight _ _ _).obj (shiftFunctor _ r)

/-- Package the fixed left strict shift as a natural isomorphism.
Source: Stacks 011G and 07A4
(blueprint: lem-pod-tensor-left-shift-naturality). -/
def podTensorStrictShiftLeftIso (W : Scheme.{u}) (r : ℤ) :
    ((podTensorGoodShiftFunctor l E W r).prod (𝟭 _)) ⋙
        podTensorTowerOnGood l E W ≅
      podTensorTowerOnGood l E W ⋙ podTensorTowerShift r :=
  NatIso.ofComponents
    (fun P ↦ podTensorSignedShiftLeftTower l E W P.1 P.2 r)
    (fun f ↦ podTensorSignedShiftLeftTower_naturality l E W f r)

/-- The natural left comparison retains the specified strict tower map.
Source: construction (blueprint: lem-pod-tensor-left-shift-naturality). -/
theorem podTensorStrictShiftLeftIso_hom_app (W : Scheme.{u}) (r : ℤ)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (podTensorStrictShiftLeftIso l E W r).hom.app (P, Q) =
      (podTensorSignedShiftLeftTower l E W P Q r).hom := by rfl

end WeilConjectures
