/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorSignedShiftTowers
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRoosShiftNaturality
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRightShiftNaturality
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingSignedRoosShift
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus

/-! # Signed tensor shifts on good representatives

Compose the fixed strict tower comparisons, the supplied signed Roos comparison,
and localization, retaining their precise components.
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

/-- Select the left or right input of a product functor.
Source: construction (blueprint: lem-pod-tensor-representative-shift-isos). -/
abbrev podTensorRepresentativePairOf {C : Type*} [Category C] (S : C ⥤ C) (right : Bool) :
    C × C ⥤ C × C :=
  if right then (𝟭 C).prod S else S.prod (𝟭 C)

/-- Compose three functorial shift comparisons.
Source: construction (blueprint: lem-pod-tensor-representative-shift-isos). -/
def podTensorRepresentativeComposeShiftIso {C D B A : Type*}
    [Category C] [Category D] [Category B] [Category A]
    (F : C ⥤ D) (R : D ⥤ B) (Q : B ⥤ A)
    (s : C ⥤ C) (S : D ⥤ D) (H : B ⥤ B) (J : A ⥤ A)
    (e : s ⋙ F ≅ F ⋙ S) (f : S ⋙ R ≅ R ⋙ H) (g : H ⋙ Q ≅ Q ⋙ J) :
    s ⋙ (F ⋙ R ⋙ Q) ≅ (F ⋙ R ⋙ Q) ⋙ J :=
  isoWhiskerRight (isoWhiskerRight e R) Q ≪≫
    isoWhiskerRight (isoWhiskerLeft F f) Q ≪≫
      isoWhiskerLeft (F ⋙ R) g

/-- The existing shift functor on good representatives.
Source: construction (blueprint: lem-pod-tensor-representative-shift-isos). -/
abbrev podTensorRepresentativeGoodShift (W : Scheme.{u}) (r : ℤ) :
    (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      (integralOperationsGoodComplex l E W).FullSubcategory :=
  podTensorGoodShiftFunctor l E W r

/-- Restrict the existing strict tensor tower to good pairs.
Source: construction (blueprint: lem-pod-tensor-representative-shift-isos). -/
abbrev podTensorRepresentativeTensorTowerOnGood (W : Scheme.{u}) := podTensorTowerOnGood l E W

/-- The existing levelwise shift on towers.
Source: construction (blueprint: lem-pod-tensor-representative-shift-isos). -/
abbrev podTensorRepresentativeTowerShift {A : Type*} [Category A] [Preadditive A] (r : ℤ) :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  podTensorTowerShift r

/-- Select the already fixed left or right strict tensor shift.
Source: construction (blueprint: lem-pod-tensor-representative-shift-isos). -/
def podTensorRepresentativeStrictTensorShift (W : Scheme.{u}) (r : ℤ) (right : Bool) :
    podTensorRepresentativePairOf (podTensorRepresentativeGoodShift l E W r) right ⋙
      podTensorRepresentativeTensorTowerOnGood l E W ≅
      podTensorRepresentativeTensorTowerOnGood l E W ⋙ podTensorRepresentativeTowerShift r := by
  cases right
  · exact podTensorStrictShiftLeftIso l E W r
  · exact podTensorStrictShiftRightIso l E W r

attribute [local irreducible] podTensorStrictShiftLeftIso podTensorStrictShiftRightIso

attribute [local irreducible] integralOperationsTensorTowerFunctor integralOperationsRoos

/-- Compose shift comparisons after restriction, retaining explicit associators.
Source: construction (blueprint: lem-pod-tensor-representative-shift-isos). -/
def podTensorRepresentativeComposeRestrictionShiftIso {C C₀ D B A : Type*}
    [Category C] [Category C₀] [Category D] [Category B] [Category A]
    (I : C ⥤ C₀) (F : C₀ ⥤ D) (R : D ⥤ B) (Q : B ⥤ A)
    (s : C ⥤ C) (S : D ⥤ D) (H : B ⥤ B) (J : A ⥤ A)
    (e : s ⋙ (I ⋙ F) ≅ (I ⋙ F) ⋙ S)
    (f : S ⋙ R ≅ R ⋙ H) (g : H ⋙ Q ≅ Q ⋙ J) :
    s ⋙ (I ⋙ (F ⋙ R) ⋙ Q) ≅ (I ⋙ (F ⋙ R) ⋙ Q) ⋙ J :=
  let a : I ⋙ (F ⋙ R) ⋙ Q ≅ (I ⋙ F) ⋙ R ⋙ Q :=
    isoWhiskerLeft I (Functor.associator F R Q) ≪≫
      (Functor.associator I F (R ⋙ Q)).symm
  isoWhiskerLeft s a ≪≫ podTensorRepresentativeComposeShiftIso (I ⋙ F) R Q s S H J e f g ≪≫
    isoWhiskerRight a.symm J

private theorem composeRestrictionShiftIso_hom_app {C C₀ D B A : Type*}
    [Category C] [Category C₀] [Category D] [Category B] [Category A]
    (I : C ⥤ C₀) (F : C₀ ⥤ D) (R : D ⥤ B) (Q : B ⥤ A)
    (s : C ⥤ C) (S : D ⥤ D) (H : B ⥤ B) (J : A ⥤ A)
    (e : s ⋙ (I ⋙ F) ≅ (I ⋙ F) ⋙ S)
    (f : S ⋙ R ≅ R ⋙ H) (g : H ⋙ Q ≅ Q ⋙ J) (X : C) :
    (podTensorRepresentativeComposeRestrictionShiftIso I F R Q s S H J e f g).hom.app X =
      Q.map (R.map (e.hom.app X)) ≫ Q.map (f.hom.app ((I ⋙ F).obj X)) ≫
        g.hom.app ((I ⋙ F ⋙ R).obj X) := by
  simp [podTensorRepresentativeComposeRestrictionShiftIso, podTensorRepresentativeComposeShiftIso]

/-- The constructed signed tensor shift on good representatives.
Source: construction (blueprint: lem-pod-tensor-representative-shift-isos). -/
def podTensorRepresentativeOnGoodShiftIso (W : Scheme.{u})
    (ρ : PodSignedRoosShift (scalarReductionSource l E W)) (hρ : ρ.Laws)
    (r : ℤ) (right : Bool) :
    podTensorRepresentativePairOf (podTensorRepresentativeGoodShift l E W r) right ⋙
      integralOperationsTensorOnGood l E W ≅
      integralOperationsTensorOnGood l E W ⋙ shiftFunctor _ r :=
  podTensorRepresentativeComposeRestrictionShiftIso
    ((integralOperationsGoodComplex l E W).ι.prod (integralOperationsGoodComplex l E W).ι)
    (integralOperationsTensorTowerFunctor l E W) integralOperationsRoosFunctor
    DerivedCategory.Q (podTensorRepresentativePairOf (podTensorRepresentativeGoodShift l E W r)
      right) (podTensorRepresentativeTowerShift r)
    (shiftFunctor _ r) (shiftFunctor _ r) (podTensorRepresentativeStrictTensorShift l E W r right)
    (podTensorRoosShiftIso ρ hρ r) (DerivedCategory.Q.commShiftIso r)

private theorem onGoodShiftIso_hom_app (W : Scheme.{u})
    (ρ : PodSignedRoosShift (scalarReductionSource l E W)) (hρ : ρ.Laws)
    (r : ℤ) (right : Bool)
    (X : (integralOperationsGoodComplex l E W).FullSubcategory ×
      (integralOperationsGoodComplex l E W).FullSubcategory) :
    (podTensorRepresentativeOnGoodShiftIso l E W ρ hρ r right).hom.app X =
      DerivedCategory.Q.map
          (integralOperationsRoosFunctor.map ((podTensorRepresentativeStrictTensorShift l E W r
      right).hom.app X)) ≫
        DerivedCategory.Q.map (ρ.comparison ((podTensorRepresentativeTensorTowerOnGood l E
      W).obj X) r).hom ≫
          (DerivedCategory.Q.commShiftIso r).hom.app
            (integralOperationsRoosFunctor.obj ((podTensorRepresentativeTensorTowerOnGood l E
      W).obj X)) :=
  composeRestrictionShiftIso_hom_app
    ((integralOperationsGoodComplex l E W).ι.prod (integralOperationsGoodComplex l E W).ι)
    (integralOperationsTensorTowerFunctor l E W) integralOperationsRoosFunctor
    DerivedCategory.Q (podTensorRepresentativePairOf (podTensorRepresentativeGoodShift l E W r)
      right) (podTensorRepresentativeTowerShift r)
    (shiftFunctor _ r) (shiftFunctor _ r) (podTensorRepresentativeStrictTensorShift l E W r right)
    (podTensorRoosShiftIso ρ hρ r) (DerivedCategory.Q.commShiftIso r) X

attribute [local irreducible] podTensorRepresentativeOnGoodShiftIso

/-- The two representative tensor shifts, with their prescribed signed Roos components.

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G and 07A4
(blueprint: lem-pod-tensor-representative-shift-isos).

Proof: the two coordinate laws identify the supplied Roos comparison with the
native mapping-cocone shift: compose each degree with the two coordinates of
the mapping cocone and use its identity decomposition. The native comparison
is natural by the Roos commShift isomorphism. Compose it with the natural strict
left or right tensor-tower shift and with the localization commShift isomorphism.
Functor associators identify the result with the representative tensor functor.
Evaluating the composite gives exactly the three displayed maps. -/
theorem podTensorRepresentativeShift_isos (W : Scheme.{u})
    (ρ : PodSignedRoosShift (scalarReductionSource l E W)) (hρ : ρ.Laws) (r : ℤ) :
    ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
      ((podTensorRepresentativeOnGoodShiftIso l E W ρ hρ r false).hom.app (P, Q) =
        DerivedCategory.Q.map
          (integralOperationsRoosFunctor.map
            (podTensorSignedShiftLeftTower l E W P Q r).hom) ≫
        DerivedCategory.Q.map (ρ.comparison ((podTensorTowerOnGood l E W).obj (P, Q)) r).hom ≫
          (DerivedCategory.Q.commShiftIso r).hom.app
            (integralOperationsRoosFunctor.obj ((podTensorTowerOnGood l E W).obj (P, Q)))) ∧
      ((podTensorRepresentativeOnGoodShiftIso l E W ρ hρ r true).hom.app (P, Q) =
        DerivedCategory.Q.map
          (integralOperationsRoosFunctor.map
            (podTensorSignedShiftRightTower l E W P Q r).hom) ≫
        DerivedCategory.Q.map (ρ.comparison ((podTensorTowerOnGood l E W).obj (P, Q)) r).hom ≫
          (DerivedCategory.Q.commShiftIso r).hom.app
            (integralOperationsRoosFunctor.obj ((podTensorTowerOnGood l E W).obj (P, Q)))) := by
  intro P Q
  constructor
  · have h := onGoodShiftIso_hom_app l E W ρ hρ r false (P, Q)
    have he := congrArg
      (fun f ↦ (DerivedCategory.Q (C := integralTowerModules l E W)).map
        ((integralOperationsRoosFunctor (A := integralTowerModules l E W)).map f))
      (podTensorStrictShiftLeftIso_hom_app l E W r P Q)
    exact h.trans (congrArg (fun f ↦ f ≫ _ ≫ _) he)
  · have h := onGoodShiftIso_hom_app l E W ρ hρ r true (P, Q)
    have he := congrArg
      (fun f ↦ (DerivedCategory.Q (C := integralTowerModules l E W)).map
        ((integralOperationsRoosFunctor (A := integralTowerModules l E W)).map f))
      (podTensorStrictShiftRightIso_hom_app l E W r P Q)
    exact h.trans (congrArg (fun f ↦ f ≫ _ ≫ _) he)

end WeilConjectures
