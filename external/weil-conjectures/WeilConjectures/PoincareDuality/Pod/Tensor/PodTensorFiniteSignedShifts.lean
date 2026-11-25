/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Concrete signed shifts of finite total tensors

The finite comparison maps are explicit composites of ordinary reduction shifts,
Mathlib total-tensor shifts, and ordinary restriction shifts. Good representative
shift preservation is proved directly from the K-flatness definition.
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Good representatives remain good under every integer shift.
Source: Stacks 06YN and 011G (blueprint: def-pod-tensor-finite-signed-shifts).
The tensor with a shifted complex is the shift of its tensor; acyclicity is
stable under shifts. The terms are just reindexed flat terms. -/
theorem podTensorGoodShift (W : Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) (r : ℤ) :
    integralOperationsGoodComplex l E W (P.obj⟦r⟧) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let R := completedIntegralCommRingSheafUnrestricted l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  refine ⟨?_, fun i ↦ P.property.2 (i + r)⟩
  intro F hF
  have ht := P.property.1 F hF
  have hs :
      (CochainComplex.mapBifunctor F P.obj (MonoidalCategory.curriedTensor _)⟦r⟧).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
    rw [← HomotopyCategory.shift_quotient_obj]
    exact (HomotopyCategory.subcategoryAcyclic _).le_shift r _ ht
  intro i
  exact (hs i).of_iso
    (CochainComplex.mapBifunctorShift₂Iso F P.obj (MonoidalCategory.curriedTensor _) r).symm

attribute [local instance] integralOperationsFiniteHasMap

/-- The sign-free first-factor finite tensor shift, before taking the strict tower.
Source: Stacks 011G, 07A4 (blueprint: def-pod-tensor-finite-signed-shifts). -/
def podTensorFiniteShiftLeft (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ) :
    (integralOperationsTensorLevel l E W n).obj (P⟦r⟧, Q) ≅
      ((integralOperationsTensorLevel l E W n).obj (P, Q))⟦r⟧ := by
  letI : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  letI := integralCoefficientAbSheafify.{u, u} W
  letI := integralCoefficientAbLocallyBijective.{u, u} W
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (integralCoefficientCommRingSheaf l E W n)
  letI : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
    integralOperationsFiniteMonoidal l E W n
  letI : MonoidalPreadditive (integralOperationsFiniteModules l E W n) :=
    SheafOfModules.cochainModulesPreadditive.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf l E W n)
  let F := unrestrictedIntegralFiniteComplex l E W n
  let R := integralOperationsRestrict l E W n
  have : R.CommShift ℤ := by
    dsimp [R, integralOperationsRestrict]
    infer_instance
  let B := Functor.uncurry.obj
    (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)).map₂CochainComplex
  exact R.mapIso (B.mapIso (Iso.prod ((F.commShiftIso r).app P) (Iso.refl _)) ≪≫
    CochainComplex.mapBifunctorShift₁Iso (F.obj P) (F.obj Q)
      (MonoidalCategory.curriedTensor _) r) ≪≫ (R.commShiftIso r).app (B.obj (F.obj P, F.obj Q))

/-- The second-factor finite tensor shift, with the native Koszul sign.
Source: Stacks 011G, 07A4 (blueprint: def-pod-tensor-finite-signed-shifts). -/
def podTensorFiniteShiftRight (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ) :
    (integralOperationsTensorLevel l E W n).obj (P, Q⟦r⟧) ≅
      ((integralOperationsTensorLevel l E W n).obj (P, Q))⟦r⟧ := by
  letI : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  letI := integralCoefficientAbSheafify.{u, u} W
  letI := integralCoefficientAbLocallyBijective.{u, u} W
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (integralCoefficientCommRingSheaf l E W n)
  letI : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
    integralOperationsFiniteMonoidal l E W n
  letI : MonoidalPreadditive (integralOperationsFiniteModules l E W n) :=
    SheafOfModules.cochainModulesPreadditive.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf l E W n)
  let F := unrestrictedIntegralFiniteComplex l E W n
  let R := integralOperationsRestrict l E W n
  have : R.CommShift ℤ := by
    dsimp [R, integralOperationsRestrict]
    infer_instance
  let B := Functor.uncurry.obj
    (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)).map₂CochainComplex
  exact R.mapIso (B.mapIso (Iso.prod (Iso.refl _) ((F.commShiftIso r).app Q)) ≪≫
    CochainComplex.mapBifunctorShift₂Iso (F.obj P) (F.obj Q)
      (MonoidalCategory.curriedTensor _) r) ≪≫ (R.commShiftIso r).app (B.obj (F.obj P, F.obj Q))

/-- Quotient-transition compatibility of the two explicitly constructed finite maps.
Source: Stacks 011G and 07A4 (blueprint: def-pod-tensor-finite-signed-shifts). -/
def PodTensorFiniteShiftTransitions (W : Scheme.{u}) : Prop :=
  (∀ (n : ℕ) (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ),
    (integralOperationsTensorTransition l E W n).app (P⟦r⟧, Q) ≫
      (podTensorFiniteShiftLeft l E W n P Q r).hom =
    (podTensorFiniteShiftLeft l E W (n + 1) P Q r).hom ≫
      ((integralOperationsTensorTransition l E W n).app (P, Q))⟦r⟧') ∧
  (∀ (n : ℕ) (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ),
    (integralOperationsTensorTransition l E W n).app (P, Q⟦r⟧) ≫
      (podTensorFiniteShiftRight l E W n P Q r).hom =
    (podTensorFiniteShiftRight l E W (n + 1) P Q r).hom ≫
      ((integralOperationsTensorTransition l E W n).app (P, Q))⟦r⟧')

/-- Homogeneous sections of the explicit finite maps, including the second-factor sign.
Source: Stacks 011G and 07A4 (blueprint: def-pod-tensor-finite-signed-shifts). -/
def PodTensorFiniteShiftGenerators (W : Scheme.{u}) : Prop :=
  (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (n : ℕ) (p q r : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X (p + r)).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U),
    HEq (((podTensorFiniteShiftLeft l E W n P Q r).hom.f (p + q)).val.app U
      (integralOperationsTotalTensorSection l E W n (P⟦r⟧) Q p q U x y))
      (integralOperationsTotalTensorSection l E W n P Q (p + r) q U x y)) ∧
  (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (n : ℕ) (p q r : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X (q + r)).val.obj U),
    HEq (((podTensorFiniteShiftRight l E W n P Q r).hom.f (p + q)).val.app U
      (integralOperationsTotalTensorSection l E W n P (Q⟦r⟧) p q U x y))
      ((p * r).negOnePow • integralOperationsTotalTensorSection l E W n P Q p (q + r) U x y))

end WeilConjectures
