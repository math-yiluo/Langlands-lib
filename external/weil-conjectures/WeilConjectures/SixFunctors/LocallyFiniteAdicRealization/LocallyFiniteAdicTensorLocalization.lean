/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensorUniformizer
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationLift
import Mathlib.CategoryTheory.Shift.Localization

/-! # Localizing the explicit integral native tensor functors

Source: Bhatt--Scholze, Proposition 6.8.14(2); Stacks Tag 05R6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option linter.all false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The integral localization with its codomain explicitly the named stage category.
Source: Stacks Tag 05R6 (blueprint: lem-sf-native-integral-tensor-localization). -/
def stageLocalization (E : Index l (PadicAlgCl l)) :
    sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E :=
  sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X

/-- The named stage localization is the specified raw localization.
Source: Stacks Tag 05R6 (blueprint: lem-sf-native-integral-tensor-localization). -/
theorem stageLocalization_eq (E : Index l (PadicAlgCl l)) :
    stageLocalization l X E =
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X := by
  rfl

instance stageLocalization_shift (E : Index l (PadicAlgCl l)) :
    (stageLocalization l X E).CommShift ℤ :=
  sfRationalLocalizationCommShift l (Coefficient.{u} l (PadicAlgCl l) E) X

instance stageLocalization_additive (E : Index l (PadicAlgCl l)) :
    (stageLocalization l X E).Additive := by
  exact inferInstanceAs ((sfRationalConstructibleLocalization l
    (Coefficient.{u} l (PadicAlgCl l) E) X).Additive)

instance stageLocalization_triangulated (E : Index l (PadicAlgCl l)) :
    (stageLocalization l X E).IsTriangulated :=
  sfRationalLocalizationTriangulated l (Coefficient.{u} l (PadicAlgCl l) E) X

variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]
variable (C : CoefficientSystem l X)

/-- The morphisms killed by integral uniformizer torsion.
Source: Stacks Tag 05R6 (blueprint: lem-sf-native-integral-tensor-localization). -/
abbrev integralTensorW (E : Index l (PadicAlgCl l)) :=
  Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l
      (Coefficient.{u} l (PadicAlgCl l) E)))
    (sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)

/-- The published tensor-Hom rationalization is the Verdier localization at torsion.
Source: Stacks Tag 05R6 (blueprint: lem-sf-native-integral-tensor-localization). -/
@[instance] theorem integralTensor_localization (E : Index l (PadicAlgCl l)) :
    (stageLocalization l X E).IsLocalization (integralTensorW l X E) := by
  exact ScalarLocalization.semilinear_localization_isLocalization
    (Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E))
    (sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l (PadicAlgCl l) E))

/-- Inverting the uniformizer makes every torsion cone vanish.
Source: Stacks Tag 05R6 (blueprint: lem-sf-native-integral-tensor-localization). -/
theorem integralTensor_inverts (E : Index l (PadicAlgCl l)) :
    (integralTensorW l X E).IsInvertedBy (integralTensor l X C E) := by
  let F := integralTensor l X C E
  let t := Padic.coefficientExtensionUniformizer l (Coefficient.{u} l (PadicAlgCl l) E)
  have hp (Z : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
      (n : ℕ) : IsIso (F.map (t ^ n • 𝟙 Z)) := by
    induction n with
    | zero => simp only [pow_zero, one_smul]; infer_instance
    | succ n ih =>
      letI := ih
      have : IsIso (F.map (t • 𝟙 Z)) := integralTensor_uniformizer_isIso l X C E Z
      have he : t ^ (n + 1) • 𝟙 Z = (t ^ n • 𝟙 Z) ≫ (t • 𝟙 Z) := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
          smul_smul, pow_succ, mul_comm]
      rw [he, F.map_comp]
      infer_instance
  intro A B f hf
  obtain ⟨Z, g, h, hT, a, ha, hz⟩ := hf
  obtain ⟨n, rfl⟩ := ha
  change t ^ n • 𝟙 Z = 0 at hz
  have hzero : IsIso (0 : F.obj Z ⟶ F.obj Z) := by
    have hi := hp Z n
    rw [hz, F.map_zero] at hi
    exact hi
  have hZ : IsZero (F.obj Z) := (isIsoZero_iff_source_target_isZero _ _).mp hzero |>.1
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (F.map_distinguished _ hT)).1 hZ

/-- The rational native tensor functor, defined by the localization universal property.
Source: BS 6.8.14(2) (blueprint: lem-sf-native-integral-tensor-localization). -/
def rationalTensor (E : Index l (PadicAlgCl l)) :
    GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E ⥤
      DerivedCategory (pbcModules X (ringSheaf l X)) :=
  Localization.lift (integralTensor l X C E) (integralTensor_inverts l X C E)
    (stageLocalization l X E)

/-- The universal integral comparison for rational native tensor extension.
Source: Stacks Tag 05R6 (blueprint: lem-sf-native-integral-tensor-localization). -/
def rationalTensorIntegral (E : Index l (PadicAlgCl l)) :
    stageLocalization l X E ⋙
      rationalTensor l X C E ≅ integralTensor l X C E :=
  Localization.fac _ _ _

instance rationalTensor_lifting (E : Index l (PadicAlgCl l)) :
    Localization.Lifting
      (stageLocalization l X E)
      (integralTensorW l X E) (integralTensor l X C E) (rationalTensor l X C E) :=
  ⟨rationalTensorIntegral l X C E⟩

instance rationalTensor_shift (E : Index l (PadicAlgCl l)) :
    (rationalTensor l X C E).CommShift ℤ :=
  Functor.commShiftOfLocalization
    (stageLocalization l X E)
    (integralTensorW l X E) ℤ (integralTensor l X C E) (rationalTensor l X C E)

instance rationalTensorIntegral_shift (E : Index l (PadicAlgCl l)) :
    NatTrans.CommShift (rationalTensorIntegral l X C E).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization
    (stageLocalization l X E)
    (integralTensorW l X E) ℤ (integralTensor l X C E) (rationalTensor l X C E)

instance rationalTensor_additive (E : Index l (PadicAlgCl l)) :
    (rationalTensor l X C E).Additive := by
  let Q := stageLocalization l X E
  have : (Q ⋙ rationalTensor l X C E).Additive :=
    Functor.additive_of_iso (rationalTensorIntegral l X C E).symm
  exact (Localization.functor_additive_iff Q (integralTensorW l X E) _).mpr this

instance rationalTensor_triangulated (E : Index l (PadicAlgCl l)) :
    (rationalTensor l X C E).IsTriangulated := by
  have := Localization.essSurj_mapArrow
    (stageLocalization l X E)
    (integralTensorW l X E)
  exact Functor.isTriangulated_of_precomp_iso (rationalTensorIntegral l X C E)

end WeilConjectures.LocallyFiniteAdicRealization
