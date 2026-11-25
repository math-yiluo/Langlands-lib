/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair

/-! # Exact tensor preserves the constant coefficient action

Source: Stacks 03EL and the derived localization construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{u})

/-- Exact sheaf tensor preserves the recorded constant-section action after deriving.
Source: Stacks 03EL and Mathlib derived localization
(blueprint: lem-pur-exact-tensor-coefficient-linear).
Proof: tensor is linear over global sections. Restrict this action along the constant
coefficient homomorphism. Transport it through the specified site tensor comparison.
The recorded derived action is the localization of this sheaf action, by uniqueness
of the localized central action. The localization universal property therefore sends
the sheaf scalar equality to the same equality on all derived morphisms. -/
theorem exactTensorCoefficientLinear (P : integralTowerModules l E Y)
    [(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E Y) P).Additive]
    [PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E Y) P)]
    [PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E Y) P)] :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E Y) P).mapDerivedCategory.Linear
        (Padic.coefficientExtensionIntegers l E) := by
  let T := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    (A := completedIntegralCommRingSheafUnrestricted l E Y) P
  let R := Padic.coefficientExtensionIntegers l E
  let A := completedIntegralCommRingSheafUnrestricted l E Y
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : MonoidalCategory (integralTowerModules l E Y) :=
    @SheafOfModules.cochainModulesMonoidal.{u + 1, u, u + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _) J inferInstance A
  let := coefficientModuleLinear l E Y
  have ht : (MonoidalCategory.tensorRight P).Linear R := by
    constructor
    intro M N f a
    have ht := @SheafOfModules.LineEvaluation.tensor_linear.{u + 1, u, u}
      Y.ProEt inferInstance J (essentiallySmallSelf.{0, u, u + 1} _)
      (inferInstance : J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) A P
    exact ht.map_smul f (coefficient_scalarSections l E Y a)
  have hs : T.Linear R := by
    dsimp only [T]
    exact Functor.linear_of_iso R
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} A P).symm
  have he : integralCoefficientLinear l E Y = coefficientDerivedLinear l E Y := by
    apply coefficientLinear_ext
    intro K K' a f
    rw [(integralCoefficientLinear_existsUnique l E Y).exists.choose_spec]
    rw [coefficientDerived_eq]
    rfl
  -- Use the action characterized by localization, including all derived morphisms.
  change @Functor.Linear R _ _ _ _ _ _ _
    (integralCoefficientLinear l E Y) (integralCoefficientLinear l E Y) _
  rw [he]
  let := coefficientDerivedLinear l E Y
  let := Localization.functor_linear R
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
  have : (T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).Linear R := by
    infer_instance
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
      (T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) T.mapDerivedCategory :=
    ⟨T.mapDerivedCategoryFactors⟩
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)) R
    (T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) T.mapDerivedCategory).mp inferInstance

end WeilConjectures
