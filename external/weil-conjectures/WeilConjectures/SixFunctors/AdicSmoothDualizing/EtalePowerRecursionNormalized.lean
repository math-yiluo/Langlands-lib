/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicSmoothDualizing.AdicSmoothDualizingPowerData

/-! # Normalization from the finite Tate-power recurrence

Source: the ordered tensor-power construction in the smooth-dualizing corollary.
(blueprint: lem-sf-etale-power-recursion-normalized).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace AdicSmoothDualizing

/-- A family with the specified zero and successor equations has the original full normalization.
Source: ordered finite Tate powers (blueprint: lem-sf-etale-power-recursion-normalized).
Proof: at zero use the supplied heterogeneous equality. For each successor take the actual
right-tensor map, tensor-shift comparison, flat single-complex comparison and sheaf-power
map as witnesses. Their heterogeneous equalities are reflexive, and the supplied successor
equation is precisely the required composite equation. -/
theorem etalePowerPresentation_normalized (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤)))
    (c : (d : ℕ) → P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧)
    (hzero : HEq (c 0) (((shiftFunctorZero _ ℤ).app (P.diagonalTwistEtale T 0)).symm))
    (hsucc : ∀ d, c (d + 1) = etalePowerPresentationNext P T hT d (c d)) :
    letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    HEq (c 0) (((shiftFunctorZero _ ℤ).app (P.diagonalTwistEtale T 0)).symm) ∧
      ∀ d : ℕ,
        ∃ (e₁ : P.diagonalTwistEtale T (d + 1) ≅
              ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧))
          (e₂ : ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧) ≅
              (((etaleTensor P T).obj (etaleSingle P T d)).obj
                (etaleSingle P T 1))⟦2 * (d : ℤ) + 2⟧)
          (e₃ : ((etaleTensor P T).obj (etaleSingle P T d)).obj (etaleSingle P T 1) ≅
              (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d))
          (e₄ : (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d) ≅
              etaleSingle P T (d + 1)),
          HEq e₁ ((Etale.derivedTensorRight (ModuleCat.{u + 1} P.Coefficient) T
            ((etaleSingle P T 1)⟦(2 : ℤ)⟧)).mapIso (c d)) ∧
          HEq e₂ (Etale.derivedTensorShiftIso (ModuleCat.{u + 1} P.Coefficient) (X := T)
            (etaleSingle P T d) (etaleSingle P T 1) (2 * (d : ℤ)) 2) ∧
          HEq e₃ (Etale.singleFunctorObjTensorIso
            (A := ModuleCat.{u + 1} P.Coefficient) (X := T)
            (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates d)
            (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates) (etalePowerFlat P T hT d)) ∧
          HEq e₄ ((DerivedCategory.singleFunctor _ 0).mapIso (etalePowerStep P T d)) ∧
          c (d + 1) = e₁ ≪≫ e₂ ≪≫
            (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso (e₃ ≪≫ e₄) ≪≫
            eqToIso (congrArg (fun j : ℤ ↦ (etaleSingle P T (d + 1))⟦j⟧)
              (PurityFiniteSetting.frameDegreeNext d)) := by
  refine ⟨hzero, ?_⟩
  intro d
  refine ⟨_, _, _, _, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, ?_⟩
  exact hsucc d

end AdicSmoothDualizing
end WeilConjectures
