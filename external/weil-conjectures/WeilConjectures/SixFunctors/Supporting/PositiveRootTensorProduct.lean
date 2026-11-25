/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

set_option linter.privateModule false

/-! # Multiplication of unshifted positive root powers

Source: coefficient-twist tensor-power conventions and orientation comparison conventions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u c v r
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open SheafOfModules
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted Padic
  SheafOfModules.monoidalCategory

section PowerConstruction
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (L : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

end PowerConstruction

section RootFormulas
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u})

open FrobeniusCoefficientTwists

private theorem generator_smul (U : X.ProEtᵒᵖ)
    (a b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (d : ℕ) (x : Fin d → (purTwistZlOne X l).obj.obj U) :
    a • generator l E X U b d x = generator l E X U (a * b) d x := by
  induction d using Nat.twoStepInduction with
  | zero => rfl
  | one => exact (mul_smul a b _).symm
  | more d _ ih =>
    let M := positiveLine l E X (d + 1)
    let L := purTwistIntegralModule X l E
    let z := purTwistIntegralTensor X l E U 1 (x (Fin.last (d + 1)))
    let T := siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) M L U
    exact (scalarTensorTmul_smul_first
      (R := completedIntegralCommRingSheafUnrestricted l E X) M L U a
        (generator l E X U b (d + 1) (fun i ↦ x i.castSucc)) z).symm.trans
      (congrArg (fun w ↦ T w z) (ih (fun i ↦ x i.castSucc)))

private theorem rootTensor_restrict {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (purTwistZlOne X l).obj.obj U) :
    (purTwistIntegralModule X l E).val.map f (purTwistIntegralTensor X l E U 1 x) =
      purTwistIntegralTensor X l E V 1 ((purTwistZlOne X l).obj.map f x) := by
  change (purTwistIntegralOne X l E).val.map f
    (purTwistIntegralTensor X l E U 1 x) =
      purTwistIntegralTensor X l E V 1 ((purTwistZlModule X l).val.map f x)
  have h := scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
    (purTwistConstantIntegersMap X l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l)) f 1 x
  rw [map_one] at h
  exact h

private theorem generator_restrict {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (d : ℕ) (x : Fin d → (purTwistZlOne X l).obj.obj U) :
    (positiveLine l E X d).val.map f (generator l E X U a d x) =
      generator l E X V
        ((completedIntegralCoefficientSheafUnrestricted l E X).obj.map f a) d
        (fun i ↦ (purTwistZlOne X l).obj.map f (x i)) := by
  induction d using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    change (purTwistIntegralModule X l E).val.map f
      (@SMul.smul _ _ (purTwistIntegralAction X l E U).toSMul a
            (purTwistIntegralTensor X l E U 1 (x 0))) = _
    erw [(purTwistIntegralModule X l E).val.map_smul, rootTensor_restrict]
    rfl
  | more d _ ih =>
    let M := positiveLine l E X (d + 1)
    let L := purTwistIntegralModule X l E
    exact (scalarTensorTmul_naturality
      (R := completedIntegralCommRingSheafUnrestricted l E X) M L f
        (generator l E X U a (d + 1) (fun i ↦ x i.castSucc))
        (purTwistIntegralTensor X l E U 1 (x (Fin.last (d + 1))))).trans
      (congrArg₂ (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) M L V) (ih (fun i ↦ x i.castSucc))
        (rootTensor_restrict l E X f (x (Fin.last (d + 1)))))

end RootFormulas

end WeilConjectures
