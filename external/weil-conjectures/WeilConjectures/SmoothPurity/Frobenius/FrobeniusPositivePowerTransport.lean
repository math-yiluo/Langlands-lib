/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageHomComparison
import all WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackExistence
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower

/-! # Positive powers of a coefficient-identified pullback comparison

Source: Stacks, Modules on Sites, Tag 03EL; coefficient-twist clause 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private instance powerSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleModuleInverseImage SheafOfModules.monoidalCategory
  SheafOfModules.siteSheafTensorRight SheafOfModules.tensorIsoSite

section
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)

private def powerTensorIso (M N : proEtaleRingModules Y R) :
    (proEtaleRingModulePullback g R S c).obj
        ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} N).obj M) ≅
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        ((proEtaleRingModulePullback g R S c).obj N)).obj
        ((proEtaleRingModulePullback g R S c).obj M) :=
  (proEtaleRingModulePullback g R S c).mapIso
      (SheafOfModules.tensorIsoSite R M N).symm ≪≫
    ((proEtaleOrdinaryTensorPullback_existsUnique g R S c).exists.choose M N) ≪≫
    SheafOfModules.tensorIsoSite S _ _

omit [IsIso g] in
private theorem powerTensorIso_section (M N : proEtaleRingModules Y R)
    (V : Y.ProEt) (x : M.val.obj (op V)) (y : N.val.obj (op V)) :
    (powerTensorIso g R S c M N).hom.val.app (op ((proEtaleBaseChange g).obj V))
      (((proEtaleRingModuleAdjunction g R S c).unit.app
        ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} N).obj M)).val.app (op V)
          (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} M N (op V) x y)) =
    SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ (op ((proEtaleBaseChange g).obj
      V))
      (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op V) x)
      (((proEtaleRingModuleAdjunction g R S c).unit.app N).val.app (op V) y) := by
  let j := SheafOfModules.tensorIsoSite R M N
  have hu := congrArg (fun k ↦ k.val.app (op V)
    (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} M N (op V) x y))
      ((proEtaleRingModuleAdjunction g R S c).unit.naturality j.inv)
  change ((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V)
      (j.inv.val.app (op V) _) =
    ((proEtaleRingModulePullback g R S c).map j.inv).val.app
      (op ((proEtaleBaseChange g).obj V))
      (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) _) at hu
  have hj := SheafOfModules.tensorIsoSite_inv_pure R M N (op V) x y
  change j.inv.val.app (op V) _ = proEtaleTensorPair Y R M N (op V) x y at hj
  rw [hj] at hu
  change (SheafOfModules.tensorIsoSite S _ _).hom.val.app _
    ((((proEtaleOrdinaryTensorPullback_existsUnique g R S c).exists.choose M N).hom.val.app _)
      (((proEtaleRingModulePullback g R S c).map j.inv).val.app _ _)) = _
  rw [← hu]
  have ht := (proEtaleOrdinaryTensorPullback_existsUnique g R S c).exists.choose_spec.2
    M N V x y
  exact (congrArg (fun z ↦ (SheafOfModules.tensorIsoSite S _ _).hom.val.app
    (op ((proEtaleBaseChange g).obj V)) z) ht).trans
      (SheafOfModules.tensorIsoSite_pure S _ _ _ _ _)

attribute [local irreducible] powerTensorIso

private instance powerAdjoint :
    (SheafOfModules.pushforward.{u + 1}
      (AlgebraicGeometry.ProEtale.moduleStructuralMap g R S c)).IsRightAdjoint :=
  SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
    (U := proEtaleBaseChange g) _

private def powerUnitIso :
    (proEtaleRingModulePullback g R S c).obj
      (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
    SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) := by
  let : (proEtaleBaseChange g).IsEquivalence := PurHom.baseChange_equivalence g
  exact (AlgebraicGeometry.ProEtale.modulePullbackComparison g R S c).app _ ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit
      (AlgebraicGeometry.ProEtale.moduleStructuralMap g R S c))

private theorem powerUnitIso_section (V : Y.ProEt) (a : R.obj.obj (op V)) :
    (powerUnitIso g R S c).hom.val.app (op ((proEtaleBaseChange g).obj V))
      (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) a) =
      (proEtaleRingDirectImageMap g R S c).hom.app (op V) a := by
  change (SheafOfModules.pullbackObjUnitToUnit _).val.app _
    (((AlgebraicGeometry.ProEtale.modulePullbackComparison g R S c).hom.app _).val.app _
      (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) a)) = _
  have hu := AlgebraicGeometry.ProEtale.modulePullbackComparison_unit g R S c
    (SheafOfModules.unit _) V a
  exact (congrArg (fun z ↦ (SheafOfModules.pullbackObjUnitToUnit
    (AlgebraicGeometry.ProEtale.moduleStructuralMap g R S c)).val.app
      (op ((proEtaleBaseChange g).obj V)) z) hu).trans
        (SheafOfModules.pullback_unit_pure _ V a)

/-- A comparison of first modules extends to nonnegative powers, with the unit and
binary tensor formulas. No root sections, local freeness, or negative powers enter.
Source: Stacks, Modules on Sites, Tag 03EL; coefficient-twist clause 3.
(blueprint: lem-weil-frobenius-positive-power-transport).
Proof: use the ordinary tensor pullback comparison and the canonical identification
between the monoidal tensor and the sheafified sectionwise tensor. Their unit-section
formulas agree. At zero use pullback of the coefficient unit. At one use e. Recursively
compose the tensor pullback comparison with the tensor of the preceding map and e.
The pure-tensor formulas give the two asserted normalizations at every step. -/
theorem frobeniusPositivePowerTransport
    (M : proEtaleRingModules Y R) (N : proEtaleRingModules X S)
    (e : (proEtaleRingModulePullback g R S c).obj M ≅ N) :
    ∃ P : ∀ d : ℕ, (proEtaleRingModulePullback g R S c).obj
        (coefficientTwistPower Y (R := R) M d) ≅
          coefficientTwistPower X (R := S) N d,
      (∀ (V : Y.ProEt) (a : R.obj.obj (op V)),
        (P 0).hom.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) a) =
          (proEtaleRingDirectImageMap g R S c).hom.app (op V) a) ∧
      P 1 = e ∧
      ∀ (d : ℕ) (V : Y.ProEt)
        (x : (coefficientTwistPower Y (R := R) M (d + 1)).val.obj (op V))
        (y : M.val.obj (op V)),
        (P (d + 2)).hom.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V)
            (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ (op V) x y)) =
        SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ (op ((proEtaleBaseChange
          g).obj V))
          ((P (d + 1)).hom.val.app _
            (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) x))
          (e.hom.val.app _
            (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) y)) := by
  let pos : ∀ d : ℕ, (proEtaleRingModulePullback g R S c).obj
      (coefficientTwistPower Y (R := R) M (d + 1)) ≅
        coefficientTwistPower X (R := S) N (d + 1) := fun d ↦
    Nat.rec (motive := fun d ↦ (proEtaleRingModulePullback g R S c).obj
      (coefficientTwistPower Y (R := R) M (d + 1)) ≅
        coefficientTwistPower X (R := S) N (d + 1)) e
      (fun d prev ↦ powerTensorIso g R S c _ M ≪≫
        (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} _).mapIso prev ≪≫
        SheafOfModules.tensorSecondIso.{u + 1, u, u + 1} _ e) d
  let P : ∀ d : ℕ, (proEtaleRingModulePullback g R S c).obj
      (coefficientTwistPower Y (R := R) M d) ≅
        coefficientTwistPower X (R := S) N d
    | 0 => powerUnitIso g R S c
    | d + 1 => pos d
  refine ⟨P, powerUnitIso_section g R S c, rfl, ?_⟩
  intro d V x y
  change (SheafOfModules.tensorSecondIso.{u + 1, u, u + 1} _ e).hom.val.app _
    (((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} _).map (P (d + 1)).hom).val.app
      _
      ((powerTensorIso g R S c _ M).hom.val.app _ _)) = _
  erw [powerTensorIso_section]
  let ux : ((proEtaleRingModulePullback g R S c).obj
      (coefficientTwistPower Y (R := R) M (d + 1))).val.obj
        (op ((proEtaleBaseChange g).obj V)) :=
    ((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) x
  let uy : ((proEtaleRingModulePullback g R S c).obj M).val.obj
      (op ((proEtaleBaseChange g).obj V)) :=
    ((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op V) y
  have hf := SheafOfModules.scalarTensor_first_tmul (P (d + 1)).hom
    ((proEtaleRingModulePullback g R S c).obj M)
    (op ((proEtaleBaseChange g).obj V)) ux uy
  exact (congrArg (fun z ↦
    (SheafOfModules.tensorSecondIso.{u + 1, u, u + 1} _ e).hom.val.app
      (op ((proEtaleBaseChange g).obj V)) z) hf).trans
        (SheafOfModules.scalarTensor_second_tmul _ e.hom _ _ uy)

end
end WeilConjectures
