/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralDiscreteTransport
import all WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralDiscreteTransportInvertible
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusScalarTensorTransport

set_option linter.privateModule false

/-! # Transport of the first finite root line

Source: expanded DAG prose-10-21, clause 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleModuleInverseImage completedIntegralCoefficientSheafUnrestricted
  Padic
attribute [local instance_reducible] PurCompactSupport.completed

attribute [local implicit_reducible] constantSheaf sheafCompose Functor.sheafPushforwardContinuous
  MorphismProperty.Over.pullback Scheme.instCategoryProEt
  proEtaleRingModuleDirectImage ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  SheafOfModules.changeOfRingsOfUniverses
  integralCoefficientCommRingSheaf PurCompactSupport.finite
  isoModulePushforwardEquivalence SheafOfModules.pushforwardPushforwardEquivalence
  isoBaseChangeEquivalence SheafOfModules.toSheaf purTwistIntegralModule purTwistIntegralOne
  PresheafOfModules.presheaf purTwistZlOne

private theorem rootTransport_isIso
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose)) :
    IsIso r := by
  classical
  rw [hr]
  let c := ((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose
  have hc : ∀ k, IsIso (c.app k) := by
    intro k
    dsimp only [c]
    rw [((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose_spec k.unop]
    exact ((proEtaleRootsOfUnityInverseImageIso g).2.2.2 inferInstance
      (l ^ (k.unop + 1)) (pow_pos (Fact.out : l.Prime).pos _)).1
  have : IsIso c := (NatTrans.isIso_iff_isIso_app c).2 hc
  have := proEtaleIso_inverseLimitComparison g AddCommGrpCat.{u + 1}
    (proEtaleRootsOfUnityTower Y l Fact.out)
  infer_instance

private theorem retypeDirectImage
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (σ : R ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj S)
    (hc : proEtaleRingDirectImageMap g R S c = σ)
    (M : proEtaleRingModules Y R) (N : proEtaleRingModules X S)
    (d : M ⟶ (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      (S := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      ⟨Functor.whiskerRight σ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩).obj N)
    (hd : IsIso ((SheafOfModules.toSheaf _).map d)) :
    ∃ ψ : M ⟶ (proEtaleRingModuleDirectImage g R S c).obj N,
      IsIso ψ ∧ ∀ (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
        ψ.val.app U x = d.val.app U x := by
  let ψ : M ⟶ (proEtaleRingModuleDirectImage g R S c).obj N :=
    { val := PresheafOfModules.homMk ((SheafOfModules.toSheaf _).map d).hom (by
        intro U a t
        change d.val.app U (a • t) =
          (show S.obj.obj ((proEtaleBaseChange g).op.obj U) from
            (proEtaleRingDirectImageMap g R S c).hom.app U a) •
          (show N.val.obj ((proEtaleBaseChange g).op.obj U) from d.val.app U t)
        rw [hc]
        exact (d.val.app U).hom.map_smul a t) }
  have hψ : IsIso ψ := by
    have : IsIso ((SheafOfModules.toSheaf _).map ψ) := hd
    exact isIso_of_reflects_iso ψ (SheafOfModules.toSheaf _)
  exact ⟨ψ, hψ, fun _ _ ↦ rfl⟩

end WeilConjectures
