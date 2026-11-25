/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientTowerLimitAcyclicAux
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientTowerLimitAcyclicResolution

/-! # Inverse-limit acyclicity of completed-coefficient tower direct image

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0D6E.
(blueprint: lem-pur-completed-coefficient-tower-limit-acyclic).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

local instance completedPushTowerZeroMain {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X)) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).PreservesZeroMorphisms := by
  constructor
  intro A B
  ext n
  rfl

theorem towerLimit_push_acyclic {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (target : SiteLimitData l E Y)
    (I : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ) (hI : I.IsKInjective) :
    IsIso (target.limit.unit.app
      ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)).mapHomologicalComplex
        (.up ℤ)).obj I)) := by
  let F := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f c)
  let FC := F.mapHomologicalComplex (.up ℤ)
  obtain ⟨T, j, hT, hj⟩ := completedTower_exists_isKInjective l E f c I
  letI : QuasiIso j := hj
  have hlim := towerLimit_push_acyclic_aux l E f c I hI T hT j
  letI : QuasiIso (((lim : (ℕᵒᵖ ⥤ Mod Y (R l E Y)) ⥤
      Mod Y (R l E Y)).mapHomologicalComplex (.up ℤ)).map j) := hlim
  have huT : IsIso (target.limit.unit.app T) := target.limit.computes T hT
  have hn := target.limit.unit.naturality j
  dsimp only [Functor.comp_map] at hn
  have hcomp : IsIso (target.limit.unit.app (FC.obj I) ≫
      target.limit.functor.map (DerivedCategory.Q.map j)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (target.limit.functor.map (DerivedCategory.Q.map j))

end WeilConjectures.CompletedCoefficientPushforward
