/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage

import WeilConjectures.SixFunctors.System.SystemDirectImageRestrictedTowerComparison
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Existence of the direct-image Roos object

This is the object-existence part of the projection-compatible direct-image
comparison.  The construction uses one K-injective system resolution and the
derived tower limit theorem; the finite evaluation comparisons are supplied by
the companion interface theorem.
(blueprint: stage3-weil-system-direct-image-roos-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  AlgebraicGeometry SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option linter.unusedVariables false in
/-- The actual derived system direct image admits a finite-image Roos object.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tag 0941.
Proof: choose a K-injective representative of the reduced object, apply the
derived tower-limit construction to its sectionwise direct image, and transport
the resulting product and triangle along the canonical finite restrictions.
The resulting triangle has exactly `sfDirectImageTransition` as its tower map.
The construction is valid for arbitrary schemes and arbitrary derived inputs,
including zero objects and empty schemes. -/
theorem systemDirectImage_roosExistence
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    let N := (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
      (S.reduction.obj K)
    ∃ hprod : HasProduct (sfDirectImageTerm l E f K),
      ∃ L : @SfIntegralDirectImage l _ E _ _ _ X Y f K hprod,
      ∃ e : ((coefficientSequenceLimit l E Y).obj N ≅ L.obj), True := by
  let A := scalarReductionSource l E Y
  let : IsGrothendieckAbelian.{u + 1} A :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
      (Scheme.ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y)).1
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) :=
    CategoryTheory.UniverseProof.tower_grothendieck A
  let : HasCountableProducts (DerivedCategory A) :=
    ⟨fun J _ ↦ DerivedCategory.hasLimitsOfShape_discrete A J⟩
  let F : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E Y :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun _ _ a ↦ F.rightDerivedFunctorUnitQ_naturality a }
  obtain ⟨V, ⟨ε⟩⟩ := CategoryTheory.UniverseProof.evaluationData (A := A)
  obtain ⟨p, δ, hroos, -, -⟩ := CategoryTheory.UniverseProof.CoreWork.natural_roos
    (coefficientConstantTowerLimit l E Y) η (fun I hI ↦ by
      have := hI
      change IsIso (F.rightDerivedFunctorUnitQ I)
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance) V ε
  let N := (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
    (S.reduction.obj K)
  let Z := (coefficientSequenceDerivedRestriction l E Y).obj N
  let T := DerivedCategory.Q.objPreimage Z
  let e : DerivedCategory.Q.obj T ≅ Z := DerivedCategory.Q.objObjPreimageIso Z
  obtain ⟨a⟩ := systemDirectImage_restrictedTowerComparison l E f S K T e
  let b : V.obj Z ≅ Functor.ofOpSequence (sfDirectImageTransition l E f K) :=
    V.mapIso e.symm ≪≫ ε.app T ≪≫ a
  let c := Limits.Pi.mapIso (fun n : ℕ ↦ b.app (op n))
  have hc : c.hom ≫ towerTransitionEndomorphism (sfDirectImageTransition l E f K) =
      towerTransitionEndomorphism
        (fun n : ℕ ↦ (V.obj Z).map (homOfLE (Nat.le_succ n)).op) ≫ c.hom := by
    change Limits.Pi.map (fun n : ℕ ↦ b.hom.app (op n)) ≫
        towerTransitionEndomorphism (sfDirectImageTransition l E f K) = _
    apply towerTransitionEndomorphism_natural_backward
    intro n
    simpa only [Functor.ofOpSequence_map_homOfLE_succ] using
      (b.hom.naturality (homOfLE (Nat.le_succ n)).op).symm
  let L : SfIntegralDirectImage l E f K :=
    { obj := (coefficientConstantTowerLimit l E Y).obj Z
      projection := p Z ≫ c.hom
      boundary := c.inv ≫ δ Z
      roos := by
        let q := Triangle.mk (p Z)
          (towerTransitionEndomorphism
            (fun n : ℕ ↦ (V.obj Z).map (homOfLE (Nat.le_succ n)).op)) (δ Z)
        let q' := Triangle.mk (p Z ≫ c.hom)
          (towerTransitionEndomorphism (sfDirectImageTransition l E f K)) (c.inv ≫ δ Z)
        let hq : q ≅ q' := Triangle.isoMk q q' (Iso.refl _) c c
          (by simp [q, q']) hc.symm (by simp [q, q'])
        exact Pretriangulated.isomorphic_distinguished q (hroos Z) q' hq.symm }
  exact ⟨inferInstance, L, Iso.refl _, trivial⟩

end WeilConjectures
