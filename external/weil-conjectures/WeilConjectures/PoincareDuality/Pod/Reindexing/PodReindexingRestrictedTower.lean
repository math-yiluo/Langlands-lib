/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
import WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingGoodComplex

/-! # Reindexing the actual restricted coherent tower

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4, 0941 (blueprint: lem-pod-reindexing-restricted-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The actual sequence-pullback unit identifies the full restricted strict towers.
Source: Stacks 03D6, 0941 (blueprint: lem-pod-reindexing-restricted-tower).

Proof: identify the completed coefficient maps by all projections. The existing
whole-tower inverse-image unit then gives the comparison on system modules, with
the stated section formula. Apply it in every cochain degree and convert a complex
of towers to a tower of complexes. Naturality ensures all differentials and quotient
transitions commute. The section formula remains the original adjunction-unit formula. -/
theorem podReindexingRestrictedTower :
    ∃ e : ∀ C : CochainComplex (coefficientSequenceModules l E Y) ℤ,
      (podReindexTower l E g).obj (podRestrictedTower l E C) ≅
        podRestrictedTower l E
          (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj C),
    ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (n : ℕ) (i : ℤ) (U : X.ProEt)
      (x : (C.X i).val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
      (((e C).hom.app (op n)).f i).val.app (op U)
          (integralComparisonRestrictedSection l E Y (C.X i) n
            (op ((proEtaleIsoPostcompose g).obj U)) x) =
        integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E g).obj (C.X i)) n (op U)
          (((integralComparisonSequencePullback l E g).obj (C.X i)).val.map
            (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
            (integralComparisonSequenceGenerator l E g (C.X i) n
              ((proEtaleIsoPostcompose g).obj U) x)) := by
  have hc : inv (isoReductionCompletedMap l E g).hom =
      inv (inverseImageCompletedCoefficientMap l E g) := by
    apply (cancel_mono (inverseImageCompletedCoefficientMap l E g)).mp
    exact (congrArg (inv (isoReductionCompletedMap l E g).hom ≫ ·)
      (podCompletedCoefficientMap_eq l E g).symm).trans
        ((IsIso.inv_hom_id _).trans (IsIso.inv_hom_id _).symm)
  let c : isoReductionIntegralInverse l E g ≅ inverseImageIntegralModules l E g := by
    apply SheafOfModules.pushforwardCongr
    exact hc
  let a := isoWhiskerLeft (coefficientSequenceRestriction l E Y)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso c) ≪≫ integralTowerInverseImageUnit l E g
  let e (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso
      ((NatIso.mapHomologicalComplex a (.up ℤ)).app C)
  refine ⟨e, ?_⟩
  intro C n i U x
  change (((integralTowerInverseImageUnit l E g).hom.app (C.X i)).app (op n)).val.app
    (op U) (((c.hom.app _).val.app (op U)) _) = _
  dsimp only [c]
  erw [SheafOfModules.pushforwardCongr_hom_app_val_app]
  exact (integralTowerInverseImageUnit_existsUnique l E g).exists.choose_spec
    (C.X i) n U x

end WeilConjectures
