/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import all WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryQuotientModuleComparison
import all WeilConjectures.Algebra.Homology.OrdinaryCommonQuotientTower.OrdinaryCommonQuotientTowerSupplement
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenScalarTransitionCompatibility
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenFiniteScalarComparison

/-! # Canonical level transition for the open scalar comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

noncomputable def canonicalOpenQuotientScalarComparisonLevel
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ) :
    (unrestrictedIntegralComplexFunctor l E X n).obj
        ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) ≅
      (OpenSemilinearTensor.extensionComplex l E j o).obj
        ((unrestrictedIntegralComplexFunctor l E U n).obj Q) := by
  let e := Functor.isoWhiskerRight (tc.ordinary n)
      (scalarReductionRestriction l E X n) ≪≫
    Functor.isoWhiskerLeft (scalarReductionExtension l E U n) (sc.finite n)
  exact (NatIso.mapHomologicalComplex e (.up ℤ)).app Q

attribute [local irreducible] scalarReductionExistence
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted

private theorem scalarUnit_epi (W : Scheme.{u}) (n : ℕ)
    (M : scalarReductionSource l E W) :
    Epi ((scalarReductionExtension_adjunction l E W n).choose.unit.app M) := by
  let q := completedIntegralCommRingProjectionUnrestricted l E W n
  let R := scalarReductionRestriction l E W n
  have hobj : (scalarReductionExtension l E W n).obj M =
      SheafOfModules.changeOfRings q M := by
    unfold scalarReductionExtension
    exact (scalarReductionExistence l E W n).choose_spec.choose M
  let e := eqToIso hobj
  let η := (scalarReductionExtension_adjunction l E W n).choose.unit.app M
  have hq : Presheaf.IsLocallySurjective (ProEt.topology W) q.hom :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (IntegralOnSlice.projection_surjective l E W n)
  have he : Epi (η ≫ R.map e.hom) := SheafOfModules.quotientUnit_epi q hq M
    (η ≫ R.map e.hom) (by
      intro V x
      change e.hom.val.app V (η.val.app V x) = _
      exact OpenSemilinearTensor.scalarUnit_raw l E W n M V x)
  have : IsIso (R.map e.hom) := (R.mapIso e).isIso_hom
  exact (epi_comp_iff_of_isIso η (R.map e.hom)).mp he

private theorem transition_unit (W : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (i : ℤ) :
    (scalarReductionExtension_adjunction l E W (n + 1)).choose.unit.app (P.X i) ≫
        ((unrestrictedIntegralTransition l E W n).app P).f i =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app (P.X i) := by
  ext V x
  change (((unrestrictedIntegralTransition l E W n).app P).f i).val.app V
      (((unrestrictedTowerUnit l E W P (n + 1)).f i).val.app V x) =
    (((unrestrictedTowerUnit l E W P n).f i).val.app V x)
  rw [unrestrictedTowerUnit_condition, unrestrictedTowerUnit_condition]
  change (((unrestrictedIntegralTransition l E W n).app P).f i).val.app V
      (unrestrictedIntegralTensorSection l E W (n + 1) (P.X i) V 1 x) =
    unrestrictedIntegralTensorSection l E W n (P.X i) V 1 x
  have hone : ((integralCoefficientSheafTransition l E W n).hom.app V) (1 : _) = 1 :=
    map_one ((integralCoefficientSheafTransition l E W n).hom.app V).hom
  exact ((unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec
    P i V 1 x).trans
      (congrArg (fun a ↦ unrestrictedIntegralTensorSection l E W n (P.X i) V a x) hone)

private theorem canonical_unit
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ) (i : ℤ) :
    (scalarReductionExtension_adjunction l E X n).choose.unit.app
        ((IntegralOpenReduction.extension l E j o).obj (Q.X i)) ≫
      (canonicalOpenQuotientScalarComparisonLevel l E j o tc sc n Q).hom.f i =
    (IntegralOpenReduction.extension l E j o).map
      ((scalarReductionExtension_adjunction l E U n).choose.unit.app (Q.X i)) := by
  apply OpenSemilinearTensor.extensionSection_ext l E j o (Q.X i) _
  intro V a x
  change ((sc.finite n).hom.app
      ((scalarReductionExtension l E U n).obj (Q.X i))).val.app (op V)
    (((tc.ordinary n).hom.app (Q.X i)).val.app (op V)
      (((scalarReductionExtension_adjunction l E X n).choose.unit.app
        ((IntegralOpenReduction.extension l E j o).obj (Q.X i))).val.app (op V)
          (IntegralOpenReduction.extensionSection l E j o (Q.X i) V a x))) = _
  have ht := congrArg
    (fun z ↦ ((sc.finite n).hom.app
      ((scalarReductionExtension l E U n).obj (Q.X i))).val.app (op V) z)
    (tc.generators n (Q.X i) V a x)
  have hs := sc.sections n ((scalarReductionExtension l E U n).obj (Q.X i)) V a
    (coefficientIntegralScalarUnitSection l E U n (Q.X i)
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)
  have hm := OpenSemilinearTensor.extensionSection_map l E j o
    ((scalarReductionExtension_adjunction l E U n).choose.unit.app (Q.X i)) V a x
  exact ht.trans (hs.trans hm.symm)

/-- The canonical finite-level comparison satisfies successor transition coherence.
This is the generator calculation for the unrestricted quotient transition: on each
sheafified pure tensor, both composites apply the same coefficient quotient and the
same normalized extension section. Source: Stacks Tags 0E8I and 0941. -/
theorem openQuotientScalarComparisonCanonicalTransition
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ) (i : ℤ) :
    ((unrestrictedIntegralTransition l E X n).app
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q)).f i ≫
        (canonicalOpenQuotientScalarComparisonLevel l E j o tc sc n Q).hom.f i =
      (canonicalOpenQuotientScalarComparisonLevel l E j o tc sc (n + 1) Q).hom.f i ≫
        ((OpenSemilinearTensor.extensionComplex l E j o).map
          ((unrestrictedIntegralTransition l E U n).app Q)).f i := by
  let F := IntegralOpenReduction.extension l E j o
  let P := (OpenSemilinearTensor.extensionComplex l E j o).obj Q
  let ηX := fun k ↦ (scalarReductionExtension_adjunction l E X k).choose.unit.app
    (F.obj (Q.X i))
  let ηU := fun k ↦ (scalarReductionExtension_adjunction l E U k).choose.unit.app (Q.X i)
  let R := fun (W : Scheme.{u}) k ↦
    scalarReductionExtension l E W k ⋙ scalarReductionRestriction l E W k
  let τX : (R X (n + 1)).obj (F.obj (Q.X i)) ⟶ (R X n).obj (F.obj (Q.X i)) :=
    ((unrestrictedIntegralTransition l E X n).app P).f i
  let τU : (R U (n + 1)).obj (Q.X i) ⟶ (R U n).obj (Q.X i) :=
    ((unrestrictedIntegralTransition l E U n).app Q).f i
  let c : ∀ k, (R X k).obj (F.obj (Q.X i)) ⟶ F.obj ((R U k).obj (Q.X i)) :=
    fun k ↦ (canonicalOpenQuotientScalarComparisonLevel l E j o tc sc k Q).hom.f i
  have := scalarUnit_epi l E X (n + 1) (F.obj (Q.X i))
  apply (cancel_epi (ηX (n + 1))).mp
  change ηX (n + 1) ≫ (τX ≫ c n) = ηX (n + 1) ≫ (c (n + 1) ≫ F.map τU)
  calc
    ηX (n + 1) ≫ (τX ≫ c n) = (ηX (n + 1) ≫ τX) ≫ c n :=
      (Category.assoc _ _ _).symm
    _ = ηX n ≫ c n := congrArg (· ≫ c n) (transition_unit l E X n P i)
    _ = F.map (ηU n) := canonical_unit l E j o tc sc n Q i
    _ = F.map (ηU (n + 1) ≫ τU) :=
      congrArg F.map (transition_unit l E U n Q i).symm
    _ = F.map (ηU (n + 1)) ≫ F.map τU := F.map_comp _ _
    _ = (ηX (n + 1) ≫ c (n + 1)) ≫ F.map τU :=
      congrArg (· ≫ F.map τU) (canonical_unit l E j o tc sc (n + 1) Q i).symm
    _ = ηX (n + 1) ≫ (c (n + 1) ≫ F.map τU) := Category.assoc _ _ _

end WeilConjectures.OpenTensorQuotient
