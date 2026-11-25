/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos

/-! # Right adjointness and inverse-limit acyclicity of native sequence restriction

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941.
(blueprint: lem-pur-native-sequence-restriction-properties).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurStrictScalar

/-- Native scalar restriction is right adjoint, and a K-injective resolution of its
value on a K-injective native complex becomes a quasi-isomorphism after inverse limit.
Source: Stacks 0940 and 0941
(blueprint: lem-pur-native-sequence-restriction-properties).
Proof: the actual completion projections form a map from the constant completed ring
sheaf to the quotient-ring sequence. Under the sequence/strict-system equivalence,
its restriction functor equals native restriction: its objects have the prescribed
restricted actions, and its transitions and morphisms are the original section maps.
The generic extension/restriction adjunction and the equivalence prove right adjointness.
The equivalence preserves K-injectivity. Restricted-tower resolution acyclicity therefore
says that applying inverse limit to any stated resolution gives a quasi-isomorphism.
Transport this assertion along the functor equality. No assertion that scalar restriction
preserves K-injectivity is used. -/
theorem nativeSequenceRestriction_properties
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    (coefficientSequenceRestriction.{u, u} l E W).IsRightAdjoint ∧
      ∀ (I : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
        [I.IsKInjective] (T : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
        [T.IsKInjective]
        (j : ((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex
          (.up ℤ)).obj I ⟶ T) [QuasiIso j],
        QuasiIso (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ _).mapHomologicalComplex
          (.up ℤ)).map j) := by
  let A := completedIntegralCommRingSheafUnrestricted l E W
  let B := coefficientSequenceCommRingSystem l E W
  let α : (Functor.const ℕᵒᵖ).obj A ⟶ B :=
    NatTrans.ofOpSequence
      (fun n ↦ completedIntegralCommRingProjectionUnrestricted l E W n) (by
        intro n
        dsimp only [B, coefficientSequenceCommRingSystem]
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        change completedIntegralCommRingProjectionUnrestricted l E W n =
          completedIntegralCommRingProjectionUnrestricted l E W (n + 1) ≫
            coefficientSequenceCommRingTransition l E W n
        apply (sheafCompose (ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
        rw [Functor.map_comp]
        have hw := limit.w (integralCoefficientSheafSystem l E W)
          (homOfLE (Nat.le_succ n)).op
        simp only [integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ] at hw
        exact hw.symm)
  let e := SheafOfModules.strictSystemSequenceEquivalence B
  let V := e.inverse ⋙ SheafOfModules.RestrictedTowerResolution.restrictionFunctor A B α
  have hEval (n : ℕ) : SheafOfModules.systemSequenceEvaluation B n =
      coefficientSequenceEvaluation l E W n := by
    have hφ : SheafOfModules.systemSequenceVerticalRingMap B n =
        eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      dsimp only [SheafOfModules.systemSequenceVerticalRingMap]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    exact congrArg (fun φ ↦ SheafOfModules.pushforward.{u + 1}
      (F := Prod.sectR n W.ProEt) φ) hφ
  have hV : V = coefficientSequenceRestriction l E W := by
    apply (coefficientSequenceRestriction_exists l E W).unique
    · refine ⟨?_, ?_, ?_⟩
      · intro M n
        change (SheafOfModules.RestrictedTowerResolution.restriction A B α n).obj
          ((SheafOfModules.systemSequenceEvaluation B n).obj M) = _
        rw [hEval]
        rfl
      · intro M m n h U
        exact HEq.rfl
      · intro M N f n U
        exact HEq.rfl
    · exact (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  have : e.inverse.Additive := inferInstanceAs
    (SheafOfModules.sequenceToStrictSystemFunctor B).Additive
  let P (U : coefficientSequenceModules.{u, u} l E W ⥤
      (ℕᵒᵖ ⥤ scalarReductionSource l E W)) (hU : U.Additive) : Prop :=
    haveI := hU
    U.IsRightAdjoint ∧
      ∀ (I : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
        [I.IsKInjective] (T : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
        [T.IsKInjective] (j : (U.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
        QuasiIso (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ _).mapHomologicalComplex
          (.up ℤ)).map j)
  have hP : ∀ hU : V.Additive, P V hU := by
    intro hU
    have : V.Additive := hU
    dsimp only [P]
    constructor
    · have : (SheafOfModules.RestrictedTowerResolution.restrictionFunctor A B α).IsRightAdjoint :=
        (SheafOfModules.RestrictedTowerResolution.extensionTowerAdjunction A B α).isRightAdjoint
      exact inferInstanceAs
        (e.inverse ⋙
          SheafOfModules.RestrictedTowerResolution.restrictionFunctor A B α).IsRightAdjoint
    · intro I hI T hT j hj
      let I' := (e.inverse.mapHomologicalComplex (.up ℤ)).obj I
      have : CochainComplex.IsKInjective I' := inferInstance
      change (SheafOfModules.RestrictedTowerResolution.restrictionComplex A B α).obj I' ⟶ T at j
      exact SheafOfModules.RestrictedTowerResolution.limit_restricted_quasiIso A B α j
  exact (Eq.mp (congrArg (fun U ↦ ∀ hU : U.Additive, P U hU) hV) hP)
    (coefficientSequenceRestriction_additive l E W)

end WeilConjectures.PurStrictScalar
