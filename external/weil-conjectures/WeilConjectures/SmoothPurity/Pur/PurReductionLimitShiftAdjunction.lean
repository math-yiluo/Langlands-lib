/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.Supporting.PurReductionLimitShiftData
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.SmoothPurity.SequenceKInjectiveComparison.SequenceKInjectiveComparisonShifts
import WeilConjectures.SmoothPurity.Pur.PurReductionFiniteShiftNormalization
import WeilConjectures.SmoothPurity.Pur.PurCoefficientRoosShiftNormalization
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

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
/-!
# Shift compatibility of the coefficient reduction/limit adjunction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-thm-sf-package/fix-prop-coherence.proof.md`, coefficient-comparison sentence
(blueprint: lem-pur-reduction-limit-shift-adjunction).

The finite K-flat comparison fixes the reduction shift. The actual resolution
comparison fixes the limit shift on every K-injective replacement, including
`j[r]`. The Roos triangles below have this very limit as their first vertex;
their connecting maps satisfy the signed shift equation for that comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genInjectivity false

-- Use the existing coefficient-universe sheafification on the small site.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceRestriction coefficientSequenceEvaluation
  coefficientFiniteDerivedExtension scalarReductionExtension
  coefficientFiniteReductionModel coefficientSequenceLimit coefficientConstantTowerLimit
  HasDerivedCategory.standard
  SheafOfModules.monoidalCategory
  coefficientSequenceCommRingSheaf

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Every supplied coherent coefficient calculus admits the prescribed termwise
shift comparisons, with its actual unit and counit.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-thm-sf-package/fix-prop-coherence.proof.md`, coefficient-comparison sentence
(blueprint: lem-pur-reduction-limit-shift-adjunction).

Proof:
1. Give the total limit the canonical composite shift `totalLimitCommShift` of
   lem-pur-sequence-kinjective-comparison-shifts, and give `S.reduction` the
   left-adjoint mate shift of the actual adjunction `S.adjunction`.
2. lem-pur-reduction-finite-shift-normalization supplies the finite shifts,
   `finite_shift_model` and the shift compatibility of every evaluation.
3. The ringed-site Grothendieck theorem (prop-pur-kinjective-resolutions-exist)
   and the derived-category product construction give countable products.
4. lem-pur-coefficient-roos-shift-normalization supplies the replacement-model
   limit equation, the normalized Roos triangles and their signed shift equations.
5. The adjunction commutes with the shifts by construction of the mate, so
   Mathlib's `Adjunction.shift_unit_app` and
   `Adjunction.commShiftIso_hom_app_counit_app_shift` give the unit and counit
   equations for every integer r.
6. At r=0 the comparisons are identities; at r=1 and -1 the first cone
   coordinate is negated. Signs multiply for repeated shifts. Zero complexes,
   degree-zero sheaves and the empty scheme require no additional hypothesis.
-/
theorem purReductionLimitShiftAdjunction
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S) :
    Nonempty (PurReductionLimitShiftData l E W S) := by
  let sL := SequenceKInjectiveComparison.totalLimitCommShift l E W
  let : (coefficientSequenceLimit l E W).CommShift ℤ := sL
  let sR := S.adjunction.leftAdjointCommShift ℤ
  let : S.reduction.CommShift ℤ := sR
  have ha : S.adjunction.CommShift ℤ := S.adjunction.commShift_of_rightAdjoint ℤ
  let := ha
  obtain ⟨sF, hF, hEval⟩ := purReductionFiniteShiftNormalization l E W S hS
  let : IsGrothendieckAbelian.{max u (t + 1)} (scalarReductionSource l E W) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  have products : HasCountableProducts (DerivedCategory (scalarReductionSource l E W)) :=
    ⟨fun J _ ↦ DerivedCategory.hasLimitsOfShape_discrete (scalarReductionSource l E W) J⟩
  let := products
  obtain ⟨hLimit, roos, hRoos⟩ := purCoefficientRoosShiftNormalization l E W
  refine ⟨{
    reduction_shift := sR
    finite_reduction_shift := sF
    finite_shift_model := hF
    reduction_shift_evaluation := hEval
    limit_shift := sL
    limit_shift_resolution := ?_
    products := products
    roos := roos
    roos_triangle_shift := hRoos
    unit_shift := ?_
    counit_shift := ?_ }⟩
  · intro N I j hI hj r hIr hjr
    exact hLimit N I j r
  · intro r P
    exact S.adjunction.shift_unit_app r P
  · intro r N
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      (S.adjunction.commShiftIso_hom_app_counit_app_shift ℤ r N).symm

end WeilConjectures
