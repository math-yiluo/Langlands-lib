/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.SixFunctors.System.SystemDirectImageRoosExistence
import WeilConjectures.SixFunctors.System.SystemDirectImageRoosEvaluation

/-! # Projection-compatible Roos presentation of system direct image

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tag 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The limit of the actual derived system direct image has the finite-image Roos
presentation, with its actual limit projections. This is a comparison of models;
it asserts neither normalization nor invertibility of any reconstruction counit.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tag 0941;
steps 1--2 of lem-weil-system-direct-image-effectivity
(blueprint: lem-weil-system-direct-image-roos-presentation).

Proof: resolve the reduction of K once in the category of modules on the ringed
sequence site. Section-normalized direct-image evaluation identifies its nth derived
fiber with the finite derived direct image of the nth reduction of K. The reduction
model identifies the quotient transitions on the source. The ordinary evaluation
comparison is identity on sections, so its simultaneous derived comparison commutes
with restriction transitions. After restriction to completed coefficients these are
exactly sfDirectImageTransition, including the resolution-normalized restriction
comparisons in that definition. Apply the constant-ring tower Roos model for the
specified total limit. Transport its two product terms by the finite evaluation
isomorphisms; the transition equality transports its 1-shift map. The resulting
triangle defines L. Its first map is transported from the actual total-limit
projection, giving the displayed equality for every n. This argument does not use
completeness, boundedness, constructibility, finite type, or invertibility of l on
the schemes. In particular it includes zero complexes and empty schemes. -/
theorem systemDirectImage_roosPresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    let N := (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
      (S.reduction.obj K)
    ∃ hprod : HasProduct (sfDirectImageTerm l E f K),
      ∃ L : @SfIntegralDirectImage l _ E _ _ _ X Y f K hprod,
        ∃ e : (coefficientSequenceLimit l E Y).obj N ≅ L.obj,
          ∃ a : ∀ n : ℕ, (coefficientSequenceDerivedEvaluation l E Y n).obj N ≅
            sfFiniteDerivedDirectImage l E f K n,
            ∀ n : ℕ, (coefficientSequenceProjection l E Y n).app N ≫
                (coefficientFiniteDerivedRestriction l E Y n).map (a n).hom =
              e.hom ≫ L.projection ≫ Pi.π (sfDirectImageTerm l E f K) n := by
  dsimp
  obtain ⟨hprod, L, e, _⟩ := systemDirectImage_roosExistence l E f S K
  letI := hprod
  obtain ⟨a, ha⟩ := systemDirectImage_roosEvaluation l E f S K L e
  exact ⟨hprod, L, e, a, ha⟩

end WeilConjectures
