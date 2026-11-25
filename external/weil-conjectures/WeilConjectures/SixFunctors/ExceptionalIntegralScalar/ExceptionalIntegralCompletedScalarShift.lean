/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMatesData
import WeilConjectures.SmoothPurity.Completed.CompletedScalarChainShift
/-! # Chain shift normalization for exceptional scalar mates
Source: Stacks Tags 011G, 014E and 08TC.
(blueprint: lem-sf-exceptional-integral-completed-shift)
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
/-- The published completed scalar complex satisfies the signed cone shift formula,
including the comparison from ordinary scalar extension.
Source: Stacks Tags 011G, 014E and 08TC; the Roos-cone realization of completed scalars.
Proof: use completedScalarChainShift for the product and level comparisons. Unfold
the two predicates and their named comparison maps: both express the same first
coordinate product shift and the second coordinate shift multiplied by the sign.
The comparison equation is exactly the second conclusion of completedScalarChainShift.
(blueprint: lem-sf-exceptional-integral-completed-shift). -/
theorem exceptionalIntegralCompletedScalarShift
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (side : Bool) :
    ∃ eC : (integralScalarComplexFunctor l E.carrier L.carrier i
        (endpoint X Y side)).CommShift ℤ,
      (∀ (P : CochainComplex (integralTowerModules l E.carrier (endpoint X Y side)) ℤ)
        (m : ℤ), completedScalarShiftConeFormula i (endpoint X Y side) eC P m) ∧
      ∀ (P : CochainComplex (integralTowerModules l E.carrier (endpoint X Y side)) ℤ)
        (m : ℤ),
        (((completedOrdinaryScalarExtension l E.carrier L.carrier i
            (endpoint X Y side)).mapCochainComplexShiftIso m).hom.app P) ≫
            ((completedScalarChainComparison l E.carrier L.carrier i
              (endpoint X Y side)).app P)⟦m⟧' =
          (completedScalarChainComparison l E.carrier L.carrier i
            (endpoint X Y side)).app (P⟦m⟧) ≫
            (Functor.commShiftIso (integralScalarComplexFunctor l E.carrier L.carrier i
              (endpoint X Y side)) (self := eC) m).hom.app P := by
  obtain ⟨eC, hc, hs⟩ :=
    completedScalarChainShift l E.carrier L.carrier i (endpoint X Y side)
  refine ⟨eC, ?_, hs⟩
  intro P m
  simpa only [RoosShift.ConeFormula, completedScalarShiftConeFormula,
    completedScalarShiftProductIso, completedScalarShiftLevelIso,
    completedScalarChainProductIso, completedScalarRoosEndomorphism,
    RoosShift.endomorphism, RoosShift.roosFunctor, integralScalarComplexFunctor] using hc P m
end WeilConjectures.ExceptionalIntegralScalar
