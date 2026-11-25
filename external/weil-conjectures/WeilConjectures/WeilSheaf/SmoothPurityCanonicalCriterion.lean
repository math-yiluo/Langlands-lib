/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCanonicalFinite
import WeilConjectures.Tactic.ExactModProofs

/-! # Detecting integral normalization before the étale reading -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- An equality with each prescribed finite orientation gives the integral normalization. -/
theorem isIntegralSmoothOrientation_of_reduction_map_eq
    (φ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))
    (h : ∀ n : ℕ, (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 (n + 1)).map φ =
      (canonicalFiniteIntegralOrientationIso ℓ E f d (n + 1)).hom) :
    IsIntegralSmoothOrientation ℓ E f d φ := by
  intro n
  refine Eq.trans (congrArg (finiteEtaleReading ℓ E.1 (n + 1) X).map (h n)) ?_
  exact_mod_proofs (canonicalFiniteIntegralOrientationIso_map_hom ℓ E f d (n + 1))

end AlgebraicGeometry.ProEtale.CondensedRing
