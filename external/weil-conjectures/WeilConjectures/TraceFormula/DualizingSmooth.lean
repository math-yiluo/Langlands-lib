/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.TraceFormula.Dualizing

/-!

# Smooth purity for the dualizing complex

For `X` smooth of pure dimension `d` over the base point `s = Spec k`, the dualizing complex
`ω_X = Ra_X^! ℚ̄_ℓ` is the shifted Tate twist `ℚ̄_ℓ,X(d)[2d]`
(`ProEtale.CondensedRing.dualizingComplexSmoothIso`): smooth purity
(`ProEtale.CondensedRing.smoothPurityIso`) for the structure morphism `a_X`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Smooth purity for the dualizing complex**: for `X` smooth of pure dimension `d` over `s`,
`ω_X ≅ ℚ̄_ℓ,X(d)[2d]`, after the inclusion `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`. This is
`ProEtale.CondensedRing.smoothPurityIso` for the structure morphism `a_X`. -/
noncomputable def dualizingComplexSmoothIso (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    (dualizingComplex' ℓ X).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  haveI : SmoothOfRelativeDimension d (toPoint X).left := by
    rw [toPoint_left]
    infer_instance
  smoothPurityIso ℓ (toPoint X) d

end AlgebraicGeometry.ProEtale.CondensedRing
