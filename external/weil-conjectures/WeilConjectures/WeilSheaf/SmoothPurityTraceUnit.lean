/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SmoothPurity.Defs

/-! # The bounded unit with its finite-base scheme specified -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- The tensor unit in the bounded constructible category over the specified base field. -/
def smoothTraceUnit : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧ := 𝟙_ _

end AlgebraicGeometry.ProEtale.CondensedRing
