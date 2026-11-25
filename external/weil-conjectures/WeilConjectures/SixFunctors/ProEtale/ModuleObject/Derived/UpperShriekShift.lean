/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!
# The exceptional inverse image on bounded constructible complexes commutes with the shifts

The exceptional inverse image `Rf^! : Dᵇc(Y)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is the right adjoint of
`Rf_!`, which commutes with the shifts. It therefore carries the unique compatible `CommShift`
structure (`CategoryTheory.Adjunction.rightAdjointCommShift`), for which the adjunction
`Rf_! ⊣ Rf^!` commutes with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

/-- The exceptional inverse image on bounded constructible complexes commutes with the shifts:
the `CommShift` structure of the right adjoint of `Rf_!`. -/
noncomputable instance : (boundedConstructibleUpperShriek ℓ f).CommShift ℤ :=
  (boundedConstructibleUpperShriekAdjunction ℓ f).rightAdjointCommShift ℤ

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes commutes with the shifts. -/
instance : (boundedConstructibleUpperShriekAdjunction ℓ f).CommShift ℤ :=
  (boundedConstructibleUpperShriekAdjunction ℓ f).commShift_of_leftAdjoint ℤ

end AlgebraicGeometry.ProEtale.CondensedRing
