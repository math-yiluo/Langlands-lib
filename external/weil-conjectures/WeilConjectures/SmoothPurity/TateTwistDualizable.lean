/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.TateTwistPullback
public import WeilConjectures.TraceFormula.DualizableShift
public import WeilConjectures.TateTwist.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeDualizable

/-!

# The shifted Tate twists are dualizable

For a separated `k`-scheme of finite type `X`, the shifted Tate twist `ℚ̄_ℓ,X(d)[n]` is a
dualizable object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (blueprint `definition-tate-twists` (3),
subsection `proposition-purity-vector-bundles`): `ℚ̄_ℓ,X(d)` is locally free of rank one, and shifts
of dualizable objects are dualizable.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

variable (X) in
/-- **The Tate twists are invertible** (blueprint `definition-tate-twists` (3),
subsection `proposition-purity-vector-bundles`: "for `Λ ∈ {A, 𝒪_E, E, ℚ̄_ℓ}` the sheaf `Λ_X(1)` is
an invertible `Λ_X`-module [...] hence so are `Λ_X(d)` and `Λ_X(-d)`"): the Tate twist `ℚ̄_ℓ,X(d)`,
placed in degree `0`, is a dualizable bounded constructible complex. -/
theorem isDualizable_boundedConstructibleTateTwist (d : ℤ) :
    IsDualizable (boundedConstructibleTateTwist ℓ X d 0) := by
  have := neZero_natCast_of_ringChar_ne ℓ (k := k)
  refine (isDualizable_singleFunctor_of_isLocallyFree ℓ X (tateTwist X.left ℓ d)
    (isLocallyFree_tateTwist ℓ X.hom d)).of_iso
    ((boundedConstructible _).fullyFaithfulι.preimageIso ?_)
  exact ((shiftFunctorZero _ ℤ).app (tateTwistDerived X.left ℓ d)).symm

variable (X) in
/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]` is the shift of `ℚ̄_ℓ,X(d)` in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def boundedConstructibleTateTwistShiftIso (d n : ℤ) :
    boundedConstructibleTateTwist ℓ X d n ≅
      (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) n).obj
        (boundedConstructibleTateTwist ℓ X d 0) :=
  (boundedConstructible _).fullyFaithfulι.preimageIso
    ((shiftFunctor _ n).mapIso ((shiftFunctorZero _ ℤ).app _).symm ≪≫
      (((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
        |>.commShiftIso n).app (boundedConstructibleTateTwist ℓ X d 0)).symm)

/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]` is dualizable. -/
theorem isDualizable_boundedConstructibleTateTwist_shift (d n : ℤ) :
    IsDualizable (boundedConstructibleTateTwist ℓ X d n) :=
  (IsDualizable.shift ℓ (isDualizable_boundedConstructibleTateTwist ℓ X d) n).of_iso
    (boundedConstructibleTateTwistShiftIso ℓ X d n).symm

end AlgebraicGeometry.ProEtale.CondensedRing
