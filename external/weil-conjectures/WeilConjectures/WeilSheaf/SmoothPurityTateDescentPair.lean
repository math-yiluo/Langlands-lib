/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTateInterfacePair
public import WeilConjectures.WeilSheaf.FrobeniusTwist

/-! # The Tate datum from finite-base descent is the canonical root datum -/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilSheaf

open ProEtale ProEtaleWeilSheaf CondensedRing

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

local instance instNeZeroCast_smoothPurityTateDescentPair : NeZero (ℓ : k₀) := ⟨by
  rw [Ne, ringChar.spec, Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k₀ _) Fact.out]
  exact Fact.out⟩
attribute [local instance] neZero_natCast_algebraicClosure

/-- The pullback comparison of the Tate powers is an isomorphism of condensed Weil pairs. -/
noncomputable def purity_geometricFiberWeilLowerStarTateRootIso (d : ℕ) :
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ)
        (X ↘ Spec (.of k₀))).obj (tateTwistNat X ℓ d) ≅
      purityTateRootPair ℓ (X ↘ Spec (.of k₀)) d :=
  purity_geometricTateInterfacePairIso ℓ (X ↘ Spec (.of k₀)) d

end AlgebraicGeometry.WeilSheaf
