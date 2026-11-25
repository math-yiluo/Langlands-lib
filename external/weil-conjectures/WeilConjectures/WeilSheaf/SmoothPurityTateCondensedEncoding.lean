/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTateOnePair
public import WeilConjectures.WeilSheaf.SmoothPurityConstantWeilDatum
public import WeilConjectures.WeilSheaf.SmoothPurityTatePullbackInterface
public import WeilConjectures.WeilSheaf.TateTwistCondensedBridge
import WeilConjectures.Tactic.ExactModProofs

/-! # The canonical geometric Tate datum in the condensed Weil model -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilSheaf

open ProEtale ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

local instance instNeZeroCast_smoothPurityTateCondensedEncoding : NeZero (ℓ : k₀) := ⟨by
  rw [Ne, ringChar.spec, Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k₀ _) Fact.out]
  exact Fact.out⟩
attribute [local instance] neZero_natCast_algebraicClosure

/-- The root-defined geometric Tate datum agrees with the native cyclotomic twist
in every nonnegative degree. -/
theorem purity_nonempty_tateRootPair_iso_toCondensed_constantTwist (d : ℕ) :
    Nonempty (CondensedRing.purityTateRootPair ℓ (X ↘ Spec (.of k₀)) d ≅
      (toCondensed k₀ ℓ X).obj
        ((ProEtaleWeilSheaf.constantTwist k₀ ℓ X (cyclotomicUnit k₀ ℓ ^ d)).obj
          (ProEtaleWeilSheaf.adicConstant k₀ ℓ X))) := by
  obtain ⟨e₁⟩ := purity_nonempty_tateTwistOnePair_iso_unitScalar k₀ ℓ X
  obtain ⟨ê, hê⟩ := exists_iso_tateTwistNat_of_one ℓ
    (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso.hom
    (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure _ e₁ d
  refine ⟨eqToIso (CondensedRing.purityTateRootPair_eq ℓ (X ↘ Spec (.of k₀)) d) ≪≫
    ?_ ≪≫ (toCondensedObjConstantTwistAdicConstantIso k₀ ℓ X _).symm⟩
  exact IsoAlgebra.isoMkOfConj
    (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso)
    (upperStarTateTwistNatIso ℓ (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso.hom
      (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure d)
    (tateUnitDatum ℓ (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso.hom)
    (IsoAlgebra.scalarPow (regularSmulIso k₀ ℓ X (cyclotomicUnit k₀ ℓ)) d).hom
    (adicConstantCondensedStr k₀ ℓ X) (regularSmulIso k₀ ℓ X (cyclotomicUnit k₀ ℓ ^ d))
    ê hê (purity_adicConstantCondensedStr_hom k₀ ℓ X)
    (scalarPow_regularSmulIso_hom k₀ ℓ X (cyclotomicUnit k₀ ℓ) d).symm

end AlgebraicGeometry.WeilSheaf
