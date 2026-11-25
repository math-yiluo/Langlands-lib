/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCanonicalTateScalar
public import WeilConjectures.WeilSheaf.SmoothPurityCyclotomicScalar
public import WeilConjectures.TateTwist.TateTwistPowerDatum
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.Tactic.ExactModProofs

/-! # The canonical one-twist pair has cyclotomic Frobenius -/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] WeilSheaf.neZero_natCast_algebraicClosure

/-- The canonical geometric Tate line is the unit pair twisted by the cyclotomic
unit, with its actual root-defined Frobenius comparison. -/
theorem purity_nonempty_tateTwistOnePair_iso_unitScalar :
    Nonempty (tateTwistOnePair ℓ (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso.hom
        (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure ≅
      IsoAlgebra.unitScalarPair _
        (ProEtaleWeilSheaf.regularSmulIso k₀ ℓ X (WeilSheaf.cyclotomicUnit k₀ ℓ))) := by
  obtain ⟨ζ, hζ, hζ'⟩ := IsSepClosed.exists_isPrimitiveRoot_pow_eq (AlgebraicClosure k₀) ℓ
  let e := purityCanonicalTateOneTrivialization ℓ (X ↘ Spec (.of k₀)) hζ hζ'
  refine ⟨IsoAlgebra.isoMk e ?_⟩
  change (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso.hom).map e.hom ≫
      (Functor.OplaxMonoidal.η _ ≫
        (ProEtaleWeilSheaf.regularSmulIso k₀ ℓ X (WeilSheaf.cyclotomicUnit k₀ ℓ)).hom) =
    (upperStarTateTwistOneIso ℓ (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso.hom
      (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure).hom ≫ e.hom
  have he := purityCanonicalTateOneTrivialization_weil ℓ (X ↘ Spec (.of k₀)) hζ hζ'
  have hs := ProEtaleWeilSheaf.purity_regularSmulIso_cyclotomic_cancel k₀ ℓ X
  have h := purity_scalarDatum_inverse
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso.hom)
    (upperStarTateTwistOneIso ℓ (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso.hom
      (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure).hom
    (Functor.Monoidal.εIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.asIso.hom)).inv
    (purityCanonicalTateOneTrivialization ℓ (X ↘ Spec (.of k₀)) hζ hζ').hom
    (Nat.card k₀ : ℤ)
    (ProEtaleWeilSheaf.regularSmulIso k₀ ℓ X (WeilSheaf.cyclotomicUnit k₀ ℓ)).hom
    (by exact_mod_proofs he) hs
  dsimp only [e]
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale
