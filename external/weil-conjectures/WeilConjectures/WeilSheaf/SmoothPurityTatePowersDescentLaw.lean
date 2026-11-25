/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePowersFactor
public import WeilConjectures.WeilSheaf.SmoothPurityFrobeniusFactorAlias
import WeilConjectures.Tactic.ExactModProofs

/-! # The Tate power comparison respects the geometric descent datum -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open CondensedRing

/-- The canonical Tate power pullback is equivariant for the finite-base descent datum. -/
lemma purity_upperStarTateTwistNatIso_geometricFiber
    {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]
    [NeZero (ℓ : k)] [NeZero (ℓ : AlgebraicClosure k)]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (d : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
        a.geometricGaloisFrobenius.asIso.hom).map
          (upperStarTateTwistNatIso ℓ a.geometricFiberProj a d).hom ≫
        (upperStarTateTwistNatIso ℓ a.geometricGaloisFrobenius.asIso.hom
          a.geometricFiberToAlgebraicClosure d).hom =
      (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app
          (tateTwistNat X ℓ d) ≫
        (upperStarTateTwistNatIso ℓ a.geometricFiberProj a d).hom := by
  have h := purity_upperStarTateTwistNatIso_factor ℓ a.geometricFiberProj
    a.geometricGaloisFrobenius.asIso.hom
    a.geometricGaloisFrobenius_hom_comp_geometricFiberProj a d
  rw [purity_upperStarTateTwistNatIso_independent_base ℓ a.geometricGaloisFrobenius.asIso.hom
    (a.geometricFiberProj ≫ a) a.geometricFiberToAlgebraicClosure d,
    ← purity_geometricFiberProjUpperStarFrobeniusIso_eq (Profinite.padicAlgClRingObj ℓ) a] at h
  dsimp only [Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale
