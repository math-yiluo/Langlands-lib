/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePowersDescentLaw
import WeilConjectures.Tactic.ExactModProofs

/-! # A module interface for geometric Tate pullback

Named whole-functor and whole-isomorphism equations organize the Tate pullback
comparison. The definitions remain transparent across module boundaries.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]
  {X : Scheme.{u}} (a : X ⟶ Spec (.of k))

/-- The named geometric Frobenius pullback used in the comparison equations. -/
noncomputable def purityTateFrobeniusPull :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology a.geometricFiber) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) a.geometricFiber) ⥤
      CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology a.geometricFiber) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) a.geometricFiber) :=
  upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.asIso.hom

lemma purityTateFrobeniusPull_eq :
    purityTateFrobeniusPull ℓ a =
      upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.asIso.hom := (rfl)

/-- The comparison of the two Frobenius conventions in the module interface. -/
noncomputable def purityTateFrobeniusCompare :
    purityTateFrobeniusPull ℓ a ≅
      lowerStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.asIso.inv :=
  upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.asIso

/-- The descent datum on the pulled-back Tate power. -/
noncomputable def purityTatePulledDatum (d : ℕ) :
    (purityTateFrobeniusPull ℓ a).obj
        ((upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricFiberProj).obj
          (tateTwistNat X ℓ d)) ≅
      (upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricFiberProj).obj
        (tateTwistNat X ℓ d) :=
  (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).app
    (tateTwistNat X ℓ d)

lemma purityTatePulledDatum_transport (d : ℕ) :
    (geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).app
        (tateTwistNat X ℓ d) =
      ((purityTateFrobeniusCompare ℓ a).app _).symm ≪≫ purityTatePulledDatum ℓ a d := by
  dsimp only [purityTateFrobeniusCompare, purityTatePulledDatum, purityTateFrobeniusPull]
  exact purity_geometricFiberProjLowerStarFrobeniusIso_app
    (Profinite.padicAlgClRingObj ℓ) a (tateTwistNat X ℓ d)

variable [NeZero (ℓ : k)] [NeZero (ℓ : AlgebraicClosure k)]

/-- The root-defined Tate datum, expressed using the module interface. -/
noncomputable def purityTateRootDatum (d : ℕ) :
    (purityTateFrobeniusPull ℓ a).obj (tateTwistNat a.geometricFiber ℓ d) ≅
      tateTwistNat a.geometricFiber ℓ d :=
  upperStarTateTwistNatIso ℓ a.geometricGaloisFrobenius.asIso.hom
    a.geometricFiberToAlgebraicClosure d

lemma purityTateRootDatum_pullback (d : ℕ) :
    (purityTateFrobeniusPull ℓ a).map
        (upperStarTateTwistNatIso ℓ a.geometricFiberProj a d).hom ≫
      (purityTateRootDatum ℓ a d).hom =
    (purityTatePulledDatum ℓ a d).hom ≫
      (upperStarTateTwistNatIso ℓ a.geometricFiberProj a d).hom := by
  have h := purity_upperStarTateTwistNatIso_geometricFiber ℓ a d
  dsimp only [purityTateFrobeniusPull, purityTateRootDatum, purityTatePulledDatum,
    Iso.app_hom, Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

/-- The root pair in the inverse-Frobenius pushforward convention. -/
noncomputable def purityTateRootPair (d : ℕ) :
    IsoAlgebra (lowerStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.asIso.inv) :=
  IsoAlgebra.mk (tateTwistNat a.geometricFiber ℓ d)
    (((purityTateFrobeniusCompare ℓ a).app _).symm ≪≫ purityTateRootDatum ℓ a d)

omit [NeZero (ℓ : k)] in
lemma purityTateRootPair_def (d : ℕ) :
    purityTateRootPair ℓ a d =
      IsoAlgebra.mk (tateTwistNat a.geometricFiber ℓ d)
        (((purityTateFrobeniusCompare ℓ a).app _).symm ≪≫ purityTateRootDatum ℓ a d) := (rfl)

omit [NeZero (ℓ : k)] in
lemma purityTateRootPair_eq (d : ℕ) :
    purityTateRootPair ℓ a d =
      IsoAlgebra.mk (tateTwistNat a.geometricFiber ℓ d)
        (((upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj ℓ)
          a.geometricGaloisFrobenius.asIso).app _).symm ≪≫
          upperStarTateTwistNatIso ℓ a.geometricGaloisFrobenius.asIso.hom
            a.geometricFiberToAlgebraicClosure d) := (rfl)

end AlgebraicGeometry.ProEtale.CondensedRing
