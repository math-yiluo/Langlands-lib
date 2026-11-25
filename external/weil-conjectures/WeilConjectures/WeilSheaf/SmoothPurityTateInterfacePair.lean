/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePullbackInterface
public import WeilConjectures.WeilSheaf.SmoothPurityPairTransport

/-! # Tate pair transport through the module interface -/

@[expose] public section

universe u

open CategoryTheory Endofunctor
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The descent comparison, using only the published Frobenius interface. -/
noncomputable def purity_geometricTateInterfacePairIso
    {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]
    [NeZero (ℓ : k)] [NeZero (ℓ : AlgebraicClosure k)]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (d : ℕ) :
    (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ) a).obj
        (tateTwistNat X ℓ d) ≅ purityTateRootPair ℓ a d := by
  let e := purity_pairIso_transport (purityTateFrobeniusCompare ℓ a)
    (purityTatePulledDatum ℓ a d) (purityTateRootDatum ℓ a d)
    ((geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).app
      (tateTwistNat X ℓ d))
    (((purityTateFrobeniusCompare ℓ a).app _).symm ≪≫ purityTateRootDatum ℓ a d)
    (purityTatePulledDatum_transport ℓ a d) rfl
    (upperStarTateTwistNatIso ℓ a.geometricFiberProj a d)
    (purityTateRootDatum_pullback ℓ a d)
  exact e ≪≫ eqToIso (purityTateRootPair_def ℓ a d).symm

end AlgebraicGeometry.ProEtale.CondensedRing
