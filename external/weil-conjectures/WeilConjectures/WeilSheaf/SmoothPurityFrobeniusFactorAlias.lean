/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarComparison
public import WeilConjectures.WeilSheaf.SmoothPurityWhiskerComponent
import WeilConjectures.Tactic.ExactModProofs

/-! # The descent Frobenius factor in the abstract factorization notation -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Identify the factor isomorphisms before taking their components. -/
lemma purity_geometricFiberProjUpperStarFrobeniusIso_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) :
    geometricFiberProjUpperStarFrobeniusIso Λ a =
      purityModuleFactorIso Λ a.geometricFiberProj a.geometricGaloisFrobenius.asIso.hom
        a.geometricGaloisFrobenius_hom_comp_geometricFiberProj := rfl

/-- The pushforward convention is obtained by transporting the pullback datum. -/
lemma purity_geometricFiberProjLowerStarFrobeniusIso_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
    (geometricFiberProjLowerStarFrobeniusIso Λ a).app M =
      ((upperStarIsoLowerStarInv Λ a.geometricGaloisFrobenius.asIso).app
        ((CondensedRing.upperStar Λ a.geometricFiberProj).obj M)).symm ≪≫
        (geometricFiberProjUpperStarFrobeniusIso Λ a).app M := by
  have h := purity_isoWhiskerLeft_symm_trans_app
    (CondensedRing.upperStar Λ a.geometricFiberProj)
    (upperStarIsoLowerStarInv Λ a.geometricGaloisFrobenius.asIso)
    (geometricFiberProjUpperStarFrobeniusIso Λ a)
    (geometricFiberProjLowerStarFrobeniusIso Λ a) rfl M
  dsimp only [Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale.CondensedRing
