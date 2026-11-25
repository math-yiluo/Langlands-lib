/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.CondensedTwistedConstant

/-! # Forward factorization compatibility of pullback and forgetting coefficients -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory

/-- Turn the inverse form of a square into the forward form. -/
lemma purity_forward_square_of_inverse {C : Type*} [Category C]
    {A B A' B' : C} (a : A ≅ B) (b : A' ≅ B')
    (u : A ⟶ A') (v : B ⟶ B') (h : v ≫ b.inv = a.inv ≫ u) :
    u ≫ b.hom = a.hom ≫ v := by
  apply (cancel_mono b.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, h,
    Iso.hom_inv_id_assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}}
  (p : U ⟶ X) (s : U ⟶ U) (hs : s ≫ p = p)

/-- The forward form of the pullback-forget factorization square. -/
lemma purity_upperStarForgetIso_factor_hom
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((s)^*[Ab.{u + 1}].map ((upperStarForgetIso Λ p).hom.app M) ≫
        (upperStarForgetIso Λ s).hom.app ((p)^*⟦Λ⟧.obj M)) ≫
        (Mod.forget _).map
          (((upperStarComp Λ s p).symm ≪≫ upperStarCongr Λ hs).hom.app M) =
      (ProEtale.upperStarComp' Ab.{u + 1} s p p hs.symm).symm.hom.app M.X ≫
        (upperStarForgetIso Λ p).hom.app M := by
  have h := upperStarForgetIso_hom_app_map_upperStarComp_symm_trans_inv_app Λ p hs M
  have h' := purity_forward_square_of_inverse
    ((ProEtale.upperStarComp' Ab.{u + 1} s p p hs.symm).symm.app M.X)
    ((Mod.forget _).mapIso (((upperStarComp Λ s p).symm ≪≫ upperStarCongr Λ hs).app M))
    ((s)^*[Ab.{u + 1}].map ((upperStarForgetIso Λ p).hom.app M) ≫
      (upperStarForgetIso Λ s).hom.app ((p)^*⟦Λ⟧.obj M))
    ((upperStarForgetIso Λ p).hom.app M)
    (by
      simp only [Functor.mapIso_inv, Iso.app_inv, Functor.comp_obj] at h ⊢
      dsimp only [Mod.forget] at h ⊢
      exact h)
  exact h'

end AlgebraicGeometry.ProEtale.CondensedRing
