/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Localization restriction and restriction of scalars

Restriction `j_f^*` along a weakly étale `f : V ⟶ U` commutes strictly with restriction of
scalars along a ring map `q : R →+* S`. The mate of this strict square along the adjunctions
`j_f^* ⊣ f_*` is the identity, since the unit of `j_f^* ⊣ f_*` is computed in the same way for
both coefficient rings.

Source: Stacks Project, Tags 03DA and 0960.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : WeaklyEtale f)
  {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)

/-- The strict square: restricting scalars commutes with the localization restriction. -/
def localizationRestrictionRestrictScalarsSquare :
    TwoSquare (sheafCompose (Scheme.ProEt.topology U) (ModuleCat.restrictScalars.{u + 1} q))
      (localizationRestriction (ModuleCat.{u + 1} S) f h)
      (localizationRestriction (ModuleCat.{u + 1} R) f h)
      (sheafCompose (Scheme.ProEt.topology V) (ModuleCat.restrictScalars.{u + 1} q)) :=
  𝟙 _

/-- The unit of `j_f^* ⊣ f_*` commutes with restriction of scalars. -/
theorem localizationRestrictionLowerStarAdjunction_unit_restrictScalars
    (Y : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} S)) :
    (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} R) f h).unit.app
      ((sheafCompose (Scheme.ProEt.topology U) (ModuleCat.restrictScalars.{u + 1} q)).obj Y) =
    (sheafCompose (Scheme.ProEt.topology U) (ModuleCat.restrictScalars.{u + 1} q)).map
      ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} S) f h).unit.app Y) :=
  rfl

/-- The mate of the strict square along `j_f^* ⊣ f_*` is the identity.
Proof: its component is the image under restriction of scalars of the unit at `f_* F`
followed by `f_*` of the counit, which is the identity by a triangle identity. -/
theorem localizationRestrictionRestrictScalarsSquare_mate_app
    (F : Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} S)) :
    (mateEquiv (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} S) f h)
      (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} R) f h)
      (localizationRestrictionRestrictScalarsSquare f h q)).app F = 𝟙 _ := by
  simp only [Functor.comp_obj, mateEquiv_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    localizationRestrictionRestrictScalarsSquare, NatTrans.id_app]
  rw [localizationRestrictionLowerStarAdjunction_unit_restrictScalars]
  exact ((sheafCompose _ _).map_comp _ _).symm.trans ((congrArg _
    ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} S) f
      h).right_triangle_components F)).trans ((sheafCompose _ _).map_id _))

instance localizationRestrictionRestrictScalarsSquare_mate_isIso :
    IsIso (mateEquiv (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} S) f h)
      (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} R) f h)
      (localizationRestrictionRestrictScalarsSquare f h q)) := by
  have (F : Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} S)) :
      IsIso ((mateEquiv (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} S) f h)
        (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} R) f h)
        (localizationRestrictionRestrictScalarsSquare f h q)).app F) := by
    rw [localizationRestrictionRestrictScalarsSquare_mate_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.ProEtale
