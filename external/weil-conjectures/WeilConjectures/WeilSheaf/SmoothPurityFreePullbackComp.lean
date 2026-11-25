/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreePullbackComposition
public import WeilConjectures.TateTwist.TateModuleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.Tactic.ExactModProofs

/-! # The canonical free-module pullback comparison respects composition -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical free-module comparison intertwines the two pullback compositors. -/
lemma purity_freeFunctorCompUpperStarIso_comp
    (M : Sheaf (ProEt.topology Z) Ab.{u + 1}) :
    (upperStarComp Λ f g).hom.app ((Mod.freeFunctor (condensedRingObj Λ Z)).obj M) ≫
        (upperStar Λ f).map ((freeFunctorCompUpperStarIso Λ g).hom.app M) ≫
        (freeFunctorCompUpperStarIso Λ f).hom.app ((g)^*[Ab.{u + 1}].obj M) =
      (freeFunctorCompUpperStarIso Λ (f ≫ g)).hom.app M ≫
        (Mod.freeFunctor (condensedRingObj Λ X)).map
          ((ProEtale.upperStarComp Ab.{u + 1} f g).hom.app M) := by
  apply purity_free_pullback_composition
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g)
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
    (upperStarLowerStarAdjunction Λ g)
    (upperStarLowerStarAdjunction Λ f)
    (upperStarLowerStarAdjunction Λ (f ≫ g))
    (Mod.freeForgetAdjunction (condensedRingObj Λ Z))
    (Mod.freeForgetAdjunction (condensedRingObj Λ Y))
    (Mod.freeForgetAdjunction (condensedRingObj Λ X))
    (ProEtale.upperStarComp Ab.{u + 1} f g) (upperStarComp Λ f g)
    (freeFunctorCompUpperStarIso Λ g) (freeFunctorCompUpperStarIso Λ f)
    (freeFunctorCompUpperStarIso Λ (f ≫ g))
  intro N
  rw [ProEtale.conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarComp]
  simp only [freeFunctorCompUpperStarIso, Equiv.apply_symm_apply, Iso.refl_hom,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have h := (lowerStarComp_hom_app_hom Λ f g N).symm
  dsimp only [Mod.forget, Functor.comp_obj] at h ⊢
  erw [Category.comp_id]

end AlgebraicGeometry.ProEtale.CondensedRing
