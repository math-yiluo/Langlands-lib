/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.TateTwist.TateModuleUpperStar

/-! # Geometric pullback and the projections of the Tate tower

These equations are kept at arbitrary condensed coefficients. They give the projection
compatibility needed when comparing integral Tate data with their finite reductions.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (g : X' ⟶ X)
  {F : ℕ → Sheaf (ProEt.topology X) Ab.{u + 1}} (t : ∀ n, F (n + 1) ⟶ F n)
  {F' : ℕ → Sheaf (ProEt.topology X') Ab.{u + 1}} (t' : ∀ n, F' (n + 1) ⟶ F' n)
  (e : ∀ n, (g)^*[Ab.{u + 1}].obj (F n) ≅ F' n)
  (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n)
  (hK : PreservesLimit (Functor.ofOpSequence
    (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
    (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ⋙ Mod.forget _)
    (g)^*[Ab.{u + 1}])

set_option hygiene false in
local notation "𝒯" => Functor.ofOpSequence
  (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
  (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n))
set_option hygiene false in
local notation "𝒯'" => Functor.ofOpSequence
  (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
  (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n))

/-- The canonical comparison of limits intertwines every projection with the
corresponding comparison of free modules. -/
@[reassoc]
lemma upperStarLimitFreeTowerIso_hom_comp_π (n : ℕ) :
    (upperStarLimitFreeTowerIso Λ g t t' e he hK).hom ≫ limit.π 𝒯' (op n) =
      (CondensedRing.upperStar Λ g).map (limit.π 𝒯 (op n)) ≫
        (upperStarFreeTowerIsoApp Λ g e n).hom := by
  have := hK
  have := CondensedRing.preservesLimit_upperStar Λ g 𝒯
  simp only [upperStarLimitFreeTowerIso, Iso.trans_hom, Category.assoc,
    HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π_assoc,
    upperStarFreeTowerIso, asIso_hom, upperStarFreeTowerHom, NatTrans.ofOpSequence_app]

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The same projection equation after coefficient extension. In particular it applies
to the finite quotients used to define the integral Tate reductions. -/
@[reassoc]
lemma upperStarExtendScalarsLimitFreeTowerIso_hom_comp_map_π (n : ℕ) :
    (upperStarExtendScalarsLimitFreeTowerIso Λ g t t' e a he hK).hom ≫
        (Mod.extendScalars (coefficientMap a X')).map (limit.π 𝒯' (op n)) =
      (CondensedRing.upperStar Λ' g).map
          ((Mod.extendScalars (coefficientMap a X)).map (limit.π 𝒯 (op n))) ≫
        (CondensedRing.pullIso a g).inv.app ((𝒯).obj (op n)) ≫
        (Mod.extendScalars (coefficientMap a X')).map
          (upperStarFreeTowerIsoApp Λ g e n).hom := by
  have hn := (CondensedRing.pullIso a g).inv.naturality (limit.π 𝒯 (op n))
  dsimp only [Functor.comp_map] at hn
  simp only [upperStarExtendScalarsLimitFreeTowerIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp, upperStarLimitFreeTowerIso_hom_comp_π,
    Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]

end AlgebraicGeometry.ProEtale
