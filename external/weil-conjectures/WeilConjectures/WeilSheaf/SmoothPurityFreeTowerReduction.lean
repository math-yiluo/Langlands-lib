/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeCoefficientPull
public import WeilConjectures.WeilSheaf.SmoothPurityTateTowerProjection

/-! # Geometric compatibility of finite free-tower projections -/

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
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The projection of a free-module tower after coefficient extension, using the
canonical comparison of the extended free module with the free module. -/
noncomputable def purityFreeTowerProjection (n : ℕ) :=
  (Mod.extendScalars (coefficientMap a X)).map
      (limit.π (Functor.ofOpSequence
        (X := fun m ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F m))
        (fun m ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t m))) (op n)) ≫
    (Mod.freeFunctorCompExtendScalarsIso (coefficientMap a X)).hom.app (F n)

/-- The projection after coefficient extension intertwines the canonical geometric
datum of the limit with the canonical datum of the finite free module. -/
lemma upperStarExtendScalarsLimitFreeTowerIso_hom_comp_projection (n : ℕ) :
    (upperStarExtendScalarsLimitFreeTowerIso Λ g t t' e a he hK).hom ≫
        purityFreeTowerProjection Λ t' a n =
      (CondensedRing.upperStar Λ' g).map (purityFreeTowerProjection Λ t a n) ≫
        (upperStarFreeTowerIsoApp Λ' g e n).hom := by
  have hn := (Mod.freeFunctorCompExtendScalarsIso (coefficientMap a X')).hom.naturality
    (e n).hom
  dsimp only [Functor.comp_map] at hn
  have hp := CondensedRing.pullIso_hom_app_free_comp a g (F n)
  simp only [purityFreeTowerProjection, Functor.map_comp, Category.assoc]
  rw [upperStarExtendScalarsLimitFreeTowerIso_hom_comp_map_π_assoc]
  simp only [upperStarFreeTowerIsoApp, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  erw [hn, reassoc_of% hp, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.ProEtale
