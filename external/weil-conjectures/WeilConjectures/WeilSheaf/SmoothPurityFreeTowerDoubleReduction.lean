/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeTowerReduction
public import WeilConjectures.WeilSheaf.SmoothPurityTateCoefficientComposition

/-! # Finite projection after two coefficient changes -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

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
  {Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
  (c : Λ ⟶ Λ'') [IsMonHom c] (hc : a ≫ b = c)

set_option hygiene false in
local notation "𝒯" => Functor.ofOpSequence
  (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
  (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n))
set_option hygiene false in
local notation "𝒯'" => Functor.ofOpSequence
  (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
  (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n))

/-- The finite projection from a tower extended first to an integral coefficient ring
and then to a finite coefficient ring has the canonical geometric pullback datum. -/
lemma upperStarExtendScalarsLimitFreeTowerIso_hom_comp_doubleProjection (n : ℕ) :
    (pullIso b g).inv.app ((Mod.extendScalars (coefficientMap a X)).obj (limit 𝒯)) ≫
        (Mod.extendScalars (coefficientMap b X')).map
          (upperStarExtendScalarsLimitFreeTowerIso Λ g t t' e a he hK).hom ≫
        (Mod.extendScalarsCompIsoOfEq (coefficientMap_comp_eq a b c hc X')).hom.app (limit 𝒯') ≫
        purityFreeTowerProjection Λ t' c n =
      (CondensedRing.upperStar Λ'' g).map
          ((Mod.extendScalarsCompIsoOfEq (coefficientMap_comp_eq a b c hc X)).hom.app (limit 𝒯) ≫
            purityFreeTowerProjection Λ t c n) ≫
        (upperStarFreeTowerIsoApp Λ'' g e n).hom := by
  let τ := upperStarLimitFreeTowerIso Λ g t t' e he hK
  have h := purityCoefficientPullbackIso_comp a b c g hc τ
  have hp : (purityCoefficientPullbackIso c g τ).hom ≫ purityFreeTowerProjection Λ t' c n =
      (CondensedRing.upperStar Λ'' g).map (purityFreeTowerProjection Λ t c n) ≫
        (upperStarFreeTowerIsoApp Λ'' g e n).hom :=
    upperStarExtendScalarsLimitFreeTowerIso_hom_comp_projection Λ g t t' e he hK c n
  have h' := congrArg (· ≫ purityFreeTowerProjection Λ t' c n) h
  simp only [Category.assoc] at h'
  rw [hp] at h'
  simpa only [purityCoefficientPullbackIso, upperStarExtendScalarsLimitFreeTowerIso, τ,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] using h'

end AlgebraicGeometry.ProEtale
