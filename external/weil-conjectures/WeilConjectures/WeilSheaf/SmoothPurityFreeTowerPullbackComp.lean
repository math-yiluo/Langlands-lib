/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeLevelComposition
public import WeilConjectures.WeilSheaf.SmoothPurityLimitPullbackComposition
public import WeilConjectures.WeilSheaf.SmoothPurityTateTowerProjection

/-! # Composition compatibility of the canonical pullback of a free tower limit -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  {F : ℕ → Sheaf (ProEt.topology Z) Ab.{u + 1}} (tF : ∀ n, F (n + 1) ⟶ F n)
  {G : ℕ → Sheaf (ProEt.topology Y) Ab.{u + 1}} (tG : ∀ n, G (n + 1) ⟶ G n)
  {H : ℕ → Sheaf (ProEt.topology X) Ab.{u + 1}} (tH : ∀ n, H (n + 1) ⟶ H n)
  (e : ∀ n, (g)^*[Ab.{u + 1}].obj (F n) ≅ G n)
  (e' : ∀ n, (f)^*[Ab.{u + 1}].obj (G n) ≅ H n)
  (e'' : ∀ n, (f ≫ g)^*[Ab.{u + 1}].obj (F n) ≅ H n)
  (he : ∀ n, (g)^*[Ab.{u + 1}].map (tF n) ≫ (e n).hom = (e (n + 1)).hom ≫ tG n)
  (he' : ∀ n, (f)^*[Ab.{u + 1}].map (tG n) ≫ (e' n).hom = (e' (n + 1)).hom ≫ tH n)
  (he'' : ∀ n, (f ≫ g)^*[Ab.{u + 1}].map (tF n) ≫ (e'' n).hom =
    (e'' (n + 1)).hom ≫ tH n)

set_option hygiene false in
local notation "TF" => Functor.ofOpSequence
  (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ Z)).obj (F n))
  (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ Z)).map (tF n))
set_option hygiene false in
local notation "TG" => Functor.ofOpSequence
  (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ Y)).obj (G n))
  (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ Y)).map (tG n))
set_option hygiene false in
local notation "TH" => Functor.ofOpSequence
  (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (H n))
  (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (tH n))

variable
  (hP : PreservesLimit (TF ⋙ Mod.forget _) (g)^*[Ab.{u + 1}])
  (hQ : PreservesLimit (TG ⋙ Mod.forget _) (f)^*[Ab.{u + 1}])
  (hR : PreservesLimit (TF ⋙ Mod.forget _) (f ≫ g)^*[Ab.{u + 1}])

/-- The root-level cocycle passes to the canonical pullback of its free-module limit. -/
lemma purity_upperStarLimitFreeTowerIso_comp
    (hw : ∀ n, (ProEtale.upperStarComp Ab.{u + 1} f g).hom.app (F n) ≫
      (f)^*[Ab.{u + 1}].map (e n).hom ≫ (e' n).hom = (e'' n).hom) :
    (CondensedRing.upperStarComp Λ f g).hom.app (limit TF) ≫
        (CondensedRing.upperStar Λ f).map (upperStarLimitFreeTowerIso Λ g tF tG e he hP).hom ≫
        (upperStarLimitFreeTowerIso Λ f tG tH e' he' hQ).hom =
      (upperStarLimitFreeTowerIso Λ (f ≫ g) tF tH e'' he'' hR).hom := by
  apply purity_limit_pullback_composition TF TG TH
    (CondensedRing.upperStar Λ g) (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ (f ≫ g))
    (CondensedRing.upperStarComp Λ f g)
    (upperStarFreeTowerHom Λ g tF tG e he)
    (upperStarFreeTowerHom Λ f tG tH e' he')
    (upperStarFreeTowerHom Λ (f ≫ g) tF tH e'' he'')
  · intro i
    exact upperStarLimitFreeTowerIso_hom_comp_π Λ g tF tG e he hP i.unop
  · intro i
    exact upperStarLimitFreeTowerIso_hom_comp_π Λ f tG tH e' he' hQ i.unop
  · intro i
    exact upperStarLimitFreeTowerIso_hom_comp_π Λ (f ≫ g) tF tH e'' he'' hR i.unop
  · intro i
    exact purity_upperStarFreeTowerIsoApp_comp Λ f g e e' e'' i.unop (hw i.unop)

end AlgebraicGeometry.ProEtale
