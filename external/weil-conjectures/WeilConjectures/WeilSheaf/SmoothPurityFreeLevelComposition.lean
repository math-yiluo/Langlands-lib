/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreePullbackComp

/-! # Composition of the free-module comparisons at a Tate tower level -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  {F : ℕ → Sheaf (ProEt.topology Z) Ab.{u + 1}}
  {G : ℕ → Sheaf (ProEt.topology Y) Ab.{u + 1}}
  {H : ℕ → Sheaf (ProEt.topology X) Ab.{u + 1}}
  (e : ∀ n, (g)^*[Ab.{u + 1}].obj (F n) ≅ G n)
  (e' : ∀ n, (f)^*[Ab.{u + 1}].obj (G n) ≅ H n)
  (e'' : ∀ n, (f ≫ g)^*[Ab.{u + 1}].obj (F n) ≅ H n)

/-- Root-level composition compatibility passes through the free-module functor. -/
lemma purity_upperStarFreeTowerIsoApp_comp (n : ℕ)
    (h : (ProEtale.upperStarComp Ab.{u + 1} f g).hom.app (F n) ≫
        (f)^*[Ab.{u + 1}].map (e n).hom ≫ (e' n).hom = (e'' n).hom) :
    (CondensedRing.upperStarComp Λ f g).hom.app
          ((Mod.freeFunctor (condensedRingObj Λ Z)).obj (F n)) ≫
        (CondensedRing.upperStar Λ f).map (upperStarFreeTowerIsoApp Λ g e n).hom ≫
        (upperStarFreeTowerIsoApp Λ f e' n).hom =
      (upperStarFreeTowerIsoApp Λ (f ≫ g) e'' n).hom := by
  have hn := (freeFunctorCompUpperStarIso Λ f).hom.naturality (e n).hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [upperStarFreeTowerIsoApp, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [reassoc_of% (purity_freeFunctorCompUpperStarIso_comp Λ f g (F n))]
  rw [← Functor.map_comp, ← Functor.map_comp, h]

end AlgebraicGeometry.ProEtale
