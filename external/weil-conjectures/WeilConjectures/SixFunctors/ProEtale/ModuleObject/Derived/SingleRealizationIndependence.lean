/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-! # Independence of a single-object realization

Source: Step 9 of `lem-pod-condensed-point-sections-transport`.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Reconstructing an object in the essential image of a fully faithful functor
from its image under a retraction does not depend on its temporary trivialization.
Source: the single-complex/homology comparison in Steps 8 and 9 of the point-section
transport argument, refining the twist-removal step of blueprint
`theorem-poincare-duality-frobenius`. Proof: the transition between the two trivializations is in
the image of the fully faithful functor. Naturality of the retraction isomorphism at its preimage
identifies the two reconstruction maps, after canceling the trivializations.
(blueprint: lem-pod-point-single-realization-independent) -/
theorem single_realization_independent
    {A B : Type*} [Category* A] [Category* B]
    (S : A ⥤ B) [S.Full] [S.Faithful] (H : B ⥤ A)
    (e : S ⋙ H ≅ 𝟭 A) {X : B} {U : A} (a b : X ≅ S.obj U) :
    S.map (H.map a.hom ≫ (e.app U).hom) ≫ a.inv =
      S.map (H.map b.hom ≫ (e.app U).hom) ≫ b.inv := by
  let q := S.preimage (a.inv ≫ b.hom)
  have hq : S.map q = a.inv ≫ b.hom := S.map_preimage _
  have he := congrArg S.map (e.hom.naturality q)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, hq] at he
  have he' : S.map (e.hom.app U) ≫ (a.inv ≫ b.hom) =
      S.map (H.map (a.inv ≫ b.hom)) ≫ S.map (e.hom.app U) := by
    simpa only [Functor.map_comp] using he.symm
  calc
    _ = S.map (H.map a.hom) ≫ S.map (e.hom.app U) ≫
        (a.inv ≫ b.hom) ≫ b.inv := by simp [Category.assoc]
    _ = S.map (H.map a.hom) ≫ S.map (H.map (a.inv ≫ b.hom)) ≫
        S.map (e.hom.app U) ≫ b.inv := by
      simp only [Category.assoc]
      rw [reassoc_of% he']
    _ = _ := by
      rw [← S.map_comp_assoc, ← H.map_comp, Iso.hom_inv_id_assoc]
      simp only [S.map_comp, Category.assoc, Iso.app_hom]


end AlgebraicGeometry.ProEtale.CondensedRing
