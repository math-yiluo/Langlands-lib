/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-! # Naturality of single-object reconstruction

Source: Step 9 of the point-section transport argument.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- On the essential image of a fully faithful functor, reconstruction using a
retraction is natural for every arrow, including arrows unrelated to the chosen
temporary trivializations.
Source: the cycle-map naturality in Step 9 of point-section transport, refining
the twist-removal step of blueprint `theorem-poincare-duality-frobenius`.
Proof: conjugate the arrow by the two trivializations and lift it through the
fully faithful functor. Naturality of the retraction isomorphism at that lift,
followed by cancellation of the trivializations, is the asserted square.
(blueprint: lem-pod-point-single-realization-natural) -/
theorem single_realization_naturality
    {A B : Type*} [Category* A] [Category* B]
    (S : A ⥤ B) [S.Full] [S.Faithful] (H : B ⥤ A)
    (e : S ⋙ H ≅ 𝟭 A) {X Y : B} {U V : A}
    (a : X ≅ S.obj U) (b : Y ≅ S.obj V) (f : X ⟶ Y) :
    S.map (H.map f) ≫ (S.map (H.map b.hom ≫ (e.app V).hom) ≫ b.inv) =
      (S.map (H.map a.hom ≫ (e.app U).hom) ≫ a.inv) ≫ f := by
  let q := S.preimage (a.inv ≫ f ≫ b.hom)
  have hq : S.map q = a.inv ≫ f ≫ b.hom := S.map_preimage _
  have he := congrArg S.map (e.hom.naturality q)
  have he' : S.map (H.map (a.inv ≫ f ≫ b.hom)) ≫ S.map (e.hom.app V) =
      S.map (e.hom.app U) ≫ a.inv ≫ f ≫ b.hom := by
    simpa only [Functor.comp_map, Functor.id_map, hq, Functor.map_comp, Category.assoc]
      using he
  apply (cancel_mono b.hom).1
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = S.map (H.map a.hom) ≫ S.map (H.map (a.inv ≫ f ≫ b.hom)) ≫
        S.map (e.hom.app V) := by
      simp only [← S.map_comp_assoc, ← H.map_comp, Iso.hom_inv_id_assoc, Iso.app_hom]
    _ = _ := by
      rw [he']
      rfl

end AlgebraicGeometry.ProEtale.CondensedRing
