/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Adjusting an adjunction coordinate on its coefficient unit

Source: diagonal-tower trace (1), finite coefficient identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory

private theorem extendUnitAutomorphism {D : Type*} [Category D] [MonoidalCategory D]
    (V : D) (j : V ≅ 𝟙_ D) (d : V ≅ V) :
    ∃ α : 𝟭 D ≅ 𝟭 D, α.hom.app V = d.hom := by
  let e := j.symm ≪≫ d ≪≫ j
  let α := (leftUnitorNatIso D).symm ≪≫ (curriedTensor D).mapIso e ≪≫
    leftUnitorNatIso D
  have hunit : α.hom.app (𝟙_ D) = e.hom := by
    change (λ_ (𝟙_ D)).inv ≫ (e.hom ▷ (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom = _
    rw [unitors_equal, rightUnitor_naturality, ← Category.assoc,
      ← unitors_equal, Iso.inv_hom_id, Category.id_comp]
  refine ⟨α, ?_⟩
  apply (cancel_mono j.hom).mp
  have h := α.hom.naturality j.hom
  change j.hom ≫ α.hom.app (𝟙_ D) = α.hom.app V ≫ j.hom at h
  rw [← h, hunit]
  simp only [e, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- An equivalence from a monoidal category allows any chosen isomorphism on
one tensor-unit object to be incorporated into a natural comparison.

Source: diagonal-tower trace (1), choice of coefficient/adjunction coordinates
(blueprint: lem-sfb-finite-p1-unit-adjustment).
Proof: lift the discrepancy on H(V) through the fully faithful functor H.
Transport V to the tensor unit, tensor its automorphism with every object,
and conjugate by the left unitors. At the unit this is the original
endomorphism by equality of the two unitors. Conjugate back to V and whisker
with H and P. Naturality at i gives the prescribed component equation. -/
theorem finiteP1_adjust_coordinate_unit
    {C D E : Type*} [Category C] [Category D] [Category E] [MonoidalCategory D]
    (K : C ⥤ E) (P : C ⥤ D) (H : D ⥤ E) [H.IsEquivalence]
    (p0 : K ≅ P ⋙ H) (U : C) (V : D) (j : V ≅ 𝟙_ D)
    (i : P.obj U ≅ V) (u : K.obj U ≅ H.obj V) :
    ∃ p : K ≅ P ⋙ H, p.hom.app U ≫ H.map i.hom = u.hom := by
  let d := H.preimageIso ((p0.app U ≪≫ H.mapIso i).symm ≪≫ u)
  obtain ⟨α, hα⟩ := extendUnitAutomorphism V j d
  let z : H ≅ H := H.leftUnitor.symm ≪≫ Functor.isoWhiskerRight α H ≪≫ H.leftUnitor
  have hz : z.hom.app V = H.map d.hom := by
    change 𝟙 _ ≫ H.map (α.hom.app V) ≫ 𝟙 _ = _
    rw [hα, Category.id_comp, Category.comp_id]
  refine ⟨p0 ≪≫ Functor.isoWhiskerLeft P z, ?_⟩
  change (p0.hom.app U ≫ z.hom.app (P.obj U)) ≫ H.map i.hom = _
  calc
    _ = p0.hom.app U ≫ H.map i.hom ≫ z.hom.app V := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ p0.hom.app U ≫ k) (z.hom.naturality i.hom).symm
    _ = u.hom := by
      rw [hz]
      simp only [d, Functor.preimageIso_hom, Functor.map_preimage,
        Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_inv,
        Functor.mapIso_inv, Category.assoc]
      have hi : H.map i.hom ≫ H.map i.inv = 𝟙 _ := by
        rw [← H.map_comp, i.hom_inv_id, H.map_id]
      rw [← Category.assoc (H.map i.hom), hi, Category.id_comp,
        ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
