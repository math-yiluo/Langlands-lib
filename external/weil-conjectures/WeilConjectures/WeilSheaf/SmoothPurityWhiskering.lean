/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EssentialImage

/-! # Descent of natural isomorphisms along full essentially surjective functors -/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory.Functor

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
noncomputable def Functor.fullyFaithfulWhiskeringLeftOfFullEssSurj
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (p : C ⥤ D) [p.Full] [p.EssSurj]
    (E : Type u₃) [Category.{v₃} E] :
    ((whiskeringLeft C D E).obj p).FullyFaithful := by
  classical
  let L := (whiskeringLeft C D E).obj p
  have hfaith : L.Faithful := ⟨by
    intro A B a b h
    ext X
    apply (cancel_epi (A.map (p.objObjPreimageIso X).hom)).1
    rw [a.naturality, b.naturality]
    exact congrArg (fun z ↦ z ≫ B.map (p.objObjPreimageIso X).hom)
      (congrArg (fun z ↦ z.app (p.objPreimage X)) h)⟩
  have hfull : L.Full := ⟨by
    intro A B a
    let b : A ⟶ B :=
      { app X := A.map (p.objObjPreimageIso X).inv ≫
          a.app (p.objPreimage X) ≫ B.map (p.objObjPreimageIso X).hom
        naturality := by
          intro X Y g
          have ha := a.naturality (p.preimage
            ((p.objObjPreimageIso X).hom ≫ g ≫ (p.objObjPreimageIso Y).inv))
          change A.map (p.map _) ≫ _ = _ ≫ B.map (p.map _) at ha
          rw [p.map_preimage] at ha
          simp only [Functor.map_comp] at ha
          apply (cancel_epi (A.map (p.objObjPreimageIso X).hom)).1
          simp only [Category.assoc, ← A.map_comp_assoc, Iso.hom_inv_id, A.map_id,
            Category.id_comp]
          simp only [Functor.map_comp] at *
          rw [← Category.assoc, ha]
          simp only [Category.assoc, ← B.map_comp, Iso.inv_hom_id,
            Category.comp_id] }
    refine ⟨b, ?_⟩
    ext X
    have ha := a.naturality (p.preimage (p.objObjPreimageIso (p.obj X)).hom)
    change A.map (p.map _) ≫ _ = _ ≫ B.map (p.map _) at ha
    rw [p.map_preimage] at ha
    change A.map (p.objObjPreimageIso (p.obj X)).inv ≫
      a.app (p.objPreimage (p.obj X)) ≫ B.map (p.objObjPreimageIso (p.obj X)).hom = a.app X
    rw [← ha, ← A.map_comp_assoc, Iso.inv_hom_id, A.map_id, Category.id_comp]⟩
  exact Functor.FullyFaithful.ofFullyFaithful L

end CategoryTheory
