/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Adjunct transport through a conjugate and an open factor

Source: Stacks Project, Tag 07A7, abstract mate normalization
(blueprint: lem-sf-adjunct-conjugate-open-factor).

The existing categorical argument is extracted from
`WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting`
so it is a public interface
independent of the geometric realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

private theorem mate_app_homEquiv
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) {G : A ⥤ D} {H : B ⥤ E}
    (t : TwoSquare G L₁ L₂ H) (M : B) :
    (mateEquiv a b t).app M = b.homEquiv (G.obj (R₁.obj M)) (H.obj M)
      (t.app (R₁.obj M) ≫ H.map (a.counit.app M)) := by
  apply (b.homEquiv (G.obj (R₁.obj M)) (H.obj M)).symm.injective
  rw [Equiv.symm_apply_apply]
  exact mateEquiv_counit a b t M

private theorem homEquiv_conjugate_transport
    {A B : Type*} [Category A] [Category B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂)
    {X : A} {Y : B} (f : L₁.obj X ⟶ Y) :
    a.homEquiv X Y f ≫ (conjugateIsoEquiv a b e.symm).hom.app Y =
      b.homEquiv X Y (e.inv.app X ≫ f) := by
  rw [a.homEquiv_unit, b.homEquiv_unit]
  have hn := (conjugateIsoEquiv a b e.symm).hom.naturality f
  rw [Category.assoc, hn, ← Category.assoc]
  rw [conjugateIsoEquiv_apply_hom, unit_conjugateEquiv]
  rw [Category.assoc, ← R₂.map_comp]
  rfl

private theorem homEquiv_open_factor
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {J₀ : B ⥤ D} {P₀ : D ⥤ B}
    (a : L ⊣ R) (b : J₀ ⊣ P₀) [IsIso b.unit]
    (F : E ⥤ B) (G : E ⥤ D) (d : F ⋙ J₀ ≅ G)
    {X : A} {M : E} (f : L.obj X ⟶ F.obj M) :
    (a.comp b).homEquiv X (G.obj M) (J₀.map f ≫ d.hom.app M) ≫
        R.map (P₀.map (d.inv.app M) ≫ inv (b.unit.app (F.obj M))) =
      a.homEquiv X (F.obj M) f := by
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ _) ≫ _ = _
  rw [← a.homEquiv_naturality_right]
  congr 1
  rw [b.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% b.unit_naturality f]
  simp only [← P₀.map_comp_assoc, Iso.hom_inv_id_app]
  erw [P₀.map_id, Category.id_comp, IsIso.hom_inv_id, Category.comp_id]

/-- Transport an adjunct through a conjugate isomorphism and cancel an open factor.
Source: Stacks Project, Tag 07A7, abstract mate normalization
(blueprint: lem-sf-adjunct-conjugate-open-factor). -/
theorem adjunct_transport
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Lr : D ⥤ A} {Rr : A ⥤ D} {Lp : E ⥤ B} {Rp : B ⥤ E}
    {Ji : D ⥤ E} {Pi : E ⥤ D} {Jb : F ⥤ B} {Pb : B ⥤ F}
    {Lq : D ⥤ F} {Rq : F ⥤ D} {Js : A ⥤ F} {Jk : A ⥤ B}
    (ar : Lr ⊣ Rr) (ap : Lp ⊣ Rp) (ai : Ji ⊣ Pi)
    (ab : Jb ⊣ Pb) (aq : Lq ⊣ Rq) [IsIso ab.unit]
    (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk)
    (α : Ji ⋙ Lp ⟶ Lr ⋙ Jk) (M : A)
    (f : Lq.obj (Rr.obj M) ⟶ Js.obj M)
    (hα : β.inv.app (Rr.obj M) ≫ α.app (Rr.obj M) ≫
      Jk.map (ar.counit.app M) = Jb.map f ≫ d.hom.app M) :
    ai.homEquiv _ _ ((mateEquiv ar ap α).app M) ≫
      (conjugateIsoEquiv (ai.comp ap) (aq.comp ab) β.symm).hom.app (Jk.obj M) ≫
      Rq.map (Pb.map (d.inv.app M) ≫ inv (ab.unit.app (Js.obj M))) =
        aq.homEquiv _ _ f := by
  have hδ := homEquiv_conjugate_transport (ai.comp ap) (aq.comp ab) β
    (α.app (Rr.obj M) ≫ Jk.map (ar.counit.app M))
  rw [hα] at hδ
  have hδ' : ai.homEquiv _ _ ((mateEquiv ar ap α).app M) ≫
      (conjugateIsoEquiv (ai.comp ap) (aq.comp ab) β.symm).hom.app (Jk.obj M) =
      (aq.comp ab).homEquiv _ _ (Jb.map f ≫ d.hom.app M) := by
    rw [mate_app_homEquiv ar ap]
    simpa only [Adjunction.comp_homEquiv, Equiv.trans_apply, Functor.id_obj,
      Functor.comp_obj] using hδ
  rw [← Category.assoc, hδ']
  exact homEquiv_open_factor aq ab Js Jk d f
