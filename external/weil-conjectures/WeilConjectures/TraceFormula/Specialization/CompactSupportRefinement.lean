/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# The compact-support exchange of an open immersion along a proper refinement

Blueprint `prose-E-15` defines `ν_f = χ_p⁻¹ ∘ Rp_{s*}(ν_h)` through a compactification
`f = p ∘ h`, and shows that it does not depend on the compactification: two compactifications
have a common proper refinement `q`, with `h = q ∘ h''`, and the key step is that `ν_h` agrees with
`χ_q⁻¹ ∘ Rq_{s*}(ν_{h''})` under the proper base change identification `h_! ≅ Rq_* h''_!`.

This file proves that key step abstractly
(`CategoryTheory.compactSupportExchange_refinement`), for:

* adjunctions `h_! ⊣ h^*`, `h''_! ⊣ h''^*` and `q^* ⊣ Rq_*` on both fibres;
* the composition isomorphisms `h^* ≅ h''^* q^*`;
* the pullback exchanges `α_h`, `α_{h''}`, `α_q` related by the composition law, with
  `α_h` and `α_{h''}` invertible;
* `ν_h`, `ν_{h''}` the adjoints of `α_h⁻¹`, `α_{h''}⁻¹`, and `χ_q` the mate of `α_q`;
* the base change maps `h''_! ⟶ q^* h_!` (adjoint to the unit of `h_! ⊣ h^*`), assumed invertible
  (proper base change), giving `e : h_! ⟶ Rq_* h''_!`.

Then `ν_h ≫ Ψ(e) ≫ χ_q = e' ≫ Rq_{s*}(ν_{h''})`.

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {A B E A' B' E' : Type*} [Category A] [Category B] [Category E] [Category A']
  [Category B'] [Category E'] {ΨA : A ⥤ A'} {ΨB : B ⥤ B'} {ΨE : E ⥤ E'}
  {Dh : A ⥤ B} {Lh : B ⥤ A} {De : A ⥤ E} {Le : E ⥤ A} {Lq : B ⥤ E} {Rq : E ⥤ B}
  {Dh' : A' ⥤ B'} {Lh' : B' ⥤ A'} {De' : A' ⥤ E'} {Le' : E' ⥤ A'} {Lq' : B' ⥤ E'}
  {Rq' : E' ⥤ B'}

/-- **The compact-support exchange of an open immersion along a proper refinement** (blueprint
`prose-E-15`, independence of the compactification, key step). -/
theorem compactSupportExchange_refinement (adjh : Dh ⊣ Lh) (adje : De ⊣ Le) (adjq : Lq ⊣ Rq)
    (adjh' : Dh' ⊣ Lh') (adje' : De' ⊣ Le') (adjq' : Lq' ⊣ Rq')
    (c : Lh ≅ Lq ⋙ Le) (c' : Lh' ≅ Lq' ⋙ Le')
    (αh : ΨB ⋙ Lh' ≅ Lh ⋙ ΨA) (αe : ΨE ⋙ Le' ≅ Le ⋙ ΨA) (αq : ΨB ⋙ Lq' ⟶ Lq ⋙ ΨE)
    (hα : ∀ Y, αh.hom.app Y = c'.hom.app (ΨB.obj Y) ≫ Le'.map (αq.app Y) ≫
      αe.hom.app (Lq.obj Y) ≫ ΨA.map (c.inv.app Y))
    (bc : ∀ X, De.obj X ⟶ Lq.obj (Dh.obj X))
    (hbc : ∀ X, bc X = (adje.homEquiv _ _).symm (adjh.unit.app X ≫ c.hom.app (Dh.obj X)))
    (bc' : ∀ X, De'.obj X ⟶ Lq'.obj (Dh'.obj X))
    (hbc' : ∀ X, bc' X = (adje'.homEquiv _ _).symm (adjh'.unit.app X ≫ c'.hom.app (Dh'.obj X)))
    [∀ X, IsIso (bc X)] [∀ X, IsIso (bc' X)] (X : A) :
    (adjh'.homEquiv _ _).symm (ΨA.map (adjh.unit.app X) ≫ αh.inv.app (Dh.obj X)) ≫
        ΨB.map (adjq.unit.app (Dh.obj X) ≫ Rq.map (inv (bc X))) ≫
        (mateEquiv adjq adjq' αq).app (De.obj X) =
      (adjq'.unit.app (Dh'.obj (ΨA.obj X)) ≫ Rq'.map (inv (bc' (ΨA.obj X)))) ≫
        Rq'.map ((adje'.homEquiv _ _).symm (ΨA.map (adje.unit.app X) ≫ αe.inv.app (De.obj X))) := by
  set νh := (adjh'.homEquiv _ _).symm (ΨA.map (adjh.unit.app X) ≫ αh.inv.app (Dh.obj X)) with hνh
  set νe := (adje'.homEquiv _ _).symm (ΨA.map (adje.unit.app X) ≫ αe.inv.app (De.obj X)) with hνe
  -- the composition law for `α`, solved for `c' ≫ Le'(α_q)`
  have hα' : αh.inv.app (Dh.obj X) ≫ c'.hom.app (ΨB.obj (Dh.obj X)) ≫ Le'.map (αq.app (Dh.obj X)) =
      ΨA.map (c.hom.app (Dh.obj X)) ≫ αe.inv.app (Lq.obj (Dh.obj X)) := by
    rw [← cancel_epi (αh.hom.app (Dh.obj X)), Iso.hom_inv_id_app_assoc, hα]
    simp [← ΨA.map_comp_assoc]
  -- the key identity, on `h''_! ⊣ h''^*`-adjoints
  have K : bc' (ΨA.obj X) ≫ Lq'.map νh ≫ αq.app (Dh.obj X) = νe ≫ ΨE.map (bc X) := by
    apply (adje'.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right, hνe, hbc']
    simp only [Functor.id_obj, Equiv.apply_symm_apply]
    have h1 := c'.hom.naturality νh
    have h2 := αe.inv.naturality (bc X)
    have h3 := (adje.homEquiv _ _).apply_symm_apply (adjh.unit.app X ≫ c.hom.app (Dh.obj X))
    rw [Adjunction.homEquiv_unit] at h3
    simp only [Functor.comp_map] at h1 h2
    rw [Category.assoc, Le'.map_comp, reassoc_of% h1.symm]
    have h4 := (adjh'.homEquiv _ _).apply_symm_apply
      (ΨA.map (adjh.unit.app X) ≫ αh.inv.app (Dh.obj X))
    rw [Adjunction.homEquiv_unit, ← hνh] at h4
    rw [← hbc] at h3
    rw [reassoc_of% h4, hα', Category.assoc, ← h2, ← ΨA.map_comp_assoc]
    simp only [Functor.id_obj] at h3
    rw [← h3, ΨA.map_comp, Category.assoc]
  apply (adjq'.homEquiv _ _).symm.injective
  have hL : Lq'.map (ΨB.map (adjq.unit.app (Dh.obj X) ≫ Rq.map (inv (bc X)))) ≫
      αq.app (Rq.obj (De.obj X)) ≫ ΨE.map (adjq.counit.app (De.obj X)) =
      αq.app (Dh.obj X) ≫ ΨE.map (inv (bc X)) := by
    have := αq.naturality (adjq.unit.app (Dh.obj X) ≫ Rq.map (inv (bc X)))
    simp only [Functor.comp_map] at this
    have hc := adjq.counit.naturality (inv (bc X))
    simp only [Functor.comp_map, Functor.id_map] at hc
    rw [reassoc_of% this, ← ΨE.map_comp, Lq.map_comp, Category.assoc, hc,
      reassoc_of% (adjq.left_triangle_components (Dh.obj X))]
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Lq'.map_comp, Lq'.map_comp,
    Category.assoc, Category.assoc, mateEquiv_counit, hL]
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality,
    Adjunction.counit_naturality_assoc]
  rw [reassoc_of% (adjq'.left_triangle_components (Dh'.obj (ΨA.obj X))),
    ← cancel_epi (bc' (ΨA.obj X)), IsIso.hom_inv_id_assoc, reassoc_of% K, ← ΨE.map_comp,
    IsIso.hom_inv_id, ΨE.map_id,
    Category.comp_id, hνe]
  rfl

end CategoryTheory
