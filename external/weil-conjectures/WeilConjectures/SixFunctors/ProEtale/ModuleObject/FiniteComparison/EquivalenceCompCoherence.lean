/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherence

/-!
# Conjugates along equivalences and composition isomorphisms

Let `e_X, e_Y, e_Z` be equivalences of categories, `U_a ⊣ L_a` and `V_a ⊣ M_a` adjunctions
(for `a = f, g, f ≫ g`) on the two sides, and `λ_a : L_a ⋙ e ≅ e ⋙ M_a` isomorphisms of right
adjoints, with conjugate isomorphisms `υ_a : U_a ⋙ e ≅ e ⋙ V_a` of left adjoints (the
construction of `CategoryTheory.Adjunction.leftAdjointCompEquivalenceIso`). If the `λ_a` are
compatible with composition isomorphisms `L_f ⋙ L_g ≅ L_fg` and `M_f ⋙ M_g ≅ M_fg`, then the
`υ_a` are compatible with the conjugate composition isomorphisms `U_fg ≅ U_g ⋙ U_f` and
`V_fg ≅ V_g ⋙ V_f` (`CategoryTheory.Adjunction.compCoherence_of_equivalence_conjugate`).
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {A_X A_Y A_Z B_X B_Y B_Z : Type*} [Category* A_X] [Category* A_Y] [Category* A_Z]
  [Category* B_X] [Category* B_Y] [Category* B_Z]
  (eX : A_X ≌ B_X) (eY : A_Y ≌ B_Y) (eZ : A_Z ≌ B_Z)

/-- The components of `Iso.inverseCompIso (Iso.isoCompInverse λ ≪≫ α)` after applying the
equivalence `e_Y`. -/
lemma functor_map_inverseCompIso_isoCompInverse_hom_app {L : A_X ⥤ A_Y} {M : B_X ⥤ B_Y}
    (lam : L ⋙ eY.functor ≅ eX.functor ⋙ M) (N : B_X) :
    eY.functor.map ((Iso.inverseCompIso (Iso.isoCompInverse lam ≪≫
        Functor.associator _ _ _)).hom.app N) =
      lam.hom.app (eX.inverse.obj N) ≫ M.map (eX.counit.app N) ≫
        eY.counitInv.app (M.obj N) := by
  simp [Equivalence.fun_inv_map]

/-- The components of the inverse of `Iso.inverseCompIso (Iso.isoCompInverse λ ≪≫ α)` after
applying the equivalence `e_Y`. -/
lemma functor_map_inverseCompIso_isoCompInverse_inv_app {L : A_X ⥤ A_Y} {M : B_X ⥤ B_Y}
    (lam : L ⋙ eY.functor ≅ eX.functor ⋙ M) (N : B_X) :
    eY.functor.map ((Iso.inverseCompIso (Iso.isoCompInverse lam ≪≫
        Functor.associator _ _ _)).inv.app N) =
      eY.counit.app (M.obj N) ≫ M.map (eX.counitInv.app N) ≫ lam.inv.app (eX.inverse.obj N) := by
  rw [← cancel_epi (eY.functor.map ((Iso.inverseCompIso (Iso.isoCompInverse lam ≪≫
    Functor.associator _ _ _)).hom.app N)), ← Functor.map_comp, Iso.hom_inv_id_app,
    functor_map_inverseCompIso_isoCompInverse_hom_app]
  simp [← Functor.map_comp_assoc]

/-- Inverting the conjugate of an isomorphism of right adjoints. -/
lemma symm_conjugateIsoEquiv_symm_apply {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (x : R₁ ≅ R₂) :
    ((conjugateIsoEquiv adj₁ adj₂).symm x).symm = (conjugateIsoEquiv adj₂ adj₁).symm x.symm := by
  rw [Equiv.eq_symm_apply, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]

variable {U_f : A_Y ⥤ A_X} {L_f : A_X ⥤ A_Y} (adj_f : U_f ⊣ L_f)
  {U_g : A_Z ⥤ A_Y} {L_g : A_Y ⥤ A_Z} (adj_g : U_g ⊣ L_g)
  {U_fg : A_Z ⥤ A_X} {L_fg : A_X ⥤ A_Z} (adj_fg : U_fg ⊣ L_fg)
  {V_f : B_Y ⥤ B_X} {M_f : B_X ⥤ B_Y} (adj'_f : V_f ⊣ M_f)
  {V_g : B_Z ⥤ B_Y} {M_g : B_Y ⥤ B_Z} (adj'_g : V_g ⊣ M_g)
  {V_fg : B_Z ⥤ B_X} {M_fg : B_X ⥤ B_Z} (adj'_fg : V_fg ⊣ M_fg)

/-- The compatibility of isomorphisms `L_a ⋙ e ≅ e ⋙ M_a` with composition isomorphisms
transfers to the isomorphisms `M_a ⋙ e⁻¹ ≅ e⁻¹ ⋙ L_a` obtained by conjugating with the
equivalences. -/
lemma inverse_map_comp_inverseCompIso_isoCompInverse
    (lam_f : L_f ⋙ eY.functor ≅ eX.functor ⋙ M_f)
    (lam_g : L_g ⋙ eZ.functor ≅ eY.functor ⋙ M_g)
    (lam_fg : L_fg ⋙ eZ.functor ≅ eX.functor ⋙ M_fg)
    (l : L_f ⋙ L_g ≅ L_fg) (l' : M_f ⋙ M_g ≅ M_fg)
    (h : ∀ N : A_X, eZ.functor.map (l.hom.app N) ≫ lam_fg.hom.app N =
      lam_g.hom.app (L_f.obj N) ≫ M_g.map (lam_f.hom.app N) ≫ l'.hom.app (eX.functor.obj N))
    (N : B_X) :
    eZ.inverse.map (l'.hom.app N) ≫
        (Iso.inverseCompIso (Iso.isoCompInverse lam_fg ≪≫ Functor.associator _ _ _)).inv.app N =
      (Iso.inverseCompIso (Iso.isoCompInverse lam_g ≪≫ Functor.associator _ _ _)).inv.app
          (M_f.obj N) ≫
        L_g.map ((Iso.inverseCompIso (Iso.isoCompInverse lam_f ≪≫
          Functor.associator _ _ _)).inv.app N) ≫ l.hom.app (eX.inverse.obj N) := by
  apply eZ.functor.map_injective
  have h' : M_g.map (lam_f.inv.app (eX.inverse.obj N)) ≫
      lam_g.inv.app (L_f.obj (eX.inverse.obj N)) ≫
      eZ.functor.map (l.hom.app (eX.inverse.obj N)) =
      l'.hom.app (eX.functor.obj (eX.inverse.obj N)) ≫ lam_fg.inv.app (eX.inverse.obj N) := by
    rw [← cancel_mono (lam_fg.hom.app _), Category.assoc, Category.assoc, Category.assoc,
      h]
    simp [← Functor.map_comp_assoc]
  have nlam := lam_g.inv.naturality
    ((Iso.inverseCompIso (Iso.isoCompInverse lam_f ≪≫ Functor.associator _ _ _)).inv.app N)
  have nl := l'.hom.naturality (eX.counitInv.app N)
  simp only [Functor.comp_obj, Functor.comp_map] at nlam nl
  simp only [Functor.map_comp, functor_map_inverseCompIso_isoCompInverse_inv_app,
    Equivalence.fun_inv_map, Category.assoc]
  rw [← reassoc_of% nlam, functor_map_inverseCompIso_isoCompInverse_inv_app]
  simp only [Functor.map_comp, Category.assoc, h']
  simp [← reassoc_of% nl]

/-- **Conjugates along equivalences and composition isomorphisms.** Let
`υ_a : U_a ⋙ e ≅ e ⋙ V_a` be the conjugates (as in
`CategoryTheory.Adjunction.leftAdjointCompEquivalenceIso`) of isomorphisms
`λ_a : L_a ⋙ e ≅ e ⋙ M_a` of right adjoints, and `c`, `c'` the conjugates of composition
isomorphisms `L_f ⋙ L_g ≅ L_fg`, `M_f ⋙ M_g ≅ M_fg`. If the `λ_a` are compatible with the
latter, then the `υ_a` are compatible with `c` and `c'`. -/
lemma compCoherence_of_equivalence_conjugate
    (lam_f : L_f ⋙ eY.functor ≅ eX.functor ⋙ M_f)
    (lam_g : L_g ⋙ eZ.functor ≅ eY.functor ⋙ M_g)
    (lam_fg : L_fg ⋙ eZ.functor ≅ eX.functor ⋙ M_fg)
    (l : L_f ⋙ L_g ≅ L_fg) (l' : M_f ⋙ M_g ≅ M_fg)
    (h : ∀ N : A_X, eZ.functor.map (l.hom.app N) ≫ lam_fg.hom.app N =
      lam_g.hom.app (L_f.obj N) ≫ M_g.map (lam_f.hom.app N) ≫ l'.hom.app (eX.functor.obj N))
    (c : U_fg ≅ U_g ⋙ U_f) (c' : V_fg ≅ V_g ⋙ V_f)
    (hc : c = ((conjugateIsoEquiv adj_fg (adj_g.comp adj_f)).symm l.symm).symm)
    (hc' : c' = ((conjugateIsoEquiv adj'_fg (adj'_g.comp adj'_f)).symm l'.symm).symm)
    (υ_f : U_f ⋙ eX.functor ≅ eY.functor ⋙ V_f) (υ_g : U_g ⋙ eY.functor ≅ eZ.functor ⋙ V_g)
    (υ_fg : U_fg ⋙ eX.functor ≅ eZ.functor ⋙ V_fg)
    (hυ_f : υ_f = ((conjugateIsoEquiv (adj_f.comp eX.toAdjunction)
      (eY.toAdjunction.comp adj'_f)).symm (Iso.inverseCompIso (Iso.isoCompInverse lam_f ≪≫
        Functor.associator _ _ _))).symm)
    (hυ_g : υ_g = ((conjugateIsoEquiv (adj_g.comp eY.toAdjunction)
      (eZ.toAdjunction.comp adj'_g)).symm (Iso.inverseCompIso (Iso.isoCompInverse lam_g ≪≫
        Functor.associator _ _ _))).symm)
    (hυ_fg : υ_fg = ((conjugateIsoEquiv (adj_fg.comp eX.toAdjunction)
      (eZ.toAdjunction.comp adj'_fg)).symm (Iso.inverseCompIso (Iso.isoCompInverse lam_fg ≪≫
        Functor.associator _ _ _))).symm) :
    CompCoherence c c' υ_g υ_f υ_fg := by
  subst hc hc' hυ_f hυ_g hυ_fg
  rw [symm_conjugateIsoEquiv_symm_apply, symm_conjugateIsoEquiv_symm_apply,
    symm_conjugateIsoEquiv_symm_apply, symm_conjugateIsoEquiv_symm_apply,
    symm_conjugateIsoEquiv_symm_apply]
  intro M
  refine pullIsoOfComapIso_hom_app_comp eX.toAdjunction eY.toAdjunction eZ.toAdjunction adj_f
    adj_g adj_fg adj'_f adj'_g adj'_fg _ _ _ _ _ (fun N ↦ ?_) M
  rw [Iso.symm_symm_eq, Iso.symm_symm_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact inverse_map_comp_inverseCompIso_isoCompInverse eX eY eZ lam_f lam_g lam_fg l l' h N

end CategoryTheory.Adjunction
