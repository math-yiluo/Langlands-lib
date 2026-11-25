/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedProperUniversality

/-! # Transfer of trace universality through fully faithful inclusions -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

/-- Universality in full subcategories implies universality on the ambient hom
sets, through the specified comparison of the direct-image functors. -/
lemma traceUniversalAt_of_fullyFaithful
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (I : C ⥤ C') (J : D ⥤ D') [I.Full] [I.Faithful] [J.Full] [J.Faithful]
    {L : C ⥤ D} {R : C' ⥤ D'} (c : L ⋙ J ≅ I ⋙ R)
    {P : C} {N : D} (ε : L.obj P ⟶ N) (K : C)
    (h : L.TraceUniversalAt K ε) :
    R.TraceUniversalAt (I.obj K) (c.inv.app P ≫ J.map ε) := by
  have he (φ : K ⟶ P) : R.map (I.map φ) ≫ c.inv.app P ≫ J.map ε =
      c.inv.app K ≫ J.map (L.map φ ≫ ε) := by
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      congrArg (fun ψ ↦ ψ ≫ J.map ε) (c.inv.naturality φ)
  constructor
  · intro φ ψ heq
    obtain ⟨φ, rfl⟩ := I.map_surjective φ
    obtain ⟨ψ, rfl⟩ := I.map_surjective ψ
    dsimp only at heq
    rw [he, he] at heq
    exact congrArg I.map (h.1 (J.map_injective ((cancel_epi _).1 heq)))
  · intro ψ
    obtain ⟨ψ, hψ⟩ := J.map_surjective (c.hom.app K ≫ ψ)
    obtain ⟨φ, hφ⟩ := h.2 ψ
    refine ⟨I.map φ, ?_⟩
    dsimp only at hφ ⊢
    rw [he, hφ, hψ, Iso.inv_hom_id_app_assoc]

/-- Replacing a direct-image functor by an isomorphic one preserves trace
universality with its comparison component prepended to the trace. -/
lemma traceUniversalAt_of_iso
    {C D : Type*} [Category C] [Category D] {L R : C ⥤ D} (e : L ≅ R)
    {P K : C} {N : D} (ε : R.obj P ⟶ N) (h : R.TraceUniversalAt K ε) :
    L.TraceUniversalAt K (e.hom.app P ≫ ε) := by
  have he (φ : K ⟶ P) : L.map φ ≫ e.hom.app P ≫ ε = e.hom.app K ≫ R.map φ ≫ ε := by
    rw [e.hom.naturality_assoc]
  constructor
  · intro φ ψ heq
    simp only [he] at heq
    exact h.1 ((cancel_epi _).1 heq)
  · intro ψ
    obtain ⟨φ, hφ⟩ := h.2 (e.inv.app K ≫ ψ)
    refine ⟨φ, ?_⟩
    dsimp only at hφ ⊢
    rw [he, hφ, Iso.hom_inv_id_app_assoc]

/-- Remove specified source and target coordinates from a universal trace. -/
lemma traceUniversalAt_of_coordinates
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {P P' K : C} {N N' : D} (eP : P ≅ P') (eN : N ≅ N')
    (ε : L.obj P' ⟶ N')
    (h : L.TraceUniversalAt K (L.map eP.hom ≫ ε ≫ eN.inv)) :
    L.TraceUniversalAt K ε := by
  have ht := bijective_map_comp_iso_trace L eP.symm eN _ h
  simpa only [TraceUniversalAt, Iso.symm_hom, Category.assoc,
    ← L.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_assoc, Category.comp_id] using ht

end CategoryTheory.Functor
