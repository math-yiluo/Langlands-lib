/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatible
public import WeilConjectures.CategoryTheory.WeilEquivariance

/-! # Reduction of the compact-support Weil datum

The comparison is stated over abstract categories. Its geometric input is precisely
the compatibility of reduction with compact-support exchange, in trace form.
-/

@[expose] public section

namespace CategoryTheory

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  {L : C ⥤ D} {L' : C' ⥤ D'} {G : C ⥤ C} {H : D ⥤ D}
  {G' : C' ⥤ C'} {H' : D' ⥤ D'}
  (T : C ⥤ C') (U : D ⥤ D')
  (a : G ⋙ T ≅ T ⋙ G') (b : H ⋙ U ≅ U ⋙ H')
  (γ : L ⋙ U ≅ T ⋙ L') (e : L ⋙ H ≅ G ⋙ L) (e' : L' ⋙ H' ≅ G' ⋙ L')

/-- A reduction comparison compatible with compact-support exchange is equivariant
for the transported compact-support data. -/
lemma purity_isWeilEquivariant_shriekReduction
    (h : NatTrans.SquareCompatible (Functor.pasteSquareIso γ b)
      (Functor.pasteSquareIso a γ) e.hom e'.hom)
    {M : C} (φ : G.obj M ⟶ M) :
    IsWeilEquivariant H'
      (transportWeilDatum U b (Adjunction.leftWeilDatum e φ))
      (Adjunction.leftWeilDatum e' (transportWeilDatum T a φ)) (γ.hom.app M) := by
  have hc := h M
  simp only [Functor.pasteSquareIso_hom_app, Category.assoc] at hc
  have hn := γ.hom.naturality φ
  dsimp only [Functor.comp_map] at hn
  unfold IsWeilEquivariant transportWeilDatum Adjunction.leftWeilDatum
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi (b.hom.app (L.obj M))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hc, ← L'.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj] at hn ⊢
  simp only [Functor.map_id, Category.id_comp]
  rw [← hn]

/-- An equivariant trace remains equivariant after coefficient reduction and the
compact-support comparison. -/
lemma purity_isWeilEquivariant_reducedTrace
    (h : NatTrans.SquareCompatible (Functor.pasteSquareIso γ b)
      (Functor.pasteSquareIso a γ) e.hom e'.hom)
    {M : C} {N : D} (φ : G.obj M ⟶ M) (ψ : H.obj N ⟶ N)
    (t : L.obj M ⟶ N) (ht : IsWeilEquivariant H (Adjunction.leftWeilDatum e φ) ψ t) :
    IsWeilEquivariant H' (Adjunction.leftWeilDatum e' (transportWeilDatum T a φ))
      (transportWeilDatum U b ψ) (γ.inv.app M ≫ U.map t) := by
  have hγ := purity_isWeilEquivariant_shriekReduction T U a b γ e e' h φ
  have hγinv : IsWeilEquivariant H'
      (Adjunction.leftWeilDatum e' (transportWeilDatum T a φ))
      (transportWeilDatum U b (Adjunction.leftWeilDatum e φ)) (γ.inv.app M) := by
    unfold IsWeilEquivariant at hγ ⊢
    apply (cancel_mono (γ.hom.app M)).1
    simpa only [Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp, Category.comp_id] using
      congrArg (fun z ↦ H'.map (γ.inv.app M) ≫ z) hγ.symm
  exact hγinv.comp (ht.map U b)

end CategoryTheory
