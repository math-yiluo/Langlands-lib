/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTateCoefficientComposition
public import WeilConjectures.WeilSheaf.SmoothPurityOrdinaryPullIsoComp

/-! # Coefficient extension preserves the pullback cocycle -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  {M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
  {N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
  {P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
  (e : (g)^*⟦Λ⟧.obj M ≅ N) (e' : (f)^*⟦Λ⟧.obj N ≅ P)
  (e'' : (f ≫ g)^*⟦Λ⟧.obj M ≅ P)

/-- The canonical coefficient pullback square carries a composable pair of data
to a composable pair, with the specified geometric compositor. -/
lemma purityCoefficientPullbackIso_geometric_comp
    (h : (upperStarComp Λ f g).hom.app M ≫
      (f)^*⟦Λ⟧.map e.hom ≫ e'.hom = e''.hom) :
    (upperStarComp Λ' f g).hom.app ((Mod.extendScalars (coefficientMap a Z)).obj M) ≫
        (f)^*⟦Λ'⟧.map (purityCoefficientPullbackIso a g e).hom ≫
        (purityCoefficientPullbackIso a f e').hom =
      (purityCoefficientPullbackIso a (f ≫ g) e'').hom := by
  have hn := (pullIso a f).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  apply (cancel_epi ((pullIso a (f ≫ g)).hom.app M)).mp
  simp only [purityCoefficientPullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, purity_pullIso_hom_app_comp]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, ← Functor.map_comp, h]

end AlgebraicGeometry.ProEtale.CondensedRing
