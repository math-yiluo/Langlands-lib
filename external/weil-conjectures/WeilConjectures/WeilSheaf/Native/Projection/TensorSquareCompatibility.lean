/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.SheafSquareTransport
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # Transport a tensor square across an isomorphism of pullback functors -/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

variable {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
  [MonoidalCategory E] [MonoidalCategory H]
  (P : C ⥤ D) (U : D ⥤ H) (V : C ⥤ E) (G G' : E ⥤ H)
  (TC : C × C ⥤ C) (TD : D × D ⥤ D)
  (mu : TC ⋙ P ≅ P.prod P ⋙ TD)
  (nY : TC ⋙ V ≅ V.prod V ⋙ Functor.uncurry.obj (curriedTensor E))
  (nZ : TD ⋙ U ≅ U.prod U ⋙ Functor.uncurry.obj (curriedTensor H))
  (a : V ⋙ G ≅ P ⋙ U) (t : G' ≅ G)
  (d : ∀ A B : E, G.obj (A ⊗ B) ⟶ G.obj A ⊗ G.obj B)
  (d' : (Functor.postcompose₂.obj G').obj (curriedTensor E) ⟶
    (((Functor.whiskeringLeft₂ H).obj G').obj G').obj (curriedTensor H))

/-- Rotation of the square followed by naturality of a change of pullback functor. -/
theorem comparisonCompatible_of_tensorSquare_transport
    (hd : ∀ A B, d A B = t.inv.app (A ⊗ B) ≫ (d'.app A).app B ≫
      (t.hom.app A ⊗ₘ t.hom.app B))
    (h : ∀ M N, PullTensorSquareWithComparison P U V G TC TD mu nY nZ a d M N) :
    ComparisonCompatible (Functor.isoWhiskerLeft V t ≪≫ a)
      (Functor.curryCompIsoOfIso mu).hom d'
      (Functor.curryCompIsoOfIso' nZ) (Functor.curryCompIsoOfIso' nY) := by
  intro M N
  have hh : U.map (mu.hom.app (M, N)) ≫ nZ.hom.app (P.obj M, P.obj N) =
      a.inv.app (TC.obj (M, N)) ≫ G.map (nY.hom.app (M, N)) ≫
      d (V.obj M) (V.obj N) ≫ (a.hom.app M ⊗ₘ a.hom.app N) := by
    apply (cancel_mono (a.inv.app M ⊗ₘ a.inv.app N)).1
    simpa only [PullTensorSquareWithComparison, Category.assoc, tensorHom_comp_tensorHom,
      Iso.hom_inv_id_app,
      MonoidalCategory.id_tensorHom_id, Category.comp_id, Functor.comp_obj] using h M N
  rw [hd] at hh
  have hn := t.inv.naturality (nY.hom.app (M, N))
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
    curriedTensor_obj_obj] at hn
  simp only [Category.assoc] at hh
  rw [reassoc_of% hn] at hh
  simp only [tensorHom_comp_tensorHom] at hh
  change U.map (mu.hom.app (M, N)) ≫ nZ.hom.app (P.obj M, P.obj N) =
    (Functor.isoWhiskerLeft V t ≪≫ a).inv.app (TC.obj (M, N)) ≫
      G'.map (nY.hom.app (M, N)) ≫ (d'.app (V.obj M)).app (V.obj N) ≫
        ((curriedTensor H).map ((Functor.isoWhiskerLeft V t ≪≫ a).hom.app M)).app
          (G'.obj (V.obj N)) ≫
        ((curriedTensor H).obj (U.obj (P.obj M))).map
          ((Functor.isoWhiskerLeft V t ≪≫ a).hom.app N)
  simpa only [
    Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    curriedTensor_map_app, curriedTensor_obj_map, Category.assoc,
    MonoidalCategory.tensorHom_def, Functor.comp_obj] using hh

end CategoryTheory.Adjunction
