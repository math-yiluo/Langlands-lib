/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.SheafSquareTransport

/-! # Component form of the total tensor square -/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

/-- The tensor square in terms of chosen total models, over abstract categories. -/
def ProjectionTotalModelSquare
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (L : C ⥤ D) (V : D ⥤ B) (F : C ⥤ A) (R : A ⥤ B)
    (e : L ⋙ V ≅ F ⋙ R) (P T WZ : C) (WU : D)
    (tr : L.obj WZ ≅ WU)
    (cZ : F.obj WZ ≅ F.obj P ⊗ F.obj T)
    (cU : V.obj WU ≅ V.obj (L.obj P) ⊗ V.obj (L.obj T))
    (ord : R.obj (F.obj P ⊗ F.obj T) ≅ R.obj (F.obj P) ⊗ R.obj (F.obj T)) : Prop :=
  V.map tr.hom ≫ cU.hom ≫ (e.hom.app P ⊗ₘ e.hom.app T) =
    e.hom.app WZ ≫ R.map cZ.hom ≫ ord.hom

/-- Express a tensor square using the isomorphisms of its individual models. -/
lemma projection_model_square_from_tensor_square
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (L : C ⥤ D) (V : D ⥤ B) (F : C ⥤ A) (R : A ⥤ B)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (t : TC ⋙ L ≅ L.prod L ⋙ TD)
    (nY : TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj (curriedTensor A))
    (nZ : TD ⋙ V ≅ V.prod V ⋙ Functor.uncurry.obj (curriedTensor B))
    (e : L ⋙ V ≅ F ⋙ R)
    (d : ∀ X Y : A, R.obj (X ⊗ Y) ≅ R.obj X ⊗ R.obj Y)
    (P T : C)
    (h : PullTensorSquareWithComparison L V F R TC TD t nY nZ e.symm
      (fun X Y ↦ (d X Y).hom) P T) :
    ProjectionTotalModelSquare L V F R e P T (TC.obj (P, T))
      (TD.obj (L.obj P, L.obj T)) (t.app (P, T)) (nY.app (P, T))
      (nZ.app (L.obj P, L.obj T)) (d (F.obj P) (F.obj T)) := h

end CategoryTheory
