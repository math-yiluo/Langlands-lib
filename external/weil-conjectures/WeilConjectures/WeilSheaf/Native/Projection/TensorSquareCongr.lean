/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.SheafSquareTransport

/-! # Transport of tensor squares along equality of comparison isomorphisms -/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
  [MonoidalCategory E] [MonoidalCategory H]
  {P : C ⥤ D} {U : D ⥤ H} {V : C ⥤ E} {G : E ⥤ H}
  {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {mu : TC ⋙ P ≅ P.prod P ⋙ TD}
  {nY : TC ⋙ V ≅ V.prod V ⋙ Functor.uncurry.obj (curriedTensor E)}
  {nZ : TD ⋙ U ≅ U.prod U ⋙ Functor.uncurry.obj (curriedTensor H)}
  {a : V ⋙ G ≅ P ⋙ U} {b : P ⋙ U ≅ V ⋙ G}
  {d : ∀ A B : E, G.obj (A ⊗ B) ⟶ G.obj A ⊗ G.obj B} {M N : C}

/-- Replace an inverse square by the inverse of the chosen forward square. -/
lemma PullTensorSquareWithComparison.of_symm_eq (hba : b = a.symm)
    (h : PullTensorSquareWithComparison P U V G TC TD mu nY nZ b.symm d M N) :
    PullTensorSquareWithComparison P U V G TC TD mu nY nZ a d M N := by
  subst b
  simpa only [Iso.symm_symm_eq] using h

end CategoryTheory
