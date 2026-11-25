/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.Functor.CurryComparison

/-! # Checking a tensor comparison square on representatives

Naturality extends a square of tensor comparisons from representatives to all objects.
This applies to the native K-flat representatives without identifying a derived category
of Weil sheaves with a category of pairs in an ordinary derived category.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

/-- A square of tensor comparisons can be checked on a family of representatives that
contains every object up to isomorphism. -/
theorem tensorSquare_of_representatives
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {I : Type*} (Q : I → C) (flat : I → Prop)
    (hQ : ∀ X : C, ∃ P, flat P ∧ Nonempty (Q P ≅ X))
    (P : C ⥤ D) (U : D ⥤ H) (V : C ⥤ E) (L : E ⥤ H)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (TE : E × E ⥤ E) (TH : H × H ⥤ H)
    (mu : TC ⋙ P ≅ P.prod P ⋙ TD)
    (tZ : TD ⋙ U ≅ U.prod U ⋙ TH)
    (tY : TC ⋙ V ≅ V.prod V ⋙ TE)
    (pull : P ⋙ U ≅ V ⋙ L)
    (c : TE ⋙ L ≅ L.prod L ⋙ TH)
    (h : ∀ M N, flat M → flat N →
      U.map (mu.hom.app (Q M, Q N)) ≫
        tZ.hom.app (P.obj (Q M), P.obj (Q N)) ≫
        TH.map (Prod.mkHom (pull.hom.app (Q M)) (pull.hom.app (Q N))) =
      pull.hom.app (TC.obj (Q M, Q N)) ≫
        L.map (tY.hom.app (Q M, Q N)) ≫
        c.hom.app (V.obj (Q M), V.obj (Q N))) :
    ∀ M N,
      U.map (mu.hom.app (M, N)) ≫ tZ.hom.app (P.obj M, P.obj N) ≫
        TH.map (Prod.mkHom (pull.hom.app M) (pull.hom.app N)) =
      pull.hom.app (TC.obj (M, N)) ≫ L.map (tY.hom.app (M, N)) ≫
        c.hom.app (V.obj M, V.obj N) := by
  let α : TC ⋙ P ⋙ U ⟶ V.prod V ⋙ L.prod L ⋙ TH :=
    Functor.whiskerRight mu.hom U ≫ Functor.whiskerLeft (P.prod P) tZ.hom ≫
      Functor.whiskerRight (NatTrans.prod pull.hom pull.hom) TH
  let β : TC ⋙ P ⋙ U ⟶ V.prod V ⋙ L.prod L ⋙ TH :=
    Functor.whiskerLeft TC pull.hom ≫ Functor.whiskerRight tY.hom L ≫
      Functor.whiskerLeft (V.prod V) c.hom
  have hab : α = β := by
    apply NatTrans.ext
    funext X
    obtain ⟨M, hM, ⟨e⟩⟩ := hQ X.1
    obtain ⟨N, hN, ⟨f⟩⟩ := hQ X.2
    let g : (Q M, Q N) ≅ X := e.prod f
    apply (cancel_epi ((TC ⋙ P ⋙ U).map g.hom)).1
    rw [α.naturality, β.naturality]
    change (U.map (mu.hom.app (Q M, Q N)) ≫
        tZ.hom.app (P.obj (Q M), P.obj (Q N)) ≫
        TH.map (Prod.mkHom (pull.hom.app (Q M)) (pull.hom.app (Q N)))) ≫ _ =
      (pull.hom.app (TC.obj (Q M, Q N)) ≫ L.map (tY.hom.app (Q M, Q N)) ≫
        c.hom.app (V.obj (Q M), V.obj (Q N))) ≫ _
    rw [h M N hM hN]
  intro M N
  exact congrArg (fun t ↦ t.app (M, N)) hab

end CategoryTheory.Adjunction
