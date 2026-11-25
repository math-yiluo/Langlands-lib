/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates of derived comparisons through units and counits

Let `p ⊣ q` and `p' ⊣ q'` be adjunctions between "homotopy" categories `H_•`, and `P ⊣ Q`,
`P' ⊣ Q'` adjunctions between "derived" categories `D_•`, related by functors `ι : H_• ⥤ D_•`,
by "counits" `c_P : ι ⋙ P ⟶ p ⋙ ι` (of left derived functors) and "units" `u : q ⋙ ι ⟶ ι ⋙ Q`
(of right derived functors) compatible with the units and counits of the adjunctions. Let
`T_X, T_Y` be "derived" versions of functors `E_X, E_Y` through counits `c_X, c_Y`, and let
`α : T_Y ⋙ P' ⟶ P ⋙ T_X` be a "derived" version of `π : E_Y ⋙ p' ⟶ p ⋙ E_X`. We show that the mate
`Q ⋙ T_Y ⟶ T_X ⋙ Q'` of `α` is, through the units and counits, the mate of `π`
(`CategoryTheory.mateEquiv_app_comp_eq_of_fac`).

This is the formal part of the computation, on complexes, of the comparison between derived
pushforwards and derived extensions of scalars, for an arbitrary coefficient change.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {H_X H_Y H'_X H'_Y D_X D_Y D'_X D'_Y : Type*} [Category* H_X] [Category* H_Y]
  [Category* H'_X] [Category* H'_Y] [Category* D_X] [Category* D_Y] [Category* D'_X]
  [Category* D'_Y]
  {ι_X : H_X ⥤ D_X} {ι_Y : H_Y ⥤ D_Y} {ι'_X : H'_X ⥤ D'_X} {ι'_Y : H'_Y ⥤ D'_Y}
  {p : H_Y ⥤ H_X} {q : H_X ⥤ H_Y} {p' : H'_Y ⥤ H'_X} {q' : H'_X ⥤ H'_Y}
  {E_X : H_X ⥤ H'_X} {E_Y : H_Y ⥤ H'_Y}
  {P : D_Y ⥤ D_X} {Q : D_X ⥤ D_Y} {P' : D'_Y ⥤ D'_X} {Q' : D'_X ⥤ D'_Y}
  {T_X : D_X ⥤ D'_X} {T_Y : D_Y ⥤ D'_Y}

/-- The mate along `P ⊣ Q` and `P' ⊣ Q'` of a "derived" comparison `α : T_Y ⋙ P' ⟶ P ⋙ T_X` is,
through the units `u, u'` and counits `c_X, c_Y`, the mate along `p ⊣ q` and `p' ⊣ q'` of an
"underived" comparison `π`, provided the units and counits of the derived adjunctions are
induced by the underived ones (`hη'` and `hε`) and `α` is induced by `π` (`hα`). -/
lemma mateEquiv_app_comp_eq_of_fac (e : p ⊣ q) (e' : p' ⊣ q') (A : P ⊣ Q) (A' : P' ⊣ Q')
    (c_P : ι_Y ⋙ P ⟶ p ⋙ ι_X) (c_P' : ι'_Y ⋙ P' ⟶ p' ⋙ ι'_X)
    (c_X : ι_X ⋙ T_X ⟶ E_X ⋙ ι'_X) (c_Y : ι_Y ⋙ T_Y ⟶ E_Y ⋙ ι'_Y)
    (u : q ⋙ ι_Y ⟶ ι_X ⋙ Q) (u' : q' ⋙ ι'_Y ⟶ ι'_X ⋙ Q')
    (α : TwoSquare T_Y P P' T_X) (π : TwoSquare E_Y p p' E_X)
    (hη' : ∀ N, A'.unit.app (ι'_Y.obj N) ≫ Q'.map (c_P'.app N) =
      ι'_Y.map (e'.unit.app N) ≫ u'.app (p'.obj N))
    (hε : ∀ M, P.map (u.app M) ≫ A.counit.app (ι_X.obj M) =
      c_P.app (q.obj M) ≫ ι_X.map (e.counit.app M))
    (hα : ∀ N, α.app (ι_Y.obj N) ≫ T_X.map (c_P.app N) ≫ c_X.app (p.obj N) =
      P'.map (c_Y.app N) ≫ c_P'.app (E_Y.obj N) ≫ ι'_X.map (π.app N))
    (M : H_X) :
    T_Y.map (u.app M) ≫ (mateEquiv A A' α).app (ι_X.obj M) ≫ Q'.map (c_X.app M) =
      c_Y.app (q.obj M) ≫ ι'_Y.map ((mateEquiv e e' π).app M) ≫ u'.app (E_X.obj M) := by
  have n₁ := A'.unit.naturality (T_Y.map (u.app M))
  have n₂ := α.naturality (u.app M)
  have n₃ := c_X.naturality (e.counit.app M)
  have n₄ := A'.unit.naturality (c_Y.app (q.obj M))
  have n₅ := u'.naturality (π.app (q.obj M) ≫ E_X.map (e.counit.app M))
  have h₂ := hε M
  have h₃ := hα (q.obj M)
  have h₄ := hη' (E_Y.obj (q.obj M))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n₁ n₂ n₃ n₄ n₅
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_map, Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [reassoc_of% n₁]
  simp only [← Q'.map_comp]
  rw [reassoc_of% n₂, ← T_X.map_comp_assoc, h₂, T_X.map_comp_assoc, n₃, reassoc_of% h₃]
  simp only [Q'.map_comp]
  rw [← reassoc_of% n₄, reassoc_of% h₄]
  simp only [← Q'.map_comp, ← ι'_X.map_comp]
  rw [← n₅]
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
